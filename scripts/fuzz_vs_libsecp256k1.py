#!/usr/bin/env python3
"""Differential fuzzing of the Lean implementation against libsecp256k1.

Generates random and mutated inputs, runs them through the Lean driver
(`lake exe fuzz`, see Tests/FuzzDriver.lean) and through libsecp256k1 (via
`coincurve`), and reports every disagreement.

Covered: public key derivation, RFC 6979 signing (with and without additional
data), verification of valid and mutated DER signatures, public key recovery,
and SEC 1 public key parsing. Values are biased towards edge cases (0, 1,
n - 1, n, p - 1, p, 2^256 - 1, small values, ...).

Usage:
    pip install coincurve
    lake build fuzz
    python3 scripts/fuzz_vs_libsecp256k1.py [--count N] [--seed S]

Known, intentional difference: libsecp256k1 accepts "hybrid" public keys
(prefix 0x06 / 0x07), which this library rejects. Such inputs are not
generated.
"""

import argparse
import os
import random
import subprocess
import sys

import coincurve
from coincurve._libsecp256k1 import ffi, lib

P = 2**256 - 2**32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DRIVER = os.path.join(ROOT, ".lake", "build", "bin", "fuzz")

EDGE_INTS = [0, 1, 2, 3, 7, N - 1, N, N + 1, N - 2, N // 2, N // 2 + 1, P - 1, P, P + 1,
             2**256 - 1, 2**255, 2**128, 2**32 - 1, 2**32, P - N, N - P + 2**256]


def b32(x: int) -> bytes:
    return (x % 2**256).to_bytes(32, "big")


def h(b: bytes) -> str:
    return b.hex() if b else "-"


class Gen:
    def __init__(self, rng: random.Random):
        self.r = rng

    def int256(self) -> int:
        c = self.r.random()
        if c < 0.25:
            return self.r.choice(EDGE_INTS)
        if c < 0.35:
            return self.r.getrandbits(self.r.randrange(1, 256))  # leading zeros
        return self.r.getrandbits(256)

    def scalar(self) -> int:
        while True:
            x = self.int256()
            if 0 < x < N:
                return x

    def bytes32(self) -> bytes:
        return b32(self.int256())


def der_int(x: int) -> bytes:
    body = x.to_bytes((x.bit_length() + 7) // 8, "big") if x else b""
    if not body or body[0] & 0x80:
        body = b"\x00" + body
    return bytes([0x02, len(body)]) + body


def der(r: int, s: int) -> bytes:
    body = der_int(r) + der_int(s)
    return bytes([0x30, len(body)]) + body


def compact_to_rs(c: bytes):
    return int.from_bytes(c[:32], "big"), int.from_bytes(c[32:64], "big")


def lib_pub(d: bytes):
    try:
        return coincurve.PrivateKey(d).public_key.format(compressed=True).hex()
    except Exception:
        return "ERR"


def lib_sign(d: bytes, msg: bytes, extra: bytes):
    try:
        sk = coincurve.PrivateKey(d)
    except Exception:
        return "ERR"
    if extra:
        nonce = (lib.secp256k1_nonce_function_rfc6979, ffi.new("unsigned char[32]", extra))
        sig = sk.sign_recoverable(msg, hasher=None, custom_nonce=nonce)
    else:
        sig = sk.sign_recoverable(msg, hasher=None)
    return f"{sig[:64].hex()} {sig[64]}"


def lib_verify(pub: bytes, msg: bytes, sig: bytes):
    try:
        return "1" if coincurve.PublicKey(pub).verify(sig, msg, hasher=None) else "0"
    except Exception:
        return "0"


def lib_recover(msg: bytes, sig64: bytes, recid: int):
    try:
        pk = coincurve.PublicKey.from_signature_and_message(sig64 + bytes([recid]), msg, hasher=None)
        return pk.format(compressed=True).hex()
    except Exception:
        return "ERR"


def lib_parsepub(data: bytes):
    try:
        return coincurve.PublicKey(data).format(compressed=True).hex()
    except Exception:
        return "ERR"


def mutate_der(g: Gen, sig: bytes, r: int, s: int) -> bytes:
    rr = g.r
    kind = rr.randrange(9)
    b = bytearray(sig)
    if kind == 0:
        return sig  # unchanged
    if kind == 1:  # flip one bit
        i = rr.randrange(len(b))
        b[i] ^= 1 << rr.randrange(8)
        return bytes(b)
    if kind == 2:  # high-S twin
        return der(r, N - s)
    if kind == 3:  # replace r or s with an edge or random value
        v = g.int256()
        return der(v, s) if rr.random() < 0.5 else der(r, v)
    if kind == 4:  # truncate or extend
        return bytes(b[:rr.randrange(len(b))]) if rr.random() < 0.5 else bytes(b) + bytes([rr.randrange(256)])
    if kind == 5:  # tamper with a length or tag byte
        i = rr.choice([0, 1, 2, 3, 4 + b[3], 5 + b[3]])
        if i < len(b):
            b[i] = (b[i] + rr.choice([-1, 1, 0x80])) % 256
        return bytes(b)
    if kind == 6:  # non-minimal integer: prepend a zero byte to r or s
        rb = der_int(r)[2:]
        sb = der_int(s)[2:]
        if rr.random() < 0.5:
            rb = b"\x00" + rb
        else:
            sb = b"\x00" + sb
        body = bytes([2, len(rb)]) + rb + bytes([2, len(sb)]) + sb
        return bytes([0x30, len(body)]) + body
    if kind == 7:  # r + n, s + n (out of range but same residue)
        return der(r + N, s) if rr.random() < 0.5 else der(r, s + N)
    return bytes(rr.randrange(256) for _ in range(rr.randrange(0, 80)))  # garbage


def random_pub_bytes(g: Gen) -> bytes:
    rr = g.r
    kind = rr.randrange(6)
    if kind == 0:  # valid point, compressed or uncompressed
        pk = coincurve.PrivateKey(b32(g.scalar())).public_key
        return pk.format(compressed=rr.random() < 0.5)
    if kind == 1:  # random x, compressed (about half are on the curve)
        return bytes([rr.choice([2, 3])]) + g.bytes32()
    if kind == 2:  # random x and y, uncompressed (almost never on the curve)
        return b"\x04" + g.bytes32() + g.bytes32()
    if kind == 3:  # valid uncompressed point with one coordinate perturbed
        b = bytearray(coincurve.PrivateKey(b32(g.scalar())).public_key.format(compressed=False))
        i = rr.randrange(1, 65)
        b[i] ^= 1 << rr.randrange(8)
        return bytes(b)
    if kind == 4:  # coordinates p, p + small, as compressed / uncompressed
        x = rr.choice([P, P + 1, P + 2, 2**256 - 1, P - 1, 0])
        return bytes([rr.choice([2, 3])]) + b32(x) if rr.random() < 0.5 else b"\x04" + b32(x) + g.bytes32()
    # wrong lengths and prefixes (excluding hybrid 0x06 / 0x07, see the module docstring)
    n = rr.choice([0, 1, 32, 34, 64, 66, 33, 65])
    b = bytes(rr.randrange(256) for _ in range(n))
    if b and b[0] in (6, 7):
        b = b"\x05" + b[1:]
    return b


def make_cases(g: Gen, count: int):
    rr = g.r
    cases = []
    for _ in range(count):
        kind = rr.choice(["pub", "sign", "sign", "verify", "verify", "verify", "recover", "parsepub"])
        if kind == "pub":
            d = g.bytes32()
            cases.append((f"pub {h(d)}", lib_pub(d)))
        elif kind == "sign":
            d, msg = b32(g.scalar()), g.bytes32()
            extra = g.bytes32() if rr.random() < 0.3 else b""
            cases.append((f"sign {h(d)} {h(msg)} {h(extra)}", lib_sign(d, msg, extra)))
        elif kind == "verify":
            sk = coincurve.PrivateKey(b32(g.scalar()))
            msg = g.bytes32()
            sig = sk.sign(msg, hasher=None)
            r, s = compact_to_rs(sk.sign_recoverable(msg, hasher=None)[:64])
            sig = mutate_der(g, sig, r, s)
            pub = sk.public_key.format(compressed=rr.random() < 0.5)
            c = rr.random()
            if c < 0.1:
                msg = bytes([msg[0] ^ 1]) + msg[1:]
            elif c < 0.15:
                pub = coincurve.PrivateKey(b32(g.scalar())).public_key.format()
            cases.append((f"verify {h(pub)} {h(msg)} {h(sig)}", lib_verify(pub, msg, sig)))
        elif kind == "recover":
            sk = coincurve.PrivateKey(b32(g.scalar()))
            msg = g.bytes32()
            rec = sk.sign_recoverable(msg, hasher=None)
            sig64, recid = rec[:64], rec[64]
            c = rr.random()
            if c < 0.3:
                recid = rr.randrange(4)
            elif c < 0.5:
                r, s = compact_to_rs(sig64)
                v = g.int256() % 2**256
                sig64 = b32(v) + b32(s) if rr.random() < 0.5 else b32(r) + b32(v)
            elif c < 0.6:
                msg = g.bytes32()
            cases.append((f"recover {h(msg)} {h(sig64)} {recid}", lib_recover(msg, sig64, recid)))
        else:
            data = random_pub_bytes(g)
            cases.append((f"parsepub {h(data)}", lib_parsepub(data)))
    return cases


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=20000)
    ap.add_argument("--seed", type=int, default=None)
    args = ap.parse_args()
    seed = args.seed if args.seed is not None else random.SystemRandom().getrandbits(32)
    print(f"seed {seed}, {args.count} cases")
    g = Gen(random.Random(seed))
    cases = make_cases(g, args.count)
    inp = "".join(cmd + "\n" for cmd, _ in cases)
    res = subprocess.run([DRIVER], input=inp, capture_output=True, text=True, check=True)
    got = res.stdout.splitlines()
    if len(got) != len(cases):
        print(f"driver returned {len(got)} lines for {len(cases)} commands")
        return 1
    stats, failures = {}, []
    for (cmd, want), have in zip(cases, got):
        kind = cmd.split(" ", 1)[0]
        ok, total, accepted = stats.get(kind, (0, 0, 0))
        stats[kind] = (ok + (want == have), total + 1, accepted + (want not in ("ERR", "0")))
        if want != have:
            failures.append((cmd, want, have))
    for kind, (ok, total, accepted) in sorted(stats.items()):
        print(f"  {kind:9} {ok}/{total} agree ({accepted} accepted / {total - accepted} rejected)")
    for cmd, want, have in failures[:20]:
        print(f"MISMATCH: {cmd}\n  libsecp256k1: {want}\n  lean:         {have}")
    print("PASS" if not failures else f"FAIL: {len(failures)} mismatches")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
