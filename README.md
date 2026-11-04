# lean-ecdsa

ECDSA over secp256k1 in Lean 4, with no dependencies beyond Lean core.

It includes:

- **Constant-time arithmetic for secrets.** Key derivation and signing use fixed-width limbs with Montgomery multiplication, complete point formulas, and a fixed-window scalar multiplication with masked table lookups (see [Side-channel hardening](#side-channel-hardening)).
- **Reference arithmetic.** Field and scalar arithmetic over `Fin p` / `Fin n`, Jacobian coordinates and Shamir's trick. Used for verification and recovery (public data only), and as the specification the constant-time code is tested against.
- **SHA-256 and HMAC-SHA-256**, both implemented from scratch.
- **ECDSA** per SEC 1 v2 §4.1:
  - deterministic nonces (RFC 6979), with optional additional data
  - low-S normalisation (BIP 62/146), on by default
  - public key recovery (recovery id 0–3)
- **Encodings:**
  - SEC 1 public keys, compressed and uncompressed
  - 64-byte compact signatures
  - strict DER signatures (BIP 66)

With the default options, signatures match libsecp256k1's `secp256k1_ecdsa_sign` byte for byte.

> [!WARNING]
> Side-channel hardening is in progress and the library is **not yet suitable for keys with real value**. Secret-dependent arithmetic is now constant-time at the Lean and generated-C level, but secrets are not wiped from memory, `PrivateKey.generate` relies on `IO.getRandomBytes` (which Lean does not guarantee to be cryptographically secure), the machine code has not been checked, the limb arithmetic is tested but not yet proved, and nothing has been audited. See [what remains](#what-remains).

## Usage

Add the package to your `lakefile.toml`:

```toml
[[require]]
name = "secp256k1"
git = "https://github.com/karask/lean-ecdsa"
rev = "main"
```

Example:

```lean
import Secp256k1
open Secp256k1 Secp256k1.ECDSA

def demo : IO Unit := do
  let some sk := PrivateKey.ofBytes?
      (Hex.decode! "c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721")
    | throw (.userError "invalid private key")
  let pk := sk.publicKey
  IO.println (Hex.encode pk.toBytes)
  -- 032c8c31fc9f990c6b55e3865a184a4ce50e09481f2eaeb3e60ec1cea13a6ae645

  -- Sign / verify SHA-256(msg)
  let msg := "hello, secp256k1".toUTF8
  let some sig := sk.sign msg | throw (.userError "signing failed")
  IO.println (Hex.encode sig.toDER)
  -- 304402200efd2825…ae3f02204c35bc06…234e
  IO.println (pk.verify msg sig)                          -- true
  IO.println (pk.verify "tampered".toUTF8 sig)            -- false

  -- Public key recovery
  let some rsig := sk.signRecoverable msg | throw (.userError "signing failed")
  IO.println (PublicKey.recover? msg rsig == some pk)     -- true

  -- Sign a precomputed digest; verify as strictly as libsecp256k1 (reject high-S)
  let digest := SHA256.hash (SHA256.hash msg)
  let some sig2 := sk.signHash digest | throw (.userError "signing failed")
  IO.println (pk.verifyHash digest sig2 (requireLowS := true))  -- true
```

`sign` returns `Option` because RFC 6979 may in principle reject nonce candidates. It gives up after 64 rejected candidates, which in practice never happens.

## API overview

All ECDSA definitions live in `Secp256k1.ECDSA`.

| Definition | Description |
| --- | --- |
| `PrivateKey` | Constant-time scalar `d < n` with a proof that it was checked to be non-zero |
| `PrivateKey.ofBytes?` / `toBytes` / `generate` | Construct or encode a private key (constant time) |
| `PrivateKey.ofNat?` | Construct from a `Nat`; convenient for tests, but **not constant time** |
| `PrivateKey.publicKey` | The public key `d • G` (constant time) |
| `PublicKey` | Point with a proof that it is on the curve and not `𝒪` |
| `PublicKey.ofBytes?` / `toBytes (compressed := …)` | Parse or encode a SEC 1 public key |
| `PrivateKey.sign` / `signHash` | Sign a message or a digest. Options: `lowS := true`, `extraEntropy := …` |
| `PrivateKey.signRecoverable` / `signHashRecoverable` | Same as above, also returning the recovery id |
| `PublicKey.verify` / `verifyHash` | Verify a signature. Option: `requireLowS := false` |
| `PublicKey.recover?` / `recoverHash?` | Recover the public key from a `RecoverableSignature` |
| `Signature.toCompact` / `ofCompact?` | Encode or parse a 64-byte `r ‖ s` signature |
| `Signature.toDER` / `ofDER?` | Encode or parse a strict DER (BIP 66) signature |
| `Signature.normalize` / `isLowS` | Convert to, or check for, low-S form |
| `signWithNonce` | Sign with an explicit nonce (a `CT.Scalar`). A reused nonce leaks the private key |

Lower-level modules:

- `Secp256k1.Field`: domain parameters, `Fp`, `Fn`, modular inverse and square root.
- `Secp256k1.Curve`: `Point`, the group operations `+`, `-` and `k • P`, `Point.smulAdd`, and SEC 1 point encoding.
- `Secp256k1.SHA256`: `SHA256.hash` and `SHA256.hmac`.
- `Secp256k1.RFC6979`: the nonce generator.
- `Secp256k1.Bytes`: big-endian conversions and `Hex.encode` / `Hex.decode?`.
- `Secp256k1.CT.U256`: constant-time 256-bit limbs, masks, and Montgomery arithmetic modulo `p` and `n`.
- `Secp256k1.CT.Field`: constant-time field elements `Fe` and scalars `Scalar`.
- `Secp256k1.CT.Point`: complete projective formulas and constant-time `k • P` / `k • G`.
- `Secp256k1.CT.Lemmas`: proved facts about the word-level tricks.

The type invariants mean that every `PrivateKey` is non-zero and every `PublicKey` is a valid curve point. A few properties are proved in Lean, for example:

- `p = 2^256 - 2^32 - 977`
- `G` is on the curve
- `Signature.normalize` always yields a low-S signature
- encoding sizes are correct
- the constant-time mask, select, borrow and multiply-accumulate primitives behave as intended (by `bv_decide` and `omega`)

## Side-channel hardening

Secrets are the private key `d` and the nonce `k`. They are handled only as byte arrays or as `CT.U256` values, never as `Nat`:

- **Fixed-width arithmetic.** A `U256` is eight 32-bit limbs in `UInt64` words, so a limb product plus two carries never overflows. Every operation is a fixed sequence of word operations, and choices are made with bit masks instead of branches.
- **Montgomery multiplication** (CIOS) modulo `p` and `n`, with a masked final subtraction. Inversion is Fermat's `a^(m-2)`; the sequence of squarings and multiplications depends only on the public exponent.
- **Complete addition formulas** (Renes–Costello–Batina 2016, Algorithms 7 and 9). They are correct for all inputs, including doubling, `P + (-P)` and the point at infinity, so they need no case distinctions.
- **Fixed-window scalar multiplication.** All 64 4-bit windows of the scalar are processed, each with four doublings and one addition. Every table lookup reads all 16 entries and keeps the wanted one with a mask.
- **RFC 6979 on bytes.** The key and nonce candidates stay as bytes, and SHA-256 output uses shifts rather than `Nat` division.

Values are converted to `Nat` only once they are public: `R`, `r`, `s` and the recovery id. Verification and recovery use only public data and keep the faster variable-time reference arithmetic, as libsecp256k1 does.

### Evidence

- **Timing test.** `lake exe timing [samples]` is a dudect-style test. It times a fixed nonce `k = 1` against random nonces and applies Welch's t-test; `|t| > 4.5` indicates a leak. The old variable-time scalar multiplication is included as a positive control. With 5,000 samples per operation in one x86-64 container:

  | Operation | fixed k = 1 | random k | \|t\| |
  | --- | --- | --- | --- |
  | Reference `k • G` (variable time) | 0.3 µs | 1666 µs | **1003.8** (leak) |
  | Constant-time `k • G` | 1807 µs | 1801 µs | 0.7 |
  | Constant-time `k⁻¹ mod n` | 250 µs | 249 µs | 0.2 |
  | `signWithNonce` | 2229 µs | 2220 µs | 0.7 |

- **Generated C.** `python3 scripts/list_c_branches.py` lists every branch in the C code Lean generates for the `CT` modules. Currently each one tests public data: reference counts used for in-place memory reuse, loop counters, table bounds, public window indices, or bits of public exponents.
- **Tests and proofs.** `Tests/CT.lean` compares every constant-time operation with the reference arithmetic on edge cases and pseudo-random inputs, and `Secp256k1.CT.Lemmas` proves the word-level primitives.

### What remains

- **Machine code.** The C compiler could still turn masked selects into branches. This needs a binary-level check, such as running under valgrind with secrets marked as undefined (as libsecp256k1's `ctime_tests` does).
- **Memory hygiene and randomness.** Wiping secrets and using a vetted CSPRNG both need small C bindings.
- **Proofs.** Prove that `U256` / Montgomery arithmetic equals the `Fin p` / `Fin n` reference, and that the projective formulas implement the curve group law (for example against Mathlib's Weierstrass curves).
- **Fault attacks.** Offer verify-after-sign, and blind the scalar or base point.
- **Assurance.** Add Project Wycheproof vectors, differential fuzzing against libsecp256k1, and an independent audit.

## Building and testing

```sh
lake build   # build the library
lake test    # run the test suite
```

The test suite runs about 11,800 checks. The test vectors in `Tests/Vectors.lean` come from independent implementations:

- **libsecp256k1** (through `coincurve`):
  - public keys, compressed and uncompressed
  - RFC 6979 low-S signatures, with and without additional data
  - DER encodings and recovery ids
- **python-ecdsa**:
  - signatures without low-S normalisation
  - 20-, 32- and 64-byte digests, to exercise `bits2int` truncation
  - RFC 6979 additional data
- **Python `hashlib` / `hmac`**: SHA-256 at the one- and two-block padding boundaries, and the HMAC-SHA-256 test cases from RFC 4231.

Other tests check the group laws, rejection of malformed keys, points and DER encodings, sign/verify/recover round trips with random keys, and the constant-time arithmetic against the reference implementation.

To regenerate the vectors:

```sh
pip install coincurve ecdsa
python3 scripts/gen_test_vectors.py > Tests/Vectors.lean
```

In one x86-64 Linux container, a signature took about 2.2 ms and a verification about 3.5 ms.

## References

- [SEC 1 v2: Elliptic Curve Cryptography](https://www.secg.org/sec1-v2.pdf)
- [SEC 2 v2: Recommended Elliptic Curve Domain Parameters](https://www.secg.org/sec2-v2.pdf)
- [RFC 6979: Deterministic Usage of DSA and ECDSA](https://www.rfc-editor.org/rfc/rfc6979)
- [FIPS 180-4: Secure Hash Standard](https://csrc.nist.gov/pubs/fips/180-4/upd1/final), and [RFC 2104: HMAC](https://www.rfc-editor.org/rfc/rfc2104)
- [Renes, Costello, Batina: Complete addition formulas for prime order elliptic curves (2016)](https://eprint.iacr.org/2015/1060)
- [Koç, Acar, Kaliski: Analyzing and comparing Montgomery multiplication algorithms (1996)](https://doi.org/10.1109/40.502403)
- [Reparaz, Balasch, Verbauwhede: Dude, is my code constant time? (2017)](https://eprint.iacr.org/2016/1123)
- [BIP 66: Strict DER signatures](https://github.com/bitcoin/bips/blob/master/bip-0066.mediawiki), and [BIP 146: Low-S](https://github.com/bitcoin/bips/blob/master/bip-0146.mediawiki)
