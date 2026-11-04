# lean-ecdsa

ECDSA over secp256k1 in Lean 4, with no dependencies beyond Lean core.

It includes:

- **Curve arithmetic.** Field and scalar arithmetic over `Fin p` / `Fin n`. Points are added in Jacobian coordinates, and double scalar multiplication uses Shamir's trick.
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
> This is a reference implementation. Do not use it to protect keys with real value. Arithmetic uses Lean's arbitrary-precision `Nat`, which is **not constant-time**, so timing and other side channels can leak secrets. `PrivateKey.generate` uses `IO.getRandomBytes`, and Lean does not guarantee that source is cryptographically secure.

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
| `PrivateKey` | Scalar `d` with a proof that `0 < d < n` |
| `PrivateKey.ofBytes?` / `ofNat?` / `toBytes` / `generate` | Construct or encode a private key |
| `PrivateKey.publicKey` | The public key `d • G` |
| `PublicKey` | Point with a proof that it is on the curve and not `𝒪` |
| `PublicKey.ofBytes?` / `toBytes (compressed := …)` | Parse or encode a SEC 1 public key |
| `PrivateKey.sign` / `signHash` | Sign a message or a digest. Options: `lowS := true`, `extraEntropy := …` |
| `PrivateKey.signRecoverable` / `signHashRecoverable` | Same as above, also returning the recovery id |
| `PublicKey.verify` / `verifyHash` | Verify a signature. Option: `requireLowS := false` |
| `PublicKey.recover?` / `recoverHash?` | Recover the public key from a `RecoverableSignature` |
| `Signature.toCompact` / `ofCompact?` | Encode or parse a 64-byte `r ‖ s` signature |
| `Signature.toDER` / `ofDER?` | Encode or parse a strict DER (BIP 66) signature |
| `Signature.normalize` / `isLowS` | Convert to, or check for, low-S form |
| `signWithNonce` | Sign with an explicit nonce. A reused nonce leaks the private key |

Lower-level modules:

- `Secp256k1.Field`: domain parameters, `Fp`, `Fn`, modular inverse and square root.
- `Secp256k1.Curve`: `Point`, the group operations `+`, `-` and `k • P`, `Point.smulAdd`, and SEC 1 point encoding.
- `Secp256k1.SHA256`: `SHA256.hash` and `SHA256.hmac`.
- `Secp256k1.RFC6979`: the nonce generator.
- `Secp256k1.Bytes`: big-endian conversions and `Hex.encode` / `Hex.decode?`.

The type invariants mean that every `PrivateKey` is in range and every `PublicKey` is a valid curve point. A few properties are proved in Lean, for example:

- `p = 2^256 - 2^32 - 977`
- `G` is on the curve
- `Signature.normalize` always yields a low-S signature
- encoding sizes are correct

## Building and testing

```sh
lake build   # build the library
lake test    # run the test suite
```

The test suite runs about 3,100 checks. The test vectors in `Tests/Vectors.lean` come from independent implementations:

- **libsecp256k1** (through `coincurve`):
  - public keys, compressed and uncompressed
  - RFC 6979 low-S signatures, with and without additional data
  - DER encodings and recovery ids
- **python-ecdsa**:
  - signatures without low-S normalisation
  - 20-, 32- and 64-byte digests, to exercise `bits2int` truncation
  - RFC 6979 additional data
- **Python `hashlib` / `hmac`**: SHA-256 at the one- and two-block padding boundaries, and the HMAC-SHA-256 test cases from RFC 4231.

Other tests check the group laws, rejection of malformed keys, points and DER encodings, and sign/verify/recover round trips with random keys.

To regenerate the vectors:

```sh
pip install coincurve ecdsa
python3 scripts/gen_test_vectors.py > Tests/Vectors.lean
```

In one x86-64 Linux container, a signature took about 3 ms and a verification about 3.5 ms.

## References

- [SEC 1 v2: Elliptic Curve Cryptography](https://www.secg.org/sec1-v2.pdf)
- [SEC 2 v2: Recommended Elliptic Curve Domain Parameters](https://www.secg.org/sec2-v2.pdf)
- [RFC 6979: Deterministic Usage of DSA and ECDSA](https://www.rfc-editor.org/rfc/rfc6979)
- [FIPS 180-4: Secure Hash Standard](https://csrc.nist.gov/pubs/fips/180-4/upd1/final), and [RFC 2104: HMAC](https://www.rfc-editor.org/rfc/rfc2104)
- [BIP 66: Strict DER signatures](https://github.com/bitcoin/bips/blob/master/bip-0066.mediawiki), and [BIP 146: Low-S](https://github.com/bitcoin/bips/blob/master/bip-0146.mediawiki)
