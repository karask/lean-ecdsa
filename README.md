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
> Hardening is well advanced, but the library is **not yet suitable for keys with real value**. What is done:
> - The secret-dependent code passes a valgrind check of its machine code.
> - Its field and scalar arithmetic is proved correct, including inversion. `p` and `n` are proved prime with Pratt certificates checked by the Lean kernel.
> - Its point addition and doubling are proved to implement the elliptic curve group law, in every case.
> - It agrees with libsecp256k1 on 100,000 fuzzed inputs.
>
> However:
> - secrets are not wiped from memory
> - the windowed scalar multiplication loop is tested, but not proved to compute `k • P`
> - key generation depends on Lean's undocumented choice of randomness source (currently the OS generator)
> - nothing has been audited
>
> See [what remains](#what-remains).

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
| `PrivateKey.sign` / `signHash` | Sign a message or a digest. Options: `lowS := true`, `extraEntropy := …`, `verifyAfterSign := false` (fault countermeasure) |
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
- `Secp256k1.CT.Sign`: the constant-time ECDSA signing core.
- `Secp256k1.CT.Lemmas`: proved facts about the word-level tricks.
- `Secp256k1.CT.Proofs`: correctness proofs for the limb, Montgomery, scalar and field arithmetic.
- `Secp256k1.Primality`: a proof of the Lucas primality test, and of `powMod`.
- `Secp256k1.Certificates`: Pratt certificates proving `p` and `n` prime, plus Fermat's little theorem for both. Generated by `scripts/gen_pratt_certificates.py` and checked by the kernel.
- `Secp256k1.GroupLaw`: the group law, and proofs that the complete projective formulas implement it.
- `Secp256k1.CT.PointProofs`: proofs that the constant-time point operations implement the group law.
- `Secp256k1.CT.SmulProofs`: proofs for the precomputed table, the constant-time lookup, the windowed scalar multiplication and the conversion to affine coordinates.
- `Secp256k1.CT.ParseProofs`: parsed scalars are in range, which `PrivateKey` keeps as an invariant.
- `Secp256k1.OrderProofs`: `n • G = 𝒪`, computed by the kernel.
- `Secp256k1.CT.SignProofs`: what the constant-time signing core and `signWithNonce` / `signHash` return.
- `Secp256k1.JacobianProofs`: the Jacobian reference arithmetic and Shamir's trick, used by verification, implement the group law.
- [`proofs/`](proofs/README.md): a separate package, depending on Mathlib, for the results that need associativity of the group law.

The type invariants mean that every `PrivateKey` holds a scalar in `[1, n-1]` (checked at runtime, carried as a proof) and every `PublicKey` is a valid curve point. A few properties are proved in Lean, for example:

- `p = 2^256 - 2^32 - 977`
- `p` and `n` are prime (`p_isPrime`, `n_isPrime`), so Fermat's little theorem holds for both (`fermat_p`, `fermat_n`). The proof checks a tree of 80 Pratt certificates, each verified with the Lucas test (`Secp256k1.Primality`) by `decide +kernel`.
- `G` is on the curve
- `Signature.normalize` always yields a low-S signature
- encoding sizes are correct
- the constant-time arithmetic computes the right values (`Secp256k1.CT.Proofs`):
  - `U256.add_toNat`, `U256.sub_toNat`, `U256.mulAddRow_toNat`: the carry and borrow chains are exact
  - `Modulus.mul_spec`: Montgomery multiplication returns the canonical `c < m` with `c · 2²⁵⁶ ≡ a · b (mod m)`, for any odd modulus satisfying `Modulus.Valid`
  - `Modulus.add_spec`, `Modulus.sub_spec`, `Modulus.toMont_spec`, `Modulus.fromMont_spec`: modular addition, subtraction and Montgomery conversion
  - `pMod_valid`, `nMod_valid`: the precomputed constants for `p` and `n` satisfy those assumptions
  - `Modulus.pow_repr`: square-and-multiply exponentiation in Montgomery form
  - `Scalar.mul_spec`, `Scalar.add_spec`, `Scalar.sub_spec`, `Scalar.inv_spec`: arithmetic modulo `n`, where `inv` computes `a^(n-2) mod n`
  - `Fe.mul_spec`, `Fe.add_spec`, `Fe.sub_spec`, `Fe.neg_spec`, `Fe.inv_spec`: arithmetic modulo `p` on canonical values, where `inv` computes `a^(p-2) mod p`
  - `Fe.mul_inv`, `Scalar.mul_inv`: inversion is correct, `a · a⁻¹ = 1` for `a ≠ 0`
- the point formulas implement the group law (`Secp256k1.GroupLaw`, `Secp256k1.CT.PointProofs`):
  - `Point.addSpec` is the chord-and-tangent law, with the same cases and slopes as Mathlib's `WeierstrassCurve.Affine`
  - `rcbAdd_correct`, `rcbDouble_correct`: for any points on the curve and any projective representatives, the complete formulas (Renes–Costello–Batina 2016) return a representative of `P + Q` (resp. `P + P`). In particular they never return the invalid triple `(0, 0, 0)`.
  - `addSpec_onCurve`: the sum of two points on the curve is on the curve
  - `PPoint.add_correct`, `PPoint.double_correct`: the constant-time limb code computes exactly those formulas, so it implements the group law
  - Supporting facts: `𝔽ₚ` is a field, `−7` is not a cube in `𝔽ₚ` (no 2-torsion), and `3` is not a square (no 4-torsion). The polynomial identities are proved by Lean's `grind`.
- the constant-time scalar multiplication computes `k • P` (`Secp256k1.CT.SmulProofs`, and `proofs/` for the last step):
  - `PPoint.table_correct`, `PPoint.lookup_eq`: the table holds `0 • P, …, 15 • P`, and the masked lookup over all 16 entries returns the wanted one
  - `PPoint.smul_correct`, `PPoint.smulG_correct`: the 64-window loop computes `Point.windowSpec` on the base-16 digits of the scalar
  - `PPoint.toPoint_eq`: conversion to affine coordinates returns the represented point
  - `Secp256k1Proofs.toW_add` (Mathlib): `Point.addSpec` is the addition of Mathlib's `AddCommGroup` of points on `y² = x³ + 7` over `ZMod p`, so associativity and commutativity come from Mathlib
  - `Secp256k1Proofs.smulG_correct` (Mathlib): `CT.PPoint.smulG k` represents `k • G`
- the public key is `d • G`:
  - `Scalar.ofBytes?_valid`: parsed scalars have 32-bit limbs and are below `n`, so every `PrivateKey` satisfies `Scalar.Valid`
  - `windowSpec_n`: `n • G = 𝒪`. The kernel evaluates the windowed algorithm with the complete formulas in about a second.
  - `Secp256k1Proofs.addOrderOf_G` (Mathlib): `G` has order `n`, because `n` is prime and `G ≠ 𝒪`
  - `Secp256k1Proofs.publicKey_correct` (Mathlib): for every private key `d`, `PrivateKey.publicKey` returns `d • G`. The fallback branch for an invalid result is unreachable.
- signatures are correct (`Secp256k1.CT.SignProofs`, and `proofs/` for the last step):
  - `signCore_spec`: the constant-time signing core returns `r = R.x mod n` and `s = k⁻¹(e + r·d) mod n` for `R = k • G`, the recovery id `R.y mod 2 + 2·[R.x ≥ n]`, and a success flag that is set exactly when `k`, `r` and `s` are non-zero
  - `signWithNonce_spec`: the returned signature is `(r, s)` or, after low-S normalisation, `(r, n - s)` with the recovery id flipped to match
  - `signHash_spec`: every signature from `signHash` comes from `signWithNonce` with a valid nonce accepted by the RFC 6979 loop
  - `Secp256k1Proofs.sign_verifies` (Mathlib): every signature `(r, s)` returned by `PrivateKey.sign` satisfies the ECDSA verification equation. `r, s ∈ [1, n-1]`, and with `u₁ = e·s⁻¹`, `u₂ = r·s⁻¹ mod n` (computed as in `verifyHash`), `u₁ • G + u₂ • Q` is an affine point whose `x`-coordinate is `r` modulo `n`.
- verification is correct (`Secp256k1.JacobianProofs`, and `proofs/` for the last step):
  - `Jacobian.double_correct`, `Jacobian.add_correct`, `Jacobian.toPoint_eq`: the Jacobian formulas implement the group law, including `𝒪`, `P + P` and `P + (-P)`
  - `Point.smulAdd_eq` and `Secp256k1Proofs.toW_smulAdd` (Mathlib): Shamir's trick `Point.smulAdd a A b B` computes `a • A + b • B`
  - `Secp256k1Proofs.verifyHash_eq_true_iff` (Mathlib): `verifyHash` returns `true` exactly for signatures satisfying the verification equation (with `r, s ∈ [1, n-1]`, and low-S if required). So it accepts every valid signature and rejects every invalid one.
  - `Secp256k1Proofs.verify_sign` (Mathlib): **every signature produced by `PrivateKey.sign` passes `PublicKey.verify`** for the signer's public key, also with `requireLowS` when signing used `lowS`
- recovery is correct (`proofs/`):
  - `sqrt?_mul_self`, `lift?_eq`: the square root `a^((p+1)/4)` finds a root of every non-zero square, and `Point.lift?` returns the curve point with the requested `x`-coordinate and parity of `y`
  - `Secp256k1Proofs.recover_signRecoverable`: **for every recoverable signature produced by `PrivateKey.signRecoverable`, `PublicKey.recover?` returns the signer's public key**. The recovery id selects `R.x` (including `R.x ≥ n`) and the parity of `R.y`, with the low-S flip taken into account.

These theorems depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`); CI checks this for the Mathlib theorems. Three standalone word lemmas in `Secp256k1.CT.Lemmas` use `bv_decide`, which additionally trusts compiled code; the theorems above don't depend on them.

## Side-channel hardening

Secrets are the private key `d` and the nonce `k`. They are handled only as byte arrays or as `CT.U256` values, never as `Nat`:

- **Fixed-width arithmetic.** A `U256` is eight 32-bit limbs in `UInt64` words, so a limb product plus two carries never overflows. Every operation is a fixed sequence of word operations, and choices are made with bit masks instead of branches.
- **Montgomery multiplication** (CIOS) modulo `p` and `n`, with a masked final subtraction. Inversion is Fermat's `a^(m-2)`; the sequence of squarings and multiplications depends only on the public exponent.
- **Complete addition formulas** (Renes–Costello–Batina 2016, Algorithms 7 and 9). They are correct for all inputs, including doubling, `P + (-P)` and the point at infinity, so they need no case distinctions.
- **Fixed-window scalar multiplication.** All 64 4-bit windows of the scalar are processed, each with four doublings and one addition. Every table lookup reads all 16 entries and keeps the wanted one with a mask.
- **RFC 6979 on bytes.** The key and nonce candidates stay as bytes, and SHA-256 output uses shifts rather than `Nat` division.

The whole secret-dependent part of signing is a single branch-free function, `CT.signCore`. It computes `R = k • G`, `r`, `s = k⁻¹(e + r·d)`, the recovery id and a success flag.

Secret-derived values become public in exactly four places, each marked with `CT.declassify`:
- the signature produced by `signCore`
- the affine coordinates in `PPoint.toPoint`, used for public keys and `R`
- whether a scalar is in range (`Scalar.ofBytes?`)
- whether a private key is non-zero

Only after these points are values converted to `Nat` (`grep -rn declassify Secp256k1/` lists them). Verification and recovery use only public data and keep the faster variable-time reference arithmetic, as libsecp256k1 does.

### Evidence

- **Timing test.** `lake exe timing [samples]` is a dudect-style test. It times a fixed nonce `k = 1` against random nonces and applies Welch's t-test; `|t| > 4.5` indicates a leak. The old variable-time scalar multiplication is included as a positive control. With 5,000 samples per operation in one x86-64 container:

  | Operation | fixed k = 1 | random k | \|t\| |
  | --- | --- | --- | --- |
  | Reference `k • G` (variable time) | 0.3 µs | 1666 µs | **1003.8** (leak) |
  | Constant-time `k • G` | 1807 µs | 1801 µs | 0.7 |
  | Constant-time `k⁻¹ mod n` | 250 µs | 249 µs | 0.2 |
  | `signWithNonce` | 2229 µs | 2220 µs | 0.7 |

- **Machine code (valgrind).** [`ctgrind/`](ctgrind/README.md) runs key derivation, the signing core, RFC 6979 and the scalar and field arithmetic under valgrind memcheck, with the key and nonce bytes marked as undefined. memcheck reports any branch or memory address in the compiled binary that depends on them. The constant-time code produces **0 errors**. The variable-time reference code, run as a positive control, produces errors, including 510 inside its double-and-add loop. Two further checks confirm the method:
  - A planted secret-indexed table lookup was caught.
  - A planted `if` on a mask was correctly not flagged, because clang compiles it to a branch-free `cmov`.

  CI runs this check on every push.
- **Generated C.** `python3 scripts/list_c_branches.py` lists every branch in the C code Lean generates for the `CT` modules. Each one tests public data: reference counts used for in-place memory reuse, loop counters, table bounds, public window indices, or bits of public exponents.
- **Tests and proofs.** `Tests/CT.lean` compares every constant-time operation with the reference arithmetic on edge cases and pseudo-random inputs. `Secp256k1.CT.Proofs` proves the limb, Montgomery, scalar and field arithmetic correct.

### What remains

- **Memory hygiene.** Secrets are not wiped. Lean values are immutable and reference-counted, so copies of the key and nonce limbs end up in freed memory. Wiping them needs runtime support, not just a C binding.
- **Randomness.** In Lean v4.35.0, `IO.getRandomBytes` reads `/dev/urandom` on Unix-like systems and calls `BCryptGenRandom` on Windows (`src/runtime/io.cpp`). These are the operating system's cryptographic generators, but Lean doesn't document this as a guarantee, so re-check it when changing toolchains. A `getrandom(2)` binding would also wait for the kernel generator to be seeded at early boot.
- **Proofs.** Key derivation, signing, verification and recovery are proved end to end, from the limb code to Mathlib's group: public keys are `d • G`, `verify` accepts exactly the signatures satisfying the verification equation, every signature from `sign` passes `verify`, and `recover?` returns the signer's key. Not yet proved:
  - SHA-256, HMAC and RFC 6979 against their specifications (the proofs hold for whatever nonce they produce), and the DER and SEC 1 encodings
- **Platforms.** The valgrind and timing checks cover x86-64 Linux with the bundled toolchain. Other platforms and compilers need their own runs.
- **Fault attacks.** `verifyAfterSign := true` checks each signature before releasing it. Scalar or base-point blinding is not implemented.
- **Assurance.** An independent audit.

## Building and testing

```sh
lake build   # build the library
lake test    # run the test suite
```

The Mathlib proofs are a separate package (see [`proofs/README.md`](proofs/README.md)):

```sh
cd proofs && lake exe cache get && lake build
```

The test suite runs about 13,300 checks. They include all 1,192 secp256k1 ECDSA verification vectors from [Project Wycheproof](https://github.com/C2SP/wycheproof), in three forms: DER, Bitcoin low-S and P1363. The files are vendored unchanged in `Tests/wycheproof/`, and these vectors probe malformed encodings, out-of-range values and arithmetic edge cases. The test vectors in `Tests/Vectors.lean` come from independent implementations:

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

Side-channel checks (see above):

```sh
lake exe timing          # dudect-style timing test
./ctgrind/run.sh         # valgrind machine-code check (needs valgrind)
```

Differential fuzzing against libsecp256k1:

```sh
pip install coincurve
lake build fuzz
python3 scripts/fuzz_vs_libsecp256k1.py --count 20000 [--seed S]
```

The fuzzer compares the following on random, edge-biased and mutated inputs:
- public key derivation
- RFC 6979 signing, with and without additional data
- verification of mutated DER signatures: bit flips, high-S twins, out-of-range and non-minimal integers, truncation, garbage
- public key recovery
- SEC 1 public key parsing

100,000 cases over five seeds produced no disagreements. With the low-S check deliberately disabled, the fuzzer reports 101 mismatches within 3,000 cases. The one intentional difference is that libsecp256k1 accepts "hybrid" public keys (prefix `0x06`/`0x07`) and this library does not, so the fuzzer doesn't generate them.

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
