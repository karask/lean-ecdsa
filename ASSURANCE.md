# Assurance case

This file is for reviewers and auditors. It covers:

- what the library claims
- the evidence behind each claim
- what you must trust for that evidence to hold
- how to reproduce the checks
- what is not covered

## Scope

ECDSA over secp256k1, as in SEC 1 v2 §4.1:

- key derivation `Q = d • G`
- signing with RFC 6979 nonces (optionally hedged), with low-S normalisation
- verification
- public key recovery
- encodings: SEC 1 public keys, compact and DER signatures, 32-byte private keys

SHA-256 and HMAC-SHA-256 are implemented in the library.

## Claims and evidence

### Functional correctness (machine-checked proofs)

| Claim | Theorem | File |
| --- | --- | --- |
| `p`, `n` are prime | `p_isPrime`, `n_isPrime` (Pratt certificates) | `Secp256k1/Certificates.lean` |
| Limb, Montgomery, field and scalar arithmetic are exact | `Modulus.mul_spec`, `Fe.inv_spec`, `Scalar.mul_inv`, … | `Secp256k1/CT/Proofs.lean` |
| The complete projective formulas implement the group law | `rcbAdd_correct`, `rcbDouble_correct` | `Secp256k1/GroupLaw.lean` |
| The constant-time point operations compute those formulas | `PPoint.add_correct`, `PPoint.double_correct` | `Secp256k1/CT/PointProofs.lean` |
| The table, masked lookup and windowed loop are correct | `table_correct`, `lookup_eq`, `smulDigits_correct` | `Secp256k1/CT/SmulProofs.lean` |
| The chord-and-tangent law is Mathlib's group law | `toW_add` | `proofs/Secp256k1Proofs/GroupLaw.lean` |
| `G` has order `n` | `windowSpec_n` (kernel computation), `addOrderOf_G` | `Secp256k1/OrderProofs.lean`, `proofs/…/PublicKey.lean` |
| The blinded constant-time `k • G` is `k • G` | `smulGBlind_correct`, `toW_blindSpec` | `Secp256k1/CT/SmulProofs.lean`, `proofs/…/PublicKey.lean` |
| Public keys are `d • G` | `publicKey_correct` | `proofs/…/PublicKey.lean` |
| The signing core computes `r = R.x mod n`, `s = k⁻¹(e + r·d)` | `signCore_spec`, `blinded_s` | `Secp256k1/CT/SignProofs.lean` |
| Signatures satisfy the verification equation | `sign_verifies` | `proofs/…/Sign.lean` |
| `verify` accepts exactly the valid signatures | `verifyHash_eq_true_iff` | `proofs/…/Verify.lean` |
| Every signature from `sign` passes `verify` | `verify_sign` | `proofs/…/Verify.lean` |
| Recovery returns the signer's key | `recover_signRecoverable` | `proofs/…/Recover.lean` |
| Encodings round-trip; DER parsing is canonical | `ofDER?_toDER`, `toDER_ofDER?`, `PublicKey.ofBytes?_toBytes`, … | `Secp256k1/BytesProofs.lean`, `Secp256k1/DERProofs.lean`, `proofs/…/Encoding.lean` |
| SHA-256 and HMAC meet FIPS 180-4 and RFC 2104 | `hash_eq_spec`, `hmac_eq_spec`, `K_spec`, `H0_spec` | `Secp256k1/SHA256Spec.lean`, `Secp256k1/SHA256Proofs.lean` |
| Signing uses the first valid RFC 6979 candidate | `findNonce_eq`, `signHashRecoverable_eq` | `Secp256k1/RFC6979Proofs.lean` |

### Side channels (evidence, not proofs)

- **valgrind (ctgrind/):** key derivation, the signing core, RFC 6979 and the constant-time arithmetic run with the secret bytes marked as undefined. memcheck reports no branch or memory address that depends on them. A variable-time positive control is flagged, and so is a planted secret-indexed lookup.
- **Timing (`lake exe timing`):** dudect-style Welch t-tests of fixed against random nonces. The variable-time reference is a positive control.
- **Generated C (`scripts/list_c_branches.py`):** every branch in the C code for the `CT` modules tests public data.
- **Countermeasures:** scalar blinding, randomised projective coordinates, multiplicative blinding of `s`, optional hedging, and optional verify-after-sign. Proofs show none of them changes any result.

### Testing

- All Wycheproof secp256k1 ECDSA vectors, in DER, Bitcoin low-S and P1363 forms.
- Vectors from libsecp256k1 and python-ecdsa.
- NIST SHA-256 and RFC 4231 HMAC cases.
- Differential fuzzing against libsecp256k1 (100,000 cases).

## What you must trust

1. **The Lean 4 kernel** (toolchain v4.35.0) and the three standard axioms `propext`, `Classical.choice` and `Quot.sound`. `scripts/CheckAxioms.lean` and `proofs/CheckAxioms.lean` check every theorem. Nothing uses `sorry`, `native_decide` or `bv_decide`. Some facts are proved by kernel evaluation: the Pratt certificates, `n • G = 𝒪`, and the SHA-256 constants. These rely on the kernel's GMP-backed natural-number arithmetic.
2. **The specifications.** The theorems relate the code to definitions that must themselves be right:
   - `Point.addSpec` and the curve equation (`Secp256k1/GroupLaw.lean`)
   - the Mathlib curve `W` (`proofs/Secp256k1Proofs/GroupLaw.lean`)
   - the statements of `verifyHash_eq_true_iff` and `sign_verifies` (SEC 1 §4.1.3–4.1.4)
   - `SHA256.Spec` (FIPS 180-4)
   - `SHA256.Spec.hmac` (RFC 2104)
   - `RFC6979.Spec` (RFC 6979 §3.2)

   Read these side by side with the documents.
3. **Mathlib** (pinned in `proofs/lake-manifest.json`) for the group structure on `WeierstrassCurve.Affine.Point`, which provides associativity.
4. **The compiler chain and runtime.** The proofs are about the Lean definitions, not the binary. Correct behaviour of the compiled code assumes the Lean compiler, the C compiler and the Lean runtime are correct (`ByteArray`, `UInt64`, reference counting). The tests exercise the compiled code. The valgrind and timing checks cover x86-64 Linux with the bundled toolchain.
5. **The operating system's random number generator**, via `IO.getRandomBytes`, for `PrivateKey.generate` and hedged signing. Deterministic signing needs no randomness.

## How to check

```sh
lake build && lake test                     # library and tests
lake env lean scripts/CheckAxioms.lean      # axioms of every library theorem
./ctgrind/run.sh                            # machine-code constant-time check (valgrind)
lake exe timing                             # timing test
(cd proofs && lake exe cache get && lake build && lake env lean CheckAxioms.lean)
pip install coincurve && lake build fuzz && python3 scripts/fuzz_vs_libsecp256k1.py --count 20000
```

CI runs the build, tests, axiom checks, ctgrind and the Mathlib proofs on every push.

## Not covered

- **Memory hygiene.** Secrets are not wiped. Copies of key and nonce limbs can remain in freed memory.
- **Other platforms and compilers.** The side-channel evidence is for x86-64 Linux only.
- **Physical attacks beyond the countermeasures above.** For example, template attacks on a single trace, and fault attacks other than those `verifyAfterSign` detects.
- **Misuse of `signWithNonce`.** Reusing a nonce reveals the key; use `sign` or `signHedged`.
- **An independent audit.** None has been done.

## Suggested review focus

1. **The specifications in "What you must trust" (2).** Do they say what the standards say?
2. **The `CT` code paths and the places marked `CT.declassify`** (`grep -rn declassify Secp256k1/`). These are the only places where secret-derived values become public.
3. **What the code assumes about the Lean runtime**, and how secrets flow through `ByteArray` values.
4. **The generated C for the `CT` modules** on your target platform, and a ctgrind run there.
