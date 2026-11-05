# Mathlib proofs

The main library has no dependencies. This separate package depends on it and on
[Mathlib](https://github.com/leanprover-community/mathlib4), and proves the
facts that need Mathlib's formalisation of elliptic curves, chiefly
associativity of the group law.

```sh
cd proofs
lake exe cache get   # download prebuilt Mathlib (several GB)
lake build
lake env lean CheckAxioms.lean
```

## Contents

`Secp256k1Proofs/GroupLaw.lean`:

- `e : Fp ≃+* ZMod p`, and `W`, the curve `y² = x³ + 7` as a Mathlib
  `WeierstrassCurve.Affine (ZMod p)`.
- `toW`: points of the library (on the curve) to `W.Point`.
- `toW_add`: **`Point.addSpec` is Mathlib's addition**,
  `toW (A + B) = toW A + toW B`. With the library theorems
  `rcbAdd_correct`, `rcbDouble_correct` and `PPoint.add_correct`, this means
  the constant-time point operations compute the group law of Mathlib's
  `AddCommGroup W.Point`.
- `toW_windowSpec`: the windowed algorithm computes
  `16ʷ • B + (∑ⱼ digitⱼ 16ʲ) • A`.
- `smulG_correct`: **the constant-time `CT.PPoint.smulG k` represents
  `k • G`** for every valid scalar `k`.

`Secp256k1Proofs/PublicKey.lean`:

- `n_smul_G`, `addOrderOf_G`: **`G` has order `n`**. The kernel computes
  `n • G` in projective coordinates (`Secp256k1.windowSpec_n`, in the main
  library) and `n` is prime.
- `publicKey_correct`: **for every private key `d`,
  `PrivateKey.publicKey` returns `d • G`**. There are no hypotheses:
  `PrivateKey` carries `d ∈ [1, n-1]` as a proof, so the fallback branch of
  `PublicKey.ofPointD` is unreachable.

`Secp256k1Proofs/Sign.lean`:

- `signWithNonce_verifies`, `signHash_verifies`, `sign_verifies`: **every
  signature `(r, s)` produced by `PrivateKey.sign` satisfies the ECDSA
  verification equation**. `r, s ∈ [1, n-1]`, and with `u₁ = e·s⁻¹` and
  `u₂ = r·s⁻¹ mod n`, computed exactly as in `PublicKey.verifyHash`,
  `u₁ • G + u₂ • Q` is an affine point whose `x`-coordinate is `r` modulo
  `n`. This holds for every nonce the RFC 6979 loop can accept, with or
  without low-S normalisation.

`Secp256k1Proofs/Verify.lean`:

- `toW_smulAdd`: Shamir's trick `Point.smulAdd a A b B` (Jacobian
  coordinates) computes `a • A + b • B`.
- `verifyHash_eq_true_iff`: **`PublicKey.verifyHash` returns `true` exactly
  when the signature satisfies the verification equation** (`r, s ∈ [1, n-1]`,
  low-S if required).
- `verify_sign`: **every signature produced by `PrivateKey.sign` passes
  `PublicKey.verify`** for the signer's public key.

`Secp256k1Proofs/Recover.lean`:

- `sqrt?_mul_self`, `lift?_eq`: `Fp.sqrt?` finds a square root of every
  non-zero square, and `Point.lift?` returns the point with the requested
  `x`-coordinate and parity.
- `recover_signRecoverable`: **public key recovery returns the signer's key**
  for every recoverable signature produced by `PrivateKey.signRecoverable`.

`Secp256k1Proofs/Encoding.lean`:

- `PublicKey.ofBytes?_toBytes`: **parsing a serialised public key returns the
  same key**, in the compressed (`02/03 ‖ x`, decompressed with `lift?`) and
  the uncompressed (`04 ‖ x ‖ y`) SEC 1 form.

All of these depend only on `propext`, `Classical.choice` and `Quot.sound`;
`CheckAxioms.lean` prints them and CI fails on `sorryAx` or `Lean.ofReduceBool`.
