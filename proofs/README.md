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

All of these depend only on `propext`, `Classical.choice` and `Quot.sound`;
`CheckAxioms.lean` prints them and CI fails on `sorryAx` or `Lean.ofReduceBool`.
