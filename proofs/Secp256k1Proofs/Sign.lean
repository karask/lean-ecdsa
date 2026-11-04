import Mathlib.FieldTheory.Finite.Basic
import Secp256k1Proofs.PublicKey

/-!
# Signatures satisfy the ECDSA verification equation

`signWithNonce_verifies`: for every signature `(r, s)` produced by
`ECDSA.signWithNonce` (the function behind `PrivateKey.sign`), `r` and `s`
lie in `[1, n-1]` and, with `w = s⁻¹`, `u₁ = e·w` and `u₂ = r·w` modulo `n`
(computed exactly as in `PublicKey.verifyHash`), the point `u₁ • G + u₂ • Q`
is an affine point whose `x`-coordinate is `r` modulo `n`.

The argument is the textbook one: `u₁ + u₂·d = s⁻¹(e + r·d) = ±k (mod n)`, and
since `G` has order `n`, `u₁ • G + u₂ • Q = ±(k • G) = ±R`, which has the same
`x`-coordinate as `R`. The sign accounts for low-S normalisation.
-/

open Secp256k1

namespace Secp256k1Proofs

instance : Fact (Nat.Prime n) := ⟨nat_prime_n⟩

/-! ## Arithmetic modulo `n` -/

theorem pow_n_sub_two (a : ZMod n) : a ^ (n - 2) = a⁻¹ := by
  by_cases ha : a = 0
  · subst ha; rw [zero_pow (by decide), inv_zero]
  · apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, show n - 2 + 1 = n - 1 by decide]
    exact ZMod.pow_card_sub_one_eq_one ha

theorem Fn.val_ofNat' (a : Nat) : (Fn.ofNat a).val = a % n := Fin.val_ofNat n a

theorem Fn.val_inv (a : Fn) : (Fn.inv a).val = a.val ^ (n - 2) % n := by
  show (Fin.ofNat n (powMod a.val (n - 2) n)).val = _
  rw [Fin.val_ofNat, powMod_eq _ _ _ n_pos, Nat.mod_mod]

/-- `(a · b⁻¹ mod n)`, as `verifyHash` computes `u₁` and `u₂`. -/
theorem cast_mul_inv (a b : Nat) :
    (((Fn.ofNat a * Fn.inv (Fn.ofNat b)).val : ℕ) : ZMod n) = (a : ZMod n) * (b : ZMod n)⁻¹ := by
  rw [Fin.val_mul, ZMod.natCast_mod, Nat.cast_mul, Fn.val_inv, ZMod.natCast_mod, Nat.cast_pow,
    Fn.val_ofNat', Fn.val_ofNat', ZMod.natCast_mod, ZMod.natCast_mod, pow_n_sub_two]

theorem natCast_ne_zero {a : Nat} (h0 : 0 < a) (hn : a < n) : (a : ZMod n) ≠ 0 := by
  intro h
  rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hn] at h
  rw [h] at h0
  exact absurd h0 (by decide)

theorem natCast_sub_self {a : Nat} (h : a ≤ n) : ((n - a : ℕ) : ZMod n) = -(a : ZMod n) := by
  rw [Nat.cast_sub h, ZMod.natCast_self, zero_sub]

/-! ## Multiples of `G` -/

/-- Multiples of `G` depend only on the multiplier modulo `n`. -/
theorem nsmul_G_congr {a b : ℕ} (h : (a : ZMod n) = (b : ZMod n)) :
    a • toW G G_onCurve = b • toW G G_onCurve := by
  have h1 := mod_addOrderOf_nsmul (toW G G_onCurve) a
  have h2 := mod_addOrderOf_nsmul (toW G G_onCurve) b
  rw [addOrderOf_G] at h1 h2
  rw [← h1, ← h2, (ZMod.natCast_eq_natCast_iff' a b n).1 h]

theorem sub_nsmul_G {a : ℕ} (h : a ≤ n) :
    (n - a) • toW G G_onCurve = -(a • toW G G_onCurve) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← add_nsmul, Nat.sub_add_cancel h, n_smul_G]

theorem neg_onCurve {x y : Fp} (h : (Point.affine x y).OnCurve) : (Point.affine x (-y)).OnCurve := by
  have h' : y * y = x * x * x + 7 := h
  show -y * -y = x * x * x + 7
  grind

/-- `(x, -y)` is the negative of `(x, y)`. -/
theorem toW_neg {x y : Fp} (h : (Point.affine x y).OnCurve) :
    toW (.affine x (-y)) (neg_onCurve h) = -toW (.affine x y) h := by
  show WeierstrassCurve.Affine.Point.some _ _ _ = -(WeierstrassCurve.Affine.Point.some _ _ _)
  rw [WeierstrassCurve.Affine.Point.neg_some]
  congr 1
  rw [W_negY, map_neg]

/-! ## The verification equation -/

-- `smulGSpec` unfolds to a 64-step recursion.
set_option maxRecDepth 10000 in
/-- **ECDSA signatures verify.** For every signature `(r, s)` returned by
`signWithNonce`, `r, s ∈ [1, n-1]`, and with `w = s⁻¹`, `u₁ = e·w`,
`u₂ = r·w` modulo `n` (as in `PublicKey.verifyHash`), `u₁ • G + u₂ • Q` is an
affine point `(x, y)` with `x ≡ r (mod n)`, where `Q` is the signer's public key. -/
theorem signWithNonce_verifies {sk : ECDSA.PrivateKey} {e : Nat} {k : CT.Scalar} {lowS : Bool}
    {rsig : ECDSA.RecoverableSignature} (hk : k.Valid)
    (h : ECDSA.signWithNonce sk e k lowS = some rsig) :
    0 < rsig.sig.r ∧ rsig.sig.r < n ∧ 0 < rsig.sig.s ∧ rsig.sig.s < n ∧
    ∃ (x y : Fp) (hxy : (Point.affine x y).OnCurve),
      (Fn.ofNat e * Fn.inv (Fn.ofNat rsig.sig.s)).val • toW G G_onCurve +
        (Fn.ofNat rsig.sig.r * Fn.inv (Fn.ofNat rsig.sig.s)).val •
          toW sk.publicKey.point sk.publicKey.onCurve =
        toW (.affine x y) hxy ∧
      x.val % n = rsig.sig.r := by
  obtain ⟨x, y, hR, hr, hr0, hrn, hk0, s₀, hs₀, hs0, hsn, flip, hs, -, -⟩ :=
    ECDSA.signWithNonce_spec hk h
  have hsr : 0 < rsig.sig.s ∧ rsig.sig.s < n := by
    rw [hs]; cases flip <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  refine ⟨hr0, hrn, hsr.1, hsr.2, ?_⟩
  -- `R = k • G` and `Q = d • G`
  have hRon : (Point.affine x y).OnCurve := hR ▸ smulGSpec_onCurve k
  have hRW : toW (.affine x y) hRon = k.toNat • toW G G_onCurve :=
    (toW_congr hR.symm hRon (smulGSpec_onCurve k)).trans (toW_smulGSpec k hk)
  obtain ⟨hQ, hQW⟩ := publicKey_correct sk
  rw [toW_congr rfl _ hQ, hQW, smul_smul, ← add_nsmul]
  -- `u₁ + u₂·d = s⁻¹(e + r·d) = ±k (mod n)`
  set K : ZMod n := (k.toNat : ZMod n)
  set X : ZMod n := (e : ZMod n) + (rsig.sig.r : ZMod n) * (sk.scalar.toNat : ZMod n)
  have hK : K ≠ 0 := natCast_ne_zero (Nat.pos_of_ne_zero (by omega)) hk.2
  have hS₀ : (s₀ : ZMod n) = K⁻¹ * X := by
    rw [hs₀]
    simp only [CT.sSpec, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, ZMod.natCast_mod, pow_n_sub_two,
      K, X]
  have hX : X ≠ 0 := by
    intro h0
    apply natCast_ne_zero hs0 hsn
    rw [hS₀, h0, mul_zero]
  have hu : (((Fn.ofNat e * Fn.inv (Fn.ofNat rsig.sig.s)).val +
      (Fn.ofNat rsig.sig.r * Fn.inv (Fn.ofNat rsig.sig.s)).val * sk.scalar.toNat : ℕ) : ZMod n) =
      (rsig.sig.s : ZMod n)⁻¹ * X := by
    rw [Nat.cast_add, Nat.cast_mul, cast_mul_inv, cast_mul_inv]
    ring
  have hkn : k.toNat ≤ n := hk.2.le
  cases flip with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hs
    have hkey : (rsig.sig.s : ZMod n)⁻¹ * X = K := by
      rw [hs, hS₀, mul_inv, inv_inv, mul_assoc, inv_mul_cancel₀ hX, mul_one]
    refine ⟨x, y, hRon, ?_, hr.symm⟩
    rw [nsmul_G_congr (hu.trans hkey), hRW]
  | true =>
    simp only [↓reduceIte] at hs
    have hkey : (rsig.sig.s : ZMod n)⁻¹ * X = ((n - k.toNat : ℕ) : ZMod n) := by
      rw [hs, natCast_sub_self hsn.le, hS₀, natCast_sub_self hkn, inv_neg, mul_inv, inv_inv,
        neg_mul, mul_assoc, inv_mul_cancel₀ hX, mul_one]
    refine ⟨x, -y, neg_onCurve hRon, ?_, hr.symm⟩
    rw [nsmul_G_congr (hu.trans hkey), sub_nsmul_G hkn, ← hRW, toW_neg]

/-- **Signatures from `PrivateKey.signHash` verify**: `signWithNonce_verifies`
with `e = hashToScalar h`, whatever nonce the RFC 6979 loop accepted, and with
or without `verifyAfterSign`. -/
theorem signHash_verifies {sk : ECDSA.PrivateKey} {h : ByteArray} {lowS : Bool}
    {extra : ByteArray} {verifyAfterSign : Bool} {sig : ECDSA.Signature}
    (hs : sk.signHash h lowS extra verifyAfterSign = some sig) :
    0 < sig.r ∧ sig.r < n ∧ 0 < sig.s ∧ sig.s < n ∧
    ∃ (x y : Fp) (hxy : (Point.affine x y).OnCurve),
      (Fn.ofNat (ECDSA.hashToScalar h) * Fn.inv (Fn.ofNat sig.s)).val • toW G G_onCurve +
        (Fn.ofNat sig.r * Fn.inv (Fn.ofNat sig.s)).val •
          toW sk.publicKey.point sk.publicKey.onCurve =
        toW (.affine x y) hxy ∧
      x.val % n = sig.r := by
  obtain ⟨k, rsig, hk, hw, rfl⟩ := ECDSA.PrivateKey.signHash_spec hs
  exact signWithNonce_verifies hk hw

/-- **Signatures from `PrivateKey.sign` verify**, with `e` derived from
`SHA-256(msg)`. -/
theorem sign_verifies {sk : ECDSA.PrivateKey} {msg : ByteArray} {lowS : Bool}
    {extra : ByteArray} {verifyAfterSign : Bool} {sig : ECDSA.Signature}
    (hs : sk.sign msg lowS extra verifyAfterSign = some sig) :
    0 < sig.r ∧ sig.r < n ∧ 0 < sig.s ∧ sig.s < n ∧
    ∃ (x y : Fp) (hxy : (Point.affine x y).OnCurve),
      (Fn.ofNat (ECDSA.hashToScalar (SHA256.hash msg)) * Fn.inv (Fn.ofNat sig.s)).val •
          toW G G_onCurve +
        (Fn.ofNat sig.r * Fn.inv (Fn.ofNat sig.s)).val •
          toW sk.publicKey.point sk.publicKey.onCurve =
        toW (.affine x y) hxy ∧
      x.val % n = sig.r :=
  signHash_verifies hs

end Secp256k1Proofs
