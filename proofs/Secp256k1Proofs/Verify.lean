import Secp256k1Proofs.Sign

/-!
# Verification

* `toW_smulAdd`: the Jacobian double scalar multiplication `Point.smulAdd`
  (Shamir's trick) computes `a • A + b • B`.
* `verifyHash_eq_true_iff`: **`PublicKey.verifyHash` accepts exactly the
  signatures that satisfy the ECDSA verification equation** (`r, s ∈ [1, n-1]`,
  low-S if required, and `u₁ • G + u₂ • Q` affine with `x ≡ r (mod n)`).
* `verify_sign`: **every signature produced by `PrivateKey.sign` passes
  `PublicKey.verify`** for the signer's public key.
-/

open Secp256k1

namespace Secp256k1Proofs

/-! ## Shamir's trick -/

theorem toW_shamirStep {A B C : Point} (hA : A.OnCurve) (hB : B.OnCurve) (hC : C.OnCurve)
    (ba bb : Bool) :
    toW (Point.shamirStep A B (A.addSpec B) ba bb C) (Point.shamirStep_onCurve hA hB hC ba bb) =
      2 • toW C hC + (if ba then 1 else 0) • toW A hA + (if bb then 1 else 0) • toW B hB := by
  have hd := Point.dbl_onCurve hC
  cases ba <;> cases bb
  · show toW C.dbl hd = _
    rw [toW_dbl hC]; simp
  · show toW (C.dbl.addSpec B) (addSpec_onCurve hd hB) = _
    rw [toW_add _ _ hd hB, toW_dbl hC]; simp
  · show toW (C.dbl.addSpec A) (addSpec_onCurve hd hA) = _
    rw [toW_add _ _ hd hA, toW_dbl hC]; simp
  · show toW (C.dbl.addSpec (A.addSpec B)) (addSpec_onCurve hd (addSpec_onCurve hA hB)) = _
    rw [toW_add _ _ hd (addSpec_onCurve hA hB), toW_add _ _ hA hB, toW_dbl hC]
    simp only [↓reduceIte, one_nsmul]; abel

theorem bit_mod (a w : Nat) : a % 2 ^ (w + 1) = a % 2 ^ w + 2 ^ w * (if a.testBit w then 1 else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ w) with h | h <;> simp [h]

/-- `shamirSpec` on `w` bits computes `2ʷ • C + (a mod 2ʷ) • A + (b mod 2ʷ) • B`. -/
theorem toW_shamirSpec {A B : Point} (hA : A.OnCurve) (hB : B.OnCurve) (a b : Nat) :
    ∀ (w : Nat) (C : Point) (hC : C.OnCurve),
      toW (Point.shamirSpec A B (A.addSpec B) a b w C) (Point.shamirSpec_onCurve hA hB a b w C hC) =
        2 ^ w • toW C hC + (a % 2 ^ w) • toW A hA + (b % 2 ^ w) • toW B hB
  | 0, C, hC => by simp [Point.shamirSpec, Nat.mod_one]
  | w + 1, C, hC => by
    have hS := Point.shamirStep_onCurve hA hB hC (a.testBit w) (b.testBit w)
    show toW (Point.shamirSpec A B (A.addSpec B) a b w _)
      (Point.shamirSpec_onCurve hA hB a b w _ hS) = _
    rw [toW_shamirSpec hA hB a b w _ hS, toW_shamirStep hA hB hC, bit_mod a w, bit_mod b w, pow_succ]
    module

theorem smulAdd_onCurve {A B : Point} (hA : A.OnCurve) (hB : B.OnCurve) (a b : Nat) :
    (Point.smulAdd a A b B).OnCurve := by
  rw [Point.smulAdd_eq hA hB]
  exact Point.shamirSpec_onCurve hA hB a b _ _ trivial

theorem lt_two_pow_max (a b : Nat) : a < 2 ^ (max a.log2 b.log2 + 1) :=
  Nat.lt_of_lt_of_le Nat.lt_log2_self
    (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ (Nat.le_max_left _ _)))

/-- **`Point.smulAdd a A b B` computes `a • A + b • B`.** -/
theorem toW_smulAdd {A B : Point} (hA : A.OnCurve) (hB : B.OnCurve) (a b : Nat)
    (h : (Point.smulAdd a A b B).OnCurve) :
    toW (Point.smulAdd a A b B) h = a • toW A hA + b • toW B hB := by
  rw [toW_congr (Point.smulAdd_eq hA hB a b) h (Point.shamirSpec_onCurve hA hB a b _ _ trivial),
    toW_shamirSpec hA hB a b _ .infinity trivial, show toW Point.infinity trivial = 0 from rfl,
    nsmul_zero, zero_add, Nat.mod_eq_of_lt (lt_two_pow_max a b),
    Nat.mod_eq_of_lt (max_comm a.log2 b.log2 ▸ lt_two_pow_max b a)]

/-! ## Verification -/

theorem toW_injective {A B : Point} {hA : A.OnCurve} {hB : B.OnCurve}
    (h : toW A hA = toW B hB) : A = B := by
  cases A with
  | infinity => cases B with
    | infinity => rfl
    | affine _ _ => cases h
  | affine x1 y1 => cases B with
    | infinity => cases h
    | affine x2 y2 =>
      simp only [toW, WeierstrassCurve.Affine.Point.some.injEq] at h
      rw [e.injective h.1, e.injective h.2]

/-- **What `verifyHash` checks.** It returns `true` exactly when `r, s ∈ [1, n-1]`,
`s ≤ n/2` if `requireLowS`, and, with `w = s⁻¹`, `u₁ = e·w`, `u₂ = r·w` modulo
`n`, the point `u₁ • G + u₂ • Q` is an affine point whose `x`-coordinate is
`r` modulo `n`. -/
theorem verifyHash_eq_true_iff (pk : ECDSA.PublicKey) (h : ByteArray) (sig : ECDSA.Signature)
    (requireLowS : Bool) :
    pk.verifyHash h sig requireLowS = true ↔
      (0 < sig.r ∧ sig.r < n ∧ 0 < sig.s ∧ sig.s < n) ∧
      (requireLowS = true → sig.isLowS = true) ∧
      ∃ (x y : Fp) (hxy : (Point.affine x y).OnCurve),
        (Fn.ofNat (ECDSA.hashToScalar h) * Fn.inv (Fn.ofNat sig.s)).val • toW G G_onCurve +
          (Fn.ofNat sig.r * Fn.inv (Fn.ofNat sig.s)).val • toW pk.point pk.onCurve =
          toW (.affine x y) hxy ∧
        x.val % n = sig.r := by
  obtain ⟨r, s⟩ := sig
  unfold ECDSA.PublicKey.verifyHash
  dsimp only
  generalize (Fn.ofNat (ECDSA.hashToScalar h) * Fn.inv (Fn.ofNat s)).val = u₁
  generalize (Fn.ofNat r * Fn.inv (Fn.ofNat s)).val = u₂
  have hon := smulAdd_onCurve G_onCurve pk.onCurve u₁ u₂
  have hW := toW_smulAdd G_onCurve pk.onCurve u₁ u₂ hon
  generalize Point.smulAdd u₁ G u₂ pk.point = R at hon hW
  have hlowiff : (requireLowS && !(ECDSA.Signature.isLowS ⟨r, s⟩)) = true ↔
      ¬(requireLowS = true → ECDSA.Signature.isLowS ⟨r, s⟩ = true) := by
    cases requireLowS <;> cases ECDSA.Signature.isLowS ⟨r, s⟩ <;> simp
  cases R with
  | infinity =>
    have hne : ∀ (x y : Fp) (hxy : (Point.affine x y).OnCurve),
        u₁ • toW G G_onCurve + u₂ • toW pk.point pk.onCurve ≠ toW (.affine x y) hxy := by
      intro x y hxy hE
      cases toW_injective (hW.trans hE)
    split_ifs <;>
      exact iff_of_false (by simp) (fun ⟨_, _, x, y, hxy, hE, _⟩ => hne x y hxy hE)
  | affine x0 y0 =>
    split_ifs with h1 h2
    · exact iff_of_false (by simp) (fun ⟨_, hl, _⟩ => hlowiff.1 h2 hl)
    · simp only [beq_iff_eq]
      constructor
      · intro hv
        exact ⟨h1, not_not.1 (mt hlowiff.2 h2), x0, y0, hon, hW.symm, hv⟩
      · rintro ⟨-, -, x, y, hxy, hE, hx⟩
        cases toW_injective (hW.trans hE)
        exact hx
    · exact iff_of_false (by simp) (fun ⟨hr, _⟩ => h1 hr)

/-! ## Signatures from `sign` pass `verify` -/

/-- **Signatures produced by `PrivateKey.signHash` pass `PublicKey.verifyHash`**
for the signer's public key, also with `requireLowS` when signing used `lowS`. -/
theorem verifyHash_signHash {sk : ECDSA.PrivateKey} {h : ByteArray} {lowS : Bool}
    {extra : ByteArray} {verifyAfterSign : Bool} {sig : ECDSA.Signature}
    (hs : sk.signHash h lowS extra verifyAfterSign = some sig) {requireLowS : Bool}
    (hreq : requireLowS = true → lowS = true) :
    sk.publicKey.verifyHash h sig requireLowS = true := by
  have ⟨hr0, hrn, hs0, hsn, heq⟩ := signHash_verifies hs
  obtain ⟨k, rsig, hk, hw, rfl⟩ := ECDSA.PrivateKey.signHash_spec hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hlow⟩ := ECDSA.signWithNonce_spec hk hw
  refine (verifyHash_eq_true_iff _ _ _ _).2 ⟨⟨hr0, hrn, hs0, hsn⟩, ?_, heq⟩
  intro hr
  simp only [ECDSA.Signature.isLowS, decide_eq_true_eq]
  exact hlow (hreq hr)

/-- **Every signature produced by `PrivateKey.sign` passes `PublicKey.verify`**
for the signer's public key, also with `requireLowS` when signing used `lowS`
(the default for both). -/
theorem verify_sign {sk : ECDSA.PrivateKey} {msg : ByteArray} {lowS : Bool}
    {extra : ByteArray} {verifyAfterSign : Bool} {sig : ECDSA.Signature}
    (hs : sk.sign msg lowS extra verifyAfterSign = some sig) {requireLowS : Bool}
    (hreq : requireLowS = true → lowS = true) :
    sk.publicKey.verify msg sig requireLowS = true :=
  verifyHash_signHash hs hreq

end Secp256k1Proofs
