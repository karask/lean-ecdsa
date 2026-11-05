import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod
import Secp256k1

/-!
# The group law of the library is Mathlib's elliptic curve group law

`Secp256k1.Point.addSpec` (the chord-and-tangent law used to specify the
constant-time code) is transported to Mathlib's
`WeierstrassCurve.Affine.Point` over `ZMod p`, whose `AddCommGroup` structure
is proved in Mathlib. This gives associativity and lets us identify the
windowed scalar multiplication with `k • G`.
-/

open Secp256k1

namespace Secp256k1Proofs

theorem nat_prime_p : Nat.Prime p := by
  rw [Nat.prime_def]; exact ⟨p_isPrime.1, p_isPrime.2⟩

instance : Fact (Nat.Prime p) := ⟨nat_prime_p⟩

/-- `𝔽ₚ` as `Fin p` (the library) and as `ZMod p` (Mathlib). -/
def e : Fp ≃+* ZMod p := ZMod.finEquiv p

theorem e_val (x : Fp) : (e x).val = x.val := rfl

theorem e_eq_natCast {x : Fp} {m : Nat} (hm : m < p) (hx : x.val = m) :
    e x = (m : ZMod p) := by
  apply ZMod.val_injective
  rw [e_val, hx, ZMod.val_natCast, Nat.mod_eq_of_lt hm]

theorem e_two : e 2 = 2 := by rw [e_eq_natCast (m := 2) (by decide) (by decide)]; norm_num
theorem e_three : e 3 = 3 := by rw [e_eq_natCast (m := 3) (by decide) (by decide)]; norm_num
theorem e_seven : e 7 = 7 := by rw [e_eq_natCast (m := 7) (by decide) (by decide)]; norm_num

theorem Fp.inv_zero' : Fp.inv 0 = 0 := by
  apply Fin.ext
  have h : 0 < p - 2 := by decide
  rw [Fp.val_inv, show (0 : Fp).val = 0 from rfl, Nat.zero_pow h, Nat.zero_mod]

theorem e_inv (a : Fp) : e (Fp.inv a) = (e a)⁻¹ := by
  by_cases h : a = 0
  · subst h; rw [Fp.inv_zero', map_zero]; simp
  · have := Fp.mul_inv_cancel h
    exact eq_inv_of_mul_eq_one_right (a := e a) (b := e (Fp.inv a))
      (by rw [← map_mul e, this, map_one])

theorem e_ne_zero {a : Fp} (h : a ≠ 0) : e a ≠ 0 := by
  intro h'; apply h; apply e.injective; rw [h', map_zero]

/-- secp256k1 as a Weierstrass curve over `ZMod p`: `y² = x³ + 7`. -/
def W : WeierstrassCurve.Affine (ZMod p) := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 7 }

@[simp] theorem W_a₁ : W.a₁ = 0 := rfl
@[simp] theorem W_a₂ : W.a₂ = 0 := rfl
@[simp] theorem W_a₃ : W.a₃ = 0 := rfl
@[simp] theorem W_a₄ : W.a₄ = 0 := rfl
@[simp] theorem W_a₆ : W.a₆ = 7 := rfl

theorem W_negY (x y : ZMod p) : W.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY]

theorem two_ne_zero' : (2 : ZMod p) ≠ 0 := by
  rw [← e_two]; exact e_ne_zero (by decide)

/-- Every point of the library's curve is a nonsingular point of `W`. -/
theorem nonsingular_of_onCurve {x y : Fp} (h : y * y = x * x * x + 7) :
    W.Nonsingular (e x) (e y) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff]
  have h' := congrArg e h
  simp only [map_mul, map_add, e_seven] at h'
  have hy : e y ≠ 0 := e_ne_zero (Point.y_ne_zero h)
  refine ⟨by simp only [W_a₁, W_a₂, W_a₃, W_a₄, W_a₆]; linear_combination h', Or.inr ?_⟩
  simp only [W_a₁, W_a₃, zero_mul, sub_zero]
  intro h2
  apply hy
  have : (2 : ZMod p) * e y = 0 := by linear_combination h2
  rcases mul_eq_zero.mp this with h3 | h3
  · exact absurd h3 two_ne_zero'
  · exact h3

/-- The library's points on the curve, as points of `W`. -/
noncomputable def toW : (A : Point) → A.OnCurve → W.Point
  | .infinity, _ => 0
  | .affine x y, h => .some (e x) (e y) (nonsingular_of_onCurve h)

@[simp] theorem toW_infinity (h : Point.infinity.OnCurve) : toW .infinity h = 0 := rfl

theorem toW_congr {A B : Point} (h : A = B) (hA : A.OnCurve) (hB : B.OnCurve) :
    toW A hA = toW B hB := by subst h; rfl

open WeierstrassCurve.Affine in
/-- **`addSpec` is Mathlib's elliptic curve addition.** -/
theorem toW_add (A B : Point) (hA : A.OnCurve) (hB : B.OnCurve) :
    toW (A.addSpec B) (addSpec_onCurve hA hB) = toW A hA + toW B hB := by
  cases A with
  | infinity =>
    rw [toW_congr (show Point.addSpec .infinity B = B from rfl) _ hB]
    simp [toW]
  | affine x1 y1 =>
    cases B with
    | infinity =>
      rw [toW_congr (show Point.addSpec (.affine x1 y1) .infinity = .affine x1 y1 from rfl) _ hA]
      simp [toW]
    | affine x2 y2 =>
      have h1 : y1 * y1 = x1 * x1 * x1 + 7 := hA
      have h2 : y2 * y2 = x2 * x2 * x2 + 7 := hB
      by_cases hx : x1 = x2
      · subst hx
        by_cases hy : y1 + y2 = 0
        · rw [toW_congr (show Point.addSpec (.affine x1 y1) (.affine x1 y2) = .infinity by
            simp [Point.addSpec, hy]) _ trivial]
          have hey : e y1 = W.negY (e x1) (e y2) := by
            rw [W_negY]; have := congrArg e hy; rw [map_add, map_zero] at this
            linear_combination this
          simp only [toW]
          rw [Point.add_of_Y_eq rfl hey]
        · obtain ⟨l, hl⟩ : ∃ l, l = 3 * x1 * x1 * Fp.inv (2 * y1) := ⟨_, rfl⟩
          have heq : Point.addSpec (.affine x1 y1) (.affine x1 y2) =
              .affine (l * l - x1 - x1) (l * (x1 - (l * l - x1 - x1)) - y1) := by
            subst hl; simp [Point.addSpec, hy]
          rw [toW_congr heq _ (heq ▸ addSpec_onCurve hA hB)]
          have hy' : e y1 ≠ W.negY (e x1) (e y2) := by
            rw [W_negY]; intro h; apply hy; apply e.injective
            rw [map_add, map_zero]; linear_combination h
          have hy1 : e y1 ≠ 0 := e_ne_zero (Point.y_ne_zero h1)
          have hslope : W.slope (e x1) (e x1) (e y1) (e y2) = e l := by
            rw [slope_of_Y_ne rfl hy', hl]
            simp only [map_mul, e_inv, e_three, e_two, W_negY, W_a₁, W_a₂, W_a₄]
            field_simp
            ring
          simp only [toW]
          rw [Point.add_some (fun h => hy' h.2), Point.some.injEq, hslope]
          constructor
          · simp only [addX, W_a₁, W_a₂, map_sub, map_mul]; ring
          · simp only [addY, negAddY, addX, W_negY, W_a₁, W_a₂, map_sub, map_mul]; ring
      · obtain ⟨l, hl⟩ : ∃ l, l = (y2 - y1) * Fp.inv (x2 - x1) := ⟨_, rfl⟩
        have heq : Point.addSpec (.affine x1 y1) (.affine x2 y2) =
            .affine (l * l - x1 - x2) (l * (x1 - (l * l - x1 - x2)) - y1) := by
          subst hl; simp [Point.addSpec, hx]
        rw [toW_congr heq _ (heq ▸ addSpec_onCurve hA hB)]
        have hex : e x1 ≠ e x2 := fun h => hx (e.injective h)
        have hd1 : e x1 - e x2 ≠ 0 := sub_ne_zero.mpr hex
        have hd2 : e x2 - e x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hex)
        have hslope : W.slope (e x1) (e x2) (e y1) (e y2) = e l := by
          rw [slope_of_X_ne hex, hl]
          simp only [map_mul, map_sub, e_inv]
          field_simp
          ring
        simp only [toW]
        rw [Point.add_some (fun h => hex h.1), Point.some.injEq, hslope]
        constructor
        · simp only [addX, W_a₁, W_a₂, map_sub, map_mul]; ring
        · simp only [addY, negAddY, addX, W_negY, W_a₁, W_a₂, map_sub, map_mul]; ring

/-! ## Scalar multiplication -/

theorem windowSpec_onCurve {A : Point} (hA : A.OnCurve) (digit : Nat → Nat) :
    ∀ (w : Nat) (B : Point), B.OnCurve → (A.windowSpec digit w B).OnCurve
  | 0, _, hB => hB
  | w + 1, _, hB =>
    windowSpec_onCurve hA digit w _
      (addSpec_onCurve (Point.dbl_onCurve (Point.dbl_onCurve (Point.dbl_onCurve
        (Point.dbl_onCurve hB)))) (Point.mulSpec_onCurve hA _))

/-- Repeated addition is `•`. -/
theorem toW_mulSpec {A : Point} (hA : A.OnCurve) :
    ∀ i, toW (A.mulSpec i) (Point.mulSpec_onCurve hA i) = i • toW A hA
  | 0 => by simp [Point.mulSpec, toW]
  | i + 1 => by
    show toW ((A.mulSpec i).addSpec A) (addSpec_onCurve (Point.mulSpec_onCurve hA i) hA) = _
    rw [toW_add _ _ (Point.mulSpec_onCurve hA i) hA, toW_mulSpec hA i, succ_nsmul]

theorem toW_dbl {X : Point} (hX : X.OnCurve) : toW X.dbl (Point.dbl_onCurve hX) = 2 • toW X hX := by
  show toW (X.addSpec X) (addSpec_onCurve hX hX) = _
  rw [toW_add, two_nsmul]

/-- The windowed algorithm evaluates `16ʷ • B + (∑ⱼ digitⱼ 16ʲ) • A`. -/
theorem toW_windowSpec {A : Point} (hA : A.OnCurve) (digit : Nat → Nat) :
    ∀ (w : Nat) (B : Point) (hB : B.OnCurve),
      toW (A.windowSpec digit w B) (windowSpec_onCurve hA digit w B hB) =
        16 ^ w • toW B hB + (∑ j ∈ Finset.range w, digit j * 16 ^ j) • toW A hA
  | 0, _, _ => by simp [Point.windowSpec]
  | w + 1, B, hB => by
    have h1 := Point.dbl_onCurve hB
    have h2 := Point.dbl_onCurve h1
    have h3 := Point.dbl_onCurve h2
    have h4 := Point.dbl_onCurve h3
    have hm := Point.mulSpec_onCurve hA (digit w)
    have hB' := addSpec_onCurve h4 hm
    show toW (A.windowSpec digit w ((B.dbl.dbl.dbl.dbl).addSpec (A.mulSpec (digit w))))
      (windowSpec_onCurve hA digit w _ hB') = _
    rw [toW_windowSpec hA digit w _ hB', toW_add _ _ h4 hm,
      toW_dbl h3, toW_dbl h2, toW_dbl h1, toW_dbl hB, toW_mulSpec hA, Finset.sum_range_succ]
    module

/-- The base-16 digits of `k` reassemble `k mod 16ⁿ`. -/
theorem sum_digits (k : Nat) : ∀ n, ∑ j ∈ Finset.range n, (k / 16 ^ j % 16) * 16 ^ j = k % 16 ^ n
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by rw [Finset.sum_range_succ, sum_digits k n, Nat.mod_pow_succ]; ring

set_option maxRecDepth 10000 in
theorem smulGSpec_onCurve (k : CT.Scalar) : (CT.smulGSpec k).OnCurve :=
  windowSpec_onCurve G_onCurve _ 64 .infinity trivial

-- Elaborating the 64-window specification unfolds a 64-step recursion.
set_option maxRecDepth 10000 in
/-- The windowed algorithm on the base-16 digits of `k` computes `k • G`. -/
theorem toW_smulGSpec (k : CT.Scalar) (hk : k.Valid) :
    toW (CT.smulGSpec k) (smulGSpec_onCurve k) = k.toNat • toW G G_onCurve := by
  show toW (G.windowSpec (fun w => (k.nibble w).toNat) 64 .infinity) _ = _
  rw [toW_windowSpec G_onCurve _ 64 .infinity trivial,
    show toW Point.infinity trivial = 0 from rfl, nsmul_zero, zero_add]
  have hsum : (∑ j ∈ Finset.range 64, (k.nibble j).toNat * 16 ^ j) = k.toNat := by
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [CT.Scalar.nibble_toNat k hk.1 j (Finset.mem_range.mp hj)]), sum_digits]
    apply Nat.mod_eq_of_lt
    have : n < 16 ^ 64 := by decide
    exact lt_trans hk.2 this
  rw [hsum]

set_option maxRecDepth 10000 in
/-- **The constant-time `k • G` computes `k • G`**: `CT.PPoint.smulG k`
represents the point corresponding to `k • G` in Mathlib's elliptic curve group. -/
theorem smulG_correct (k : CT.Scalar) (hk : k.Valid) :
    ∃ (A : Point) (hA : A.OnCurve), (CT.PPoint.smulG k).Represents A ∧
      toW A hA = k.toNat • toW G G_onCurve :=
  ⟨_, smulGSpec_onCurve k, CT.PPoint.smulG_correct k, toW_smulGSpec k hk⟩

set_option maxRecDepth 10000 in
/-- The blinded constant-time `k • G` (randomised projective coordinates) also
represents `k • G`, for any blinding factor. -/
theorem smulGBlind_correct (k : CT.Scalar) (hk : k.Valid) {z : CT.Fe} (hz : z.Valid) :
    ∃ (A : Point) (hA : A.OnCurve), (CT.PPoint.smulGBlind k z).Represents A ∧
      toW A hA = k.toNat • toW G G_onCurve :=
  ⟨_, smulGSpec_onCurve k, CT.PPoint.smulGBlind_correct k hz, toW_smulGSpec k hk⟩

end Secp256k1Proofs
