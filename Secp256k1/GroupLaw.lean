import Secp256k1.Curve
import Secp256k1.Certificates

/-!
# The group law and the complete addition formulas

This file proves that the complete projective formulas of Renes, Costello and
Batina (EUROCRYPT 2016, Algorithms 7 and 9 for `y² = x³ + b`), used by the
constant-time code, implement the elliptic curve group law of secp256k1.

* `Point.addSpec` is the textbook chord-and-tangent law on affine points
  (the same case split and slopes as Mathlib's `WeierstrassCurve.Affine`).
* `Point.ProjRep P X Y Z` says that `(X : Y : Z)` represents `P`.
* `rcbAdd_correct` and `rcbDouble_correct`: for points on the curve and any
  projective representatives, the formulas return a representative of
  `addSpec P Q` (resp. `addSpec P P`). In particular the output is never the
  invalid triple `(0, 0, 0)`.

The case analysis uses three facts about `𝔽ₚ`, all derived from the primality
of `p` (`Secp256k1.Certificates`):

* `𝔽ₚ` is a field (`Fp.mul_inv_cancel`, `Fp.mul_eq_zero`);
* `-7` is not a cube, so no point has `y = 0` (no 2-torsion);
* `3` is not a square, which rules out points of order 4.

Polynomial identities modulo the curve equation are proved by `grind`, whose
ring solver works in `Fin p`.
-/

namespace Secp256k1

theorem IsPrime.dvd_mul {q x y : Nat} (hq : IsPrime q) (h : q ∣ x * y) : q ∣ x ∨ q ∣ y := by
  rcases hq.2 (Nat.gcd q x) (Nat.gcd_dvd_left q x) with h1 | h1
  · exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left h1 h)
  · exact Or.inl (h1 ▸ Nat.gcd_dvd_right q x)

namespace Fp

theorem val_one : (1 : Fp).val = 1 := by decide

theorem val_inv (a : Fp) : (Fp.inv a).val = a.val ^ (p - 2) % p := by
  show (Fin.ofNat p (powMod a.val (p - 2) p)).val = _
  rw [Fin.val_ofNat, powMod_eq _ _ _ p_pos, Nat.mod_mod]

/-- `𝔽ₚ` is a field: every non-zero element has an inverse. -/
theorem mul_inv_cancel {a : Fp} (h : a ≠ 0) : a * Fp.inv a = 1 := by
  apply Fin.ext
  have hp := p_isPrime.1
  have ha : 0 < a.val := Nat.pos_of_ne_zero (fun h0 => h (Fin.ext h0))
  rw [Fin.val_mul, val_inv, Nat.mul_mod_mod, ← Nat.pow_succ',
    show (p - 2).succ = p - 1 by omega, fermat_p _ ha a.isLt, val_one]

/-- `𝔽ₚ` has no zero divisors. -/
theorem mul_eq_zero {a b : Fp} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have hv : a.val * b.val % p = 0 := by
    have := congrArg Fin.val h; rwa [Fin.val_mul] at this
  rcases p_isPrime.dvd_mul (Nat.dvd_of_mod_eq_zero hv) with h1 | h1
  · exact Or.inl (Fin.ext (Nat.eq_zero_of_dvd_of_lt h1 a.isLt))
  · exact Or.inr (Fin.ext (Nat.eq_zero_of_dvd_of_lt h1 b.isLt))

theorem mul_ne_zero {a b : Fp} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := fun h =>
  (mul_eq_zero h).elim ha hb

/-- From `(w + c) % p = 0` with `w, c < p`, `c > 0`: `w = p - c`. -/
private theorem eq_sub_of_add_mod {w c : Nat} (hw : w < p) (hc0 : 0 < c) (hc : c < p)
    (h : (w + c) % p = 0) : w = p - c := by
  by_cases hlt : w + c < p
  · rw [Nat.mod_eq_of_lt hlt] at h; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h; omega

theorem neg_seven_not_cube : powMod (p - 7) ((p - 1) / 3) p ≠ 1 := by decide +kernel

theorem three_not_square : powMod 3 ((p - 1) / 2) p ≠ 1 := by decide +kernel

/-- `-7` is not a cube in `𝔽ₚ`: no point of secp256k1 has `y = 0`. -/
theorem cube_add_seven_ne_zero (u : Fp) : u * u * u + 7 ≠ 0 := by
  intro h
  have hv : (u.val * u.val * u.val % p + 7) % p = 0 := by
    have := congrArg Fin.val h
    simp only [Fin.val_add, Fin.val_mul, Nat.mod_mul_mod] at this
    rwa [show (7 : Fp).val = 7 by decide] at this
  have hw := eq_sub_of_add_mod (Nat.mod_lt _ p_pos) (by decide) (by decide) hv
  have hu : 0 < u.val := by
    apply Nat.pos_of_ne_zero; intro h0; rw [h0] at hw
    exact absurd hw (by decide)
  apply neg_seven_not_cube
  have h3 : 3 * ((p - 1) / 3) = p - 1 := by decide
  rw [powMod_eq _ _ _ p_pos, ← hw, ← Nat.pow_mod, show u.val * u.val * u.val = u.val ^ 3 by
    rw [Nat.pow_succ, Nat.pow_two], ← Nat.pow_mul, h3, fermat_p _ hu u.isLt]

/-- `3` is not a square in `𝔽ₚ`. -/
theorem mul_self_ne_three (s : Fp) : s * s ≠ 3 := by
  intro h
  have hv : s.val * s.val % p = 3 := by
    have := congrArg Fin.val h; rwa [Fin.val_mul, show (3 : Fp).val = 3 by decide] at this
  have hs : 0 < s.val := by
    apply Nat.pos_of_ne_zero; intro h0; rw [h0] at hv; exact absurd hv (by decide)
  apply three_not_square
  have h2 : 2 * ((p - 1) / 2) = p - 1 := by decide
  rw [powMod_eq _ _ _ p_pos, ← hv, ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul, h2,
    fermat_p _ hs s.isLt]

end Fp


namespace Point

/-- The elliptic curve group law on affine points (chord and tangent). -/
def addSpec : Point → Point → Point
  | .infinity, Q => Q
  | P, .infinity => P
  | .affine x1 y1, .affine x2 y2 =>
    if x1 = x2 then
      if y1 + y2 = 0 then .infinity
      else
        let l := 3 * x1 * x1 * Fp.inv (2 * y1)
        let x3 := l * l - x1 - x2
        .affine x3 (l * (x1 - x3) - y1)
    else
      let l := (y2 - y1) * Fp.inv (x2 - x1)
      let x3 := l * l - x1 - x2
      .affine x3 (l * (x1 - x3) - y1)

/-- The curve equation as a proposition. -/
def OnCurve : Point → Prop
  | .infinity => True
  | .affine x y => y * y = x * x * x + 7

/-- `(X : Y : Z)` represents `P` in homogeneous projective coordinates. -/
def ProjRep : Point → Fp → Fp → Fp → Prop
  | .infinity, X, Y, Z => X = 0 ∧ Z = 0 ∧ Y ≠ 0
  | .affine x y, X, Y, Z => Z ≠ 0 ∧ X = x * Z ∧ Y = y * Z

/-- The normalised representative `(0 : 1 : 0)` or `(x : y : 1)`. -/
def normal : Point → Fp × Fp × Fp
  | .infinity => (0, 1, 0)
  | .affine x y => (x, y, 1)

theorem ProjRep.exists_normal {P : Point} {X Y Z : Fp} (h : P.ProjRep X Y Z) :
    ∃ c, c ≠ 0 ∧ X = c * P.normal.1 ∧ Y = c * P.normal.2.1 ∧ Z = c * P.normal.2.2 := by
  cases P with
  | infinity =>
    obtain ⟨hX, hZ, hY⟩ := h
    exact ⟨Y, hY, by simp only [normal]; grind, by simp only [normal]; grind,
      by simp only [normal]; grind⟩
  | affine x y =>
    obtain ⟨hZ, hX, hY⟩ := h
    exact ⟨Z, hZ, by simp only [normal]; grind, by simp only [normal]; grind,
      by simp only [normal]; grind⟩

theorem ProjRep.smul {P : Point} {X Y Z : Fp} (h : P.ProjRep X Y Z) {c : Fp} (hc : c ≠ 0) :
    P.ProjRep (c * X) (c * Y) (c * Z) := by
  cases P with
  | infinity => obtain ⟨hX, hZ, hY⟩ := h; exact ⟨by grind, by grind, Fp.mul_ne_zero hc hY⟩
  | affine x y => obtain ⟨hZ, hX, hY⟩ := h; exact ⟨Fp.mul_ne_zero hc hZ, by grind, by grind⟩

theorem y_ne_zero {x y : Fp} (h : y * y = x * x * x + 7) : y ≠ 0 := by
  intro hy; apply Fp.cube_add_seven_ne_zero x; rw [← h, hy]; decide

end Point

/-- RCB16 Algorithm 7 over 𝔽ₚ (`b₃ = 21`), as in `CT.PPoint.add`. -/
def rcbAdd (X1 Y1 Z1 X2 Y2 Z2 : Fp) : Fp × Fp × Fp :=
  let b3 : Fp := 21
  let t0 := X1 * X2
  let t1 := Y1 * Y2
  let t2 := Z1 * Z2
  let t3 := X1 + Y1
  let t4 := X2 + Y2
  let t3 := t3 * t4
  let t4 := t0 + t1
  let t3 := t3 - t4
  let t4 := Y1 + Z1
  let X3 := Y2 + Z2
  let t4 := t4 * X3
  let X3 := t1 + t2
  let t4 := t4 - X3
  let X3 := X1 + Z1
  let Y3 := X2 + Z2
  let X3 := X3 * Y3
  let Y3 := t0 + t2
  let Y3 := X3 - Y3
  let X3 := t0 + t0
  let t0 := X3 + t0
  let t2 := b3 * t2
  let Z3 := t1 + t2
  let t1 := t1 - t2
  let Y3 := b3 * Y3
  let X3 := t4 * Y3
  let t2 := t3 * t1
  let X3 := t2 - X3
  let Y3 := Y3 * t0
  let t1 := t1 * Z3
  let Y3 := t1 + Y3
  let t0 := t0 * t3
  let Z3 := Z3 * t4
  let Z3 := Z3 + t0
  (X3, Y3, Z3)

set_option maxHeartbeats 4000000 in
theorem rcbAdd_homog (c e X1 Y1 Z1 X2 Y2 Z2 : Fp) :
    rcbAdd (c * X1) (c * Y1) (c * Z1) (e * X2) (e * Y2) (e * Z2) =
      let r := rcbAdd X1 Y1 Z1 X2 Y2 Z2
      (c * c * e * e * r.1, c * c * e * e * r.2.1, c * c * e * e * r.2.2) := by
  simp only [rcbAdd, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

set_option maxHeartbeats 4000000 in
/-- Generic case: if all three outputs vanish then `(u³ + 7)·d⁶ = 0`. -/
theorem rcbAdd_degenerate (x1 y1 x2 y2 : Fp) (h1 : y1 * y1 = x1 * x1 * x1 + 7)
    (h2 : y2 * y2 = x2 * x2 * x2 + 7)
    (hX : (rcbAdd x1 y1 1 x2 y2 1).1 = 0) (hY : (rcbAdd x1 y1 1 x2 y2 1).2.1 = 0)
    (hZ : (rcbAdd x1 y1 1 x2 y2 1).2.2 = 0) :
    let d := x1 - x2
    let U := (y1 + y2) * (y1 + y2) - (x1 + x2) * (d * d)
    U * U * U + 7 * (d * d * d * d * d * d) = 0 := by
  simp only [rcbAdd] at hX hY hZ ⊢
  grind

/-- RCB16 Algorithm 9 over 𝔽ₚ (`b₃ = 21`), as in `CT.PPoint.double`. -/
def rcbDouble (X Y Z : Fp) : Fp × Fp × Fp :=
  let b3 : Fp := 21
  let t0 := Y * Y
  let Z3 := t0 + t0
  let Z3 := Z3 + Z3
  let Z3 := Z3 + Z3
  let t1 := Y * Z
  let t2 := Z * Z
  let t2 := b3 * t2
  let X3 := t2 * Z3
  let Y3 := t0 + t2
  let Z3 := t1 * Z3
  let t1 := t2 + t2
  let t2 := t1 + t2
  let t0 := t0 - t2
  let Y3 := t0 * Y3
  let Y3 := X3 + Y3
  let t1 := X * Y
  let X3 := t0 * t1
  let X3 := X3 + X3
  (X3, Y3, Z3)

set_option maxHeartbeats 4000000 in
theorem rcbDouble_homog (c X Y Z : Fp) :
    rcbDouble (c * X) (c * Y) (c * Z) =
      let r := rcbDouble X Y Z
      (c * c * c * c * r.1, c * c * c * c * r.2.1, c * c * c * c * r.2.2) := by
  simp only [rcbDouble, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

theorem two_ne_zero : (2 : Fp) ≠ 0 := by decide
theorem eight_ne_zero : (8 : Fp) ≠ 0 := by decide
theorem fortytwo_mul_inv : (42 : Fp) * Fp.inv 42 = 1 := Fp.mul_inv_cancel (by decide)

set_option maxHeartbeats 4000000 in
/-- The output of the addition formulas on normalised affine inputs, in terms of
`d = x₂ - x₁` and `L = y₂ - y₁`. -/
theorem rcbAdd_affine_identities (x1 y1 x2 y2 : Fp) (h1 : y1 * y1 = x1 * x1 * x1 + 7)
    (h2 : y2 * y2 = x2 * x2 * x2 + 7) :
    let r := rcbAdd x1 y1 1 x2 y2 1
    let d := x2 - x1
    let L := y2 - y1
    r.1 * (d * d) = r.2.2 * (L * L - (x1 + x2) * (d * d)) ∧
    r.2.1 * (d * d * d) =
      r.2.2 * (L * (x1 * (d * d) - (L * L - (x1 + x2) * (d * d))) - y1 * (d * d * d)) := by
  simp only [rcbAdd]
  constructor <;> grind

theorem sub_mul_inv_neg {a b di : Fp} (h : (b - a) * di = 1) : (a - b) * di = -1 := by grind

theorem cube_scale (U e di : Fp) (he : e * di = -1) :
    U * di * di * (U * di * di) * (U * di * di) + 7 =
      di * di * di * di * di * di * (U * U * U + 7 * (e * e * e * e * e * e)) := by grind

theorem mul_zero' (a : Fp) : a * 0 = 0 := by grind

/-- Recover the affine `x`-coordinate from the identity for `X₃`. -/
theorem generic_x {x1 x2 y1 y2 di X3 Z3 : Fp} (hdi : (x2 - x1) * di = 1)
    (I1 : X3 * ((x2 - x1) * (x2 - x1)) =
      Z3 * ((y2 - y1) * (y2 - y1) - (x1 + x2) * ((x2 - x1) * (x2 - x1)))) :
    X3 = ((y2 - y1) * di * ((y2 - y1) * di) - x1 - x2) * Z3 := by grind

/-- Recover the affine `y`-coordinate from the identity for `Y₃`. -/
theorem generic_y {x1 x2 y1 y2 di Y3 Z3 : Fp} (hdi : (x2 - x1) * di = 1)
    (I2 : Y3 * ((x2 - x1) * (x2 - x1) * (x2 - x1)) =
      Z3 * ((y2 - y1) * (x1 * ((x2 - x1) * (x2 - x1)) -
        ((y2 - y1) * (y2 - y1) - (x1 + x2) * ((x2 - x1) * (x2 - x1)))) -
          y1 * ((x2 - x1) * (x2 - x1) * (x2 - x1)))) :
    Y3 = ((y2 - y1) * di * (x1 - ((y2 - y1) * di * ((y2 - y1) * di) - x1 - x2)) - y1) * Z3 := by
  grind

/-- Generic addition `x₁ ≠ x₂`. -/
theorem rcbAdd_generic (x1 y1 x2 y2 : Fp) (h1 : y1 * y1 = x1 * x1 * x1 + 7)
    (h2 : y2 * y2 = x2 * x2 * x2 + 7) (hx : x1 ≠ x2) :
    (Point.addSpec (.affine x1 y1) (.affine x2 y2)).ProjRep
      (rcbAdd x1 y1 1 x2 y2 1).1 (rcbAdd x1 y1 1 x2 y2 1).2.1 (rcbAdd x1 y1 1 x2 y2 1).2.2 := by
  have hdeg := rcbAdd_degenerate x1 y1 x2 y2 h1 h2
  have ⟨I1, I2⟩ := rcbAdd_affine_identities x1 y1 x2 y2 h1 h2
  simp only [Point.addSpec, hx, ↓reduceIte, Point.ProjRep]
  have hd : x2 - x1 ≠ 0 := by intro h; apply hx; grind
  have hdi := Fp.mul_inv_cancel hd
  generalize Fp.inv (x2 - x1) = di at hdi ⊢
  generalize rcbAdd x1 y1 1 x2 y2 1 = r at *
  obtain ⟨X3, Y3, Z3⟩ := r
  simp only at hdeg I1 I2 ⊢
  have hZ : Z3 ≠ 0 := by
    intro hZ
    have hX : X3 = 0 := by
      rcases Fp.mul_eq_zero (show X3 * ((x2 - x1) * (x2 - x1)) = 0 by grind) with h | h
      · exact h
      · exact absurd h (Fp.mul_ne_zero hd hd)
    have hY : Y3 = 0 := by
      rcases Fp.mul_eq_zero (show Y3 * ((x2 - x1) * (x2 - x1) * (x2 - x1)) = 0 by grind) with h | h
      · exact h
      · exact absurd h (Fp.mul_ne_zero (Fp.mul_ne_zero hd hd) hd)
    have hW := hdeg hX hY hZ
    have he := sub_mul_inv_neg hdi
    generalize (y1 + y2) * (y1 + y2) - (x1 + x2) * ((x1 - x2) * (x1 - x2)) = U at hW
    generalize x1 - x2 = e at hW he
    apply Fp.cube_add_seven_ne_zero (U * di * di)
    rw [cube_scale U e di he, hW]
    exact mul_zero' _
  exact ⟨hZ, generic_x hdi I1, generic_y hdi I2⟩

/-! ### `x₁ = x₂`: inverse points and doubling -/

theorem sq_sub_ne_zero (t : Fp) : t * t - 5292 ≠ 0 := by
  intro h
  apply Fp.mul_self_ne_three (t * Fp.inv 42)
  have h42 := fortytwo_mul_inv
  generalize Fp.inv 42 = i at h42
  grind

set_option maxHeartbeats 4000000 in
/-- `P + (-P)`: the formulas return `(0 : Y : 0)` with `Y = (x³ + 70)² - 5292`. -/
theorem rcbAdd_neg_identities (x1 y1 : Fp) (h1 : y1 * y1 = x1 * x1 * x1 + 7) :
    (rcbAdd x1 y1 1 x1 (-y1) 1).1 = 0 ∧ (rcbAdd x1 y1 1 x1 (-y1) 1).2.2 = 0 ∧
    (rcbAdd x1 y1 1 x1 (-y1) 1).2.1 =
      (x1 * x1 * x1 + 70) * (x1 * x1 * x1 + 70) - 5292 := by
  simp only [rcbAdd]
  refine ⟨?_, ?_, ?_⟩ <;> grind

theorem rcbAdd_neg (x1 y1 : Fp) (h1 : y1 * y1 = x1 * x1 * x1 + 7) :
    Point.ProjRep .infinity (rcbAdd x1 y1 1 x1 (-y1) 1).1 (rcbAdd x1 y1 1 x1 (-y1) 1).2.1
      (rcbAdd x1 y1 1 x1 (-y1) 1).2.2 := by
  obtain ⟨hX, hZ, hY⟩ := rcbAdd_neg_identities x1 y1 h1
  exact ⟨hX, hZ, hY ▸ sq_sub_ne_zero _⟩

/-- The doubling slope and result, given `e = 2y` with inverse `ei`. -/
def doubleX (x ei : Fp) : Fp := 3 * x * x * ei * (3 * x * x * ei) - x - x

def doubleY (x y ei : Fp) : Fp := 3 * x * x * ei * (x - doubleX x ei) - y

set_option maxHeartbeats 4000000 in
theorem rcbAdd_double_identities (x y ei : Fp) (h : y * y = x * x * x + 7)
    (hei : 2 * y * ei = 1) :
    (rcbAdd x y 1 x y 1).2.2 = 8 * (y * y * y) ∧
    (rcbAdd x y 1 x y 1).1 = doubleX x ei * (rcbAdd x y 1 x y 1).2.2 ∧
    (rcbAdd x y 1 x y 1).2.1 = doubleY x y ei * (rcbAdd x y 1 x y 1).2.2 := by
  simp only [rcbAdd, doubleY, doubleX]
  refine ⟨?_, ?_, ?_⟩ <;> grind

set_option maxHeartbeats 4000000 in
theorem rcbDouble_identities (x y ei : Fp) (h : y * y = x * x * x + 7) (hei : 2 * y * ei = 1) :
    (rcbDouble x y 1).2.2 = 8 * (y * y * y) ∧
    (rcbDouble x y 1).1 = doubleX x ei * (rcbDouble x y 1).2.2 ∧
    (rcbDouble x y 1).2.1 = doubleY x y ei * (rcbDouble x y 1).2.2 := by
  simp only [rcbDouble, doubleY, doubleX]
  refine ⟨?_, ?_, ?_⟩ <;> grind

theorem two_y_ne_zero {x y : Fp} (h : y * y = x * x * x + 7) : 2 * y ≠ 0 :=
  Fp.mul_ne_zero two_ne_zero (Point.y_ne_zero h)

theorem y_add_y_ne_zero {x y : Fp} (h : y * y = x * x * x + 7) : y + y ≠ 0 := by
  have := two_y_ne_zero h; intro h'; apply this; grind

theorem eight_y_cube_ne_zero {x y : Fp} (h : y * y = x * x * x + 7) : 8 * (y * y * y) ≠ 0 := by
  have hy := Point.y_ne_zero h
  exact Fp.mul_ne_zero eight_ne_zero (Fp.mul_ne_zero (Fp.mul_ne_zero hy hy) hy)

/-- `addSpec P P` for an affine point on the curve is the tangent rule. -/
theorem addSpec_self (x y : Fp) (h : y * y = x * x * x + 7) :
    Point.addSpec (.affine x y) (.affine x y) =
      .affine (doubleX x (Fp.inv (2 * y))) (doubleY x y (Fp.inv (2 * y))) := by
  simp only [Point.addSpec, ↓reduceIte, y_add_y_ne_zero h, doubleX, doubleY]

theorem double_projRep {x y X3 Y3 Z3 : Fp} (h : y * y = x * x * x + 7)
    (hZ : Z3 = 8 * (y * y * y)) (hX : X3 = doubleX x (Fp.inv (2 * y)) * Z3)
    (hY : Y3 = doubleY x y (Fp.inv (2 * y)) * Z3) :
    (Point.addSpec (.affine x y) (.affine x y)).ProjRep X3 Y3 Z3 := by
  rw [addSpec_self x y h]
  exact ⟨hZ ▸ eight_y_cube_ne_zero h, hX, hY⟩

theorem rcbAdd_self (x y : Fp) (h : y * y = x * x * x + 7) :
    (Point.addSpec (.affine x y) (.affine x y)).ProjRep
      (rcbAdd x y 1 x y 1).1 (rcbAdd x y 1 x y 1).2.1 (rcbAdd x y 1 x y 1).2.2 := by
  obtain ⟨hZ, hX, hY⟩ :=
    rcbAdd_double_identities x y _ h (Fp.mul_inv_cancel (two_y_ne_zero h))
  exact double_projRep h hZ hX hY

theorem rcbDouble_affine (x y : Fp) (h : y * y = x * x * x + 7) :
    (Point.addSpec (.affine x y) (.affine x y)).ProjRep
      (rcbDouble x y 1).1 (rcbDouble x y 1).2.1 (rcbDouble x y 1).2.2 := by
  obtain ⟨hZ, hX, hY⟩ :=
    rcbDouble_identities x y _ h (Fp.mul_inv_cancel (two_y_ne_zero h))
  exact double_projRep h hZ hX hY

/-! ### The point at infinity -/

set_option maxHeartbeats 4000000 in
theorem rcbAdd_inf_left (x y : Fp) (h : y * y = x * x * x + 7) :
    (rcbAdd 0 1 0 x y 1).2.2 = y ∧ (rcbAdd 0 1 0 x y 1).1 = x * y ∧
    (rcbAdd 0 1 0 x y 1).2.1 = y * y := by
  simp only [rcbAdd]
  refine ⟨?_, ?_, ?_⟩ <;> grind

set_option maxHeartbeats 4000000 in
theorem rcbAdd_inf_right (x y : Fp) (h : y * y = x * x * x + 7) :
    (rcbAdd x y 1 0 1 0).2.2 = y ∧ (rcbAdd x y 1 0 1 0).1 = x * y ∧
    (rcbAdd x y 1 0 1 0).2.1 = y * y := by
  simp only [rcbAdd]
  refine ⟨?_, ?_, ?_⟩ <;> grind

theorem rcbAdd_inf_inf : rcbAdd 0 1 0 0 1 0 = (0, 1, 0) := by decide

theorem rcbDouble_inf : rcbDouble 0 1 0 = (0, 1, 0) := by decide

theorem affine_projRep_self {x y : Fp} (h : y * y = x * x * x + 7) {X3 Y3 Z3 : Fp}
    (hZ : Z3 = y) (hX : X3 = x * y) (hY : Y3 = y * y) : (Point.affine x y).ProjRep X3 Y3 Z3 :=
  ⟨hZ ▸ Point.y_ne_zero h, by rw [hX, hZ], by rw [hY, hZ]⟩

/-! ### Correctness for all inputs -/

theorem rcbAdd_normal (P Q : Point) (hP : P.OnCurve) (hQ : Q.OnCurve) :
    (Point.addSpec P Q).ProjRep
      (rcbAdd P.normal.1 P.normal.2.1 P.normal.2.2 Q.normal.1 Q.normal.2.1 Q.normal.2.2).1
      (rcbAdd P.normal.1 P.normal.2.1 P.normal.2.2 Q.normal.1 Q.normal.2.1 Q.normal.2.2).2.1
      (rcbAdd P.normal.1 P.normal.2.1 P.normal.2.2 Q.normal.1 Q.normal.2.1 Q.normal.2.2).2.2 := by
  cases P with
  | infinity =>
    cases Q with
    | infinity =>
      simp only [Point.normal, rcbAdd_inf_inf, Point.addSpec]; exact ⟨rfl, rfl, by decide⟩
    | affine x y =>
      obtain ⟨hZ, hX, hY⟩ := rcbAdd_inf_left x y hQ
      simp only [Point.normal, Point.addSpec]
      exact affine_projRep_self hQ hZ hX hY
  | affine x1 y1 =>
    cases Q with
    | infinity =>
      obtain ⟨hZ, hX, hY⟩ := rcbAdd_inf_right x1 y1 hP
      simp only [Point.normal, Point.addSpec]
      exact affine_projRep_self hP hZ hX hY
    | affine x2 y2 =>
      have h1 : y1 * y1 = x1 * x1 * x1 + 7 := hP
      have h2 : y2 * y2 = x2 * x2 * x2 + 7 := hQ
      simp only [Point.normal]
      by_cases hx : x1 = x2
      · subst hx
        by_cases hy : y1 + y2 = 0
        · have hy2 : y2 = -y1 := by grind
          subst hy2
          simp only [Point.addSpec, hy, ↓reduceIte]
          exact rcbAdd_neg x1 y1 h1
        · have hprod : (y2 - y1) * (y2 + y1) = 0 := by grind
          rcases Fp.mul_eq_zero hprod with h | h
          · have hy2 : y2 = y1 := by grind
            subst hy2
            exact rcbAdd_self x1 y2 h1
          · exact absurd (by grind) hy
      · exact rcbAdd_generic x1 y1 x2 y2 h1 h2 hx

/-- **The complete addition formulas implement the group law**: for points `P`, `Q`
on the curve and any projective representatives, `rcbAdd` returns a
representative of `P + Q`. -/
theorem rcbAdd_correct {P Q : Point} (hP : P.OnCurve) (hQ : Q.OnCurve) {X1 Y1 Z1 X2 Y2 Z2 : Fp}
    (h1 : P.ProjRep X1 Y1 Z1) (h2 : Q.ProjRep X2 Y2 Z2) :
    (Point.addSpec P Q).ProjRep (rcbAdd X1 Y1 Z1 X2 Y2 Z2).1 (rcbAdd X1 Y1 Z1 X2 Y2 Z2).2.1
      (rcbAdd X1 Y1 Z1 X2 Y2 Z2).2.2 := by
  obtain ⟨c, hc, rfl, rfl, rfl⟩ := h1.exists_normal
  obtain ⟨e, he, rfl, rfl, rfl⟩ := h2.exists_normal
  rw [rcbAdd_homog]
  exact (rcbAdd_normal P Q hP hQ).smul
    (Fp.mul_ne_zero (Fp.mul_ne_zero (Fp.mul_ne_zero hc hc) he) he)

/-- **The complete doubling formulas implement the group law**: `rcbDouble`
returns a representative of `P + P`. -/
theorem rcbDouble_correct {P : Point} (hP : P.OnCurve) {X Y Z : Fp} (h : P.ProjRep X Y Z) :
    (Point.addSpec P P).ProjRep (rcbDouble X Y Z).1 (rcbDouble X Y Z).2.1 (rcbDouble X Y Z).2.2 := by
  obtain ⟨c, hc, rfl, rfl, rfl⟩ := h.exists_normal
  rw [rcbDouble_homog]
  apply Point.ProjRep.smul _ (Fp.mul_ne_zero (Fp.mul_ne_zero (Fp.mul_ne_zero hc hc) hc) hc)
  cases P with
  | infinity => simp only [Point.normal, rcbDouble_inf, Point.addSpec]; exact ⟨rfl, rfl, by decide⟩
  | affine x y => exact rcbDouble_affine x y hP

/-! ### Closure -/

theorem generic_onCurve {x1 y1 x2 y2 di : Fp} (h1 : y1 * y1 = x1 * x1 * x1 + 7)
    (h2 : y2 * y2 = x2 * x2 * x2 + 7) (hdi : (x2 - x1) * di = 1) :
    ((y2 - y1) * di * (x1 - ((y2 - y1) * di * ((y2 - y1) * di) - x1 - x2)) - y1) *
      ((y2 - y1) * di * (x1 - ((y2 - y1) * di * ((y2 - y1) * di) - x1 - x2)) - y1) =
    ((y2 - y1) * di * ((y2 - y1) * di) - x1 - x2) *
      ((y2 - y1) * di * ((y2 - y1) * di) - x1 - x2) *
      ((y2 - y1) * di * ((y2 - y1) * di) - x1 - x2) + 7 := by grind

theorem double_onCurve {x y ei : Fp} (h : y * y = x * x * x + 7) (hei : 2 * y * ei = 1) :
    doubleY x y ei * doubleY x y ei = doubleX x ei * doubleX x ei * doubleX x ei + 7 := by
  simp only [doubleX, doubleY]; grind

/-- The sum of two points on the curve is on the curve. -/
theorem addSpec_onCurve {P Q : Point} (hP : P.OnCurve) (hQ : Q.OnCurve) :
    (Point.addSpec P Q).OnCurve := by
  cases P with
  | infinity => exact hQ
  | affine x1 y1 =>
    cases Q with
    | infinity => exact hP
    | affine x2 y2 =>
      have h1 : y1 * y1 = x1 * x1 * x1 + 7 := hP
      have h2 : y2 * y2 = x2 * x2 * x2 + 7 := hQ
      by_cases hx : x1 = x2
      · subst hx
        by_cases hy : y1 + y2 = 0
        · simp only [Point.addSpec, hy, ↓reduceIte]; trivial
        · have hprod : (y2 - y1) * (y2 + y1) = 0 := by grind
          rcases Fp.mul_eq_zero hprod with h | h
          · have hy2 : y2 = y1 := by grind
            subst hy2
            rw [addSpec_self x1 y2 h1]
            exact double_onCurve h1 (Fp.mul_inv_cancel (two_y_ne_zero h1))
          · exact absurd (by grind) hy
      · simp only [Point.addSpec, hx, ↓reduceIte]
        have hd : x2 - x1 ≠ 0 := by intro h; apply hx; grind
        exact generic_onCurve h1 h2 (Fp.mul_inv_cancel hd)

end Secp256k1
