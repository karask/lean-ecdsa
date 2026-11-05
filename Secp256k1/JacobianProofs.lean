import Secp256k1.CT.SmulProofs

/-!
# The Jacobian reference arithmetic

Verification and recovery use the variable-time Jacobian arithmetic of
`Secp256k1.Curve` (public data only). This file proves that it implements the
group law `Point.addSpec`:

* `Point.JacRep A P`: `P = (X : Y : Z)` represents `A` (`x = X/Z²`, `y = Y/Z³`).
* `Jacobian.double_correct`, `Jacobian.add_correct`: doubling and addition,
  including all the special cases (`𝒪`, `P + P`, `P + (-P)`).
* `Jacobian.toPoint_eq`: conversion to affine coordinates.
* `Point.smulAdd_eq`: Shamir's trick `Point.smulAdd a A b B` computes
  `Point.shamirSpec`, the double-and-add recursion on points. That this is
  `a • A + b • B` uses associativity, and is proved with Mathlib in `proofs/`.
-/

namespace Secp256k1

namespace Point

/-- `(X : Y : Z)` represents `A` in Jacobian coordinates: `𝒪` when `Z = 0`,
otherwise `(X/Z², Y/Z³)`. -/
def JacRep : Point → Jacobian → Prop
  | .infinity, P => P.Z = 0
  | .affine x y, P => P.Z ≠ 0 ∧ P.X = x * (P.Z * P.Z) ∧ P.Y = y * (P.Z * P.Z * P.Z)

/-- One step of Shamir's trick: `2·acc`, plus `A`, `B` or `AB = A + B`
according to the current bits of the two scalars. -/
def shamirStep (A B AB : Point) (ba bb : Bool) (acc : Point) : Point :=
  match ba, bb with
  | true, true => acc.dbl.addSpec AB
  | true, false => acc.dbl.addSpec A
  | false, true => acc.dbl.addSpec B
  | false, false => acc.dbl

/-- Shamir's double-and-add on points: for each bit from the most significant,
`acc ↦ 2·acc + aᵢ·A + bᵢ·B`. -/
def shamirSpec (A B AB : Point) (a b : Nat) : Nat → Point → Point
  | 0, acc => acc
  | i + 1, acc => shamirSpec A B AB a b i (shamirStep A B AB (a.testBit i) (b.testBit i) acc)

theorem shamirStep_onCurve {A B C : Point} (hA : A.OnCurve) (hB : B.OnCurve) (hC : C.OnCurve)
    (ba bb : Bool) : (shamirStep A B (A.addSpec B) ba bb C).OnCurve := by
  have hd := dbl_onCurve hC
  cases ba <;> cases bb
  · exact hd
  · exact addSpec_onCurve hd hB
  · exact addSpec_onCurve hd hA
  · exact addSpec_onCurve hd (addSpec_onCurve hA hB)

theorem shamirSpec_onCurve {A B : Point} (hA : A.OnCurve) (hB : B.OnCurve) (a b : Nat) :
    ∀ (i : Nat) (C : Point), C.OnCurve → (shamirSpec A B (A.addSpec B) a b i C).OnCurve
  | 0, _, hC => hC
  | i + 1, _, hC => shamirSpec_onCurve hA hB a b i _ (shamirStep_onCurve hA hB hC _ _)

end Point

namespace Jacobian

theorem ofPoint_rep (A : Point) : A.JacRep (ofPoint A) := by
  cases A with
  | infinity => rfl
  | affine x y =>
    show (1 : Fp) ≠ 0 ∧ x = x * (1 * 1) ∧ y = y * (1 * 1 * 1)
    exact ⟨by decide, by grind, by grind⟩

theorem infinity_rep : Point.infinity.JacRep infinity := rfl

/-- **Conversion to affine coordinates returns the represented point.** -/
theorem toPoint_eq {A : Point} {P : Jacobian} (h : A.JacRep P) : P.toPoint = A := by
  cases A with
  | infinity =>
    have hz : P.Z = 0 := h
    simp only [toPoint, isInfinity, hz, beq_self_eq_true, ↓reduceIte]
  | affine x y =>
    obtain ⟨hZ, hX, hY⟩ := h
    have hzi := Fp.mul_inv_cancel hZ
    simp only [toPoint, isInfinity, beq_iff_eq, hZ, ↓reduceIte, Point.affine.injEq]
    rw [hX, hY]
    constructor <;> grind

theorem z_pow_ne_zero {Z : Fp} (hZ : Z ≠ 0) : Z * Z * Z ≠ 0 :=
  Fp.mul_ne_zero (Fp.mul_ne_zero hZ hZ) hZ

set_option maxHeartbeats 1000000 in
/-- **Jacobian doubling implements the group law.** -/
theorem double_correct {A : Point} {P : Jacobian} (hA : A.OnCurve) (h : A.JacRep P) :
    (A.addSpec A).JacRep P.double := by
  cases A with
  | infinity =>
    have hz : P.Z = 0 := h
    simp only [double, isInfinity, hz, beq_self_eq_true, Bool.true_or, ↓reduceIte, Point.addSpec]
    rfl
  | affine x y =>
    obtain ⟨hZ, hX, hY⟩ := h
    have hon : y * y = x * x * x + 7 := hA
    have hy := Point.y_ne_zero hon
    have hYne : P.Y ≠ 0 := by rw [hY]; exact Fp.mul_ne_zero hy (z_pow_ne_zero hZ)
    have hei := Fp.mul_inv_cancel (two_y_ne_zero hon)
    rw [addSpec_self x y hon]
    simp only [double, isInfinity, beq_iff_eq, hZ, hYne, or_self, Bool.or_eq_true, ↓reduceIte]
    generalize Fp.inv (2 * y) = ei at hei
    refine ⟨?_, ?_, ?_⟩
    · exact Fp.mul_ne_zero (Fp.mul_ne_zero two_ne_zero hYne) hZ
    · simp only [doubleX]; rw [hX, hY]; grind
    · simp only [doubleY, doubleX]; rw [hX, hY]; grind

/-- Equal `x`-coordinates after scaling. -/
theorem scaled_eq_iff {a b c d : Fp} (hc : c ≠ 0) (hd : d ≠ 0) :
    a * c * d = b * d * c ↔ a = b := by
  constructor
  · intro h
    have : (a - b) * (c * d) = 0 := by grind
    rcases Fp.mul_eq_zero this with h0 | h0
    · grind
    · exact absurd h0 (Fp.mul_ne_zero hc hd)
  · intro h; subst h; grind

set_option maxHeartbeats 4000000 in
/-- **Jacobian addition implements the group law.** -/
theorem add_correct {A B : Point} {P Q : Jacobian} (hA : A.OnCurve) (hB : B.OnCurve)
    (hP : A.JacRep P) (hQ : B.JacRep Q) : (A.addSpec B).JacRep (P.add Q) := by
  cases A with
  | infinity =>
    have hz : P.Z = 0 := hP
    simp only [add, isInfinity, hz, beq_self_eq_true, ↓reduceIte, Point.addSpec]
    exact hQ
  | affine x1 y1 =>
    obtain ⟨hZ1, hX1, hY1⟩ := hP
    cases B with
    | infinity =>
      have hz : Q.Z = 0 := hQ
      simp only [add, isInfinity, beq_iff_eq, hZ1, hz, ↓reduceIte, Point.addSpec]
      exact ⟨hZ1, hX1, hY1⟩
    | affine x2 y2 =>
      obtain ⟨hZ2, hX2, hY2⟩ := hQ
      have h1 : y1 * y1 = x1 * x1 * x1 + 7 := hA
      have h2 : y2 * y2 = x2 * x2 * x2 + 7 := hB
      have hU : P.X * (Q.Z * Q.Z) = Q.X * (P.Z * P.Z) ↔ x1 = x2 := by
        rw [hX1, hX2]
        exact scaled_eq_iff (Fp.mul_ne_zero hZ1 hZ1) (Fp.mul_ne_zero hZ2 hZ2)
      have hS : P.Y * Q.Z * (Q.Z * Q.Z) = Q.Y * P.Z * (P.Z * P.Z) ↔ y1 = y2 := by
        rw [hY1, hY2]
        have e1 : y1 * (P.Z * P.Z * P.Z) * Q.Z * (Q.Z * Q.Z) =
            y1 * (P.Z * P.Z * P.Z) * (Q.Z * Q.Z * Q.Z) := by grind
        have e2 : y2 * (Q.Z * Q.Z * Q.Z) * P.Z * (P.Z * P.Z) =
            y2 * (Q.Z * Q.Z * Q.Z) * (P.Z * P.Z * P.Z) := by grind
        rw [e1, e2]
        exact scaled_eq_iff (z_pow_ne_zero hZ1) (z_pow_ne_zero hZ2)
      simp only [add, isInfinity, beq_iff_eq, hZ1, hZ2, ↓reduceIte]
      split
      · rename_i hu
        have hx := hU.1 hu
        subst hx
        split
        · rename_i hs
          have hy := hS.1 hs
          subst hy
          exact double_correct hA ⟨hZ1, hX1, hY1⟩
        · rename_i hs
          have hy : y1 ≠ y2 := fun h => hs (hS.2 h)
          have hsum : y1 + y2 = 0 := by
            have : (y1 - y2) * (y1 + y2) = 0 := by grind
            rcases Fp.mul_eq_zero this with h0 | h0
            · exact absurd (by grind) hy
            · exact h0
          simp only [Point.addSpec, ↓reduceIte, hsum]
          rfl
      · rename_i hu
        have hx : x1 ≠ x2 := fun h => hu (hU.2 h)
        have hd : x2 - x1 ≠ 0 := by intro h; apply hx; grind
        have hdi := Fp.mul_inv_cancel hd
        simp only [Point.addSpec, hx, ↓reduceIte]
        generalize Fp.inv (x2 - x1) = di at hdi
        refine ⟨?_, ?_, ?_⟩
        · refine Fp.mul_ne_zero (Fp.mul_ne_zero ?_ hZ1) hZ2
          intro h0; apply hd
          have : (x2 - x1) * (P.Z * P.Z * (Q.Z * Q.Z)) = 0 := by rw [hX1, hX2] at h0; grind
          rcases Fp.mul_eq_zero this with h | h
          · exact h
          · exact absurd h (Fp.mul_ne_zero (Fp.mul_ne_zero hZ1 hZ1) (Fp.mul_ne_zero hZ2 hZ2))
        · apply generic_x hdi
          rw [hX1, hX2, hY1, hY2]; grind
        · apply generic_y hdi
          rw [hX1, hX2, hY1, hY2]; grind

/-- **The Shamir loop computes `shamirSpec`.** -/
theorem smulAdd_go_rep {A B : Point} {P Q PQ : Jacobian} (hA : A.OnCurve) (hB : B.OnCurve)
    (hP : A.JacRep P) (hQ : B.JacRep Q) (hPQ : (A.addSpec B).JacRep PQ) (a b : Nat) :
    ∀ (i : Nat) (C : Point) (acc : Jacobian), C.OnCurve → C.JacRep acc →
      (Point.shamirSpec A B (A.addSpec B) a b i C).JacRep (smulAdd.go a P b Q PQ i acc)
  | 0, _, _, _, hacc => hacc
  | i + 1, C, acc, hC, hacc => by
    have hd : C.dbl.JacRep acc.double := double_correct hC hacc
    have hdC := Point.dbl_onCurve hC
    have hAB := addSpec_onCurve hA hB
    simp only [Point.shamirSpec, smulAdd.go]
    cases a.testBit i <;> cases b.testBit i
    · exact smulAdd_go_rep hA hB hP hQ hPQ a b i _ _ hdC hd
    · exact smulAdd_go_rep hA hB hP hQ hPQ a b i _ _ (addSpec_onCurve hdC hB)
        (add_correct hdC hB hd hQ)
    · exact smulAdd_go_rep hA hB hP hQ hPQ a b i _ _ (addSpec_onCurve hdC hA)
        (add_correct hdC hA hd hP)
    · exact smulAdd_go_rep hA hB hP hQ hPQ a b i _ _ (addSpec_onCurve hdC hAB)
        (add_correct hdC hAB hd hPQ)

theorem smulAdd_rep {A B : Point} (hA : A.OnCurve) (hB : B.OnCurve) (a b : Nat) :
    (Point.shamirSpec A B (A.addSpec B) a b (max a.log2 b.log2 + 1) .infinity).JacRep
      (smulAdd a (ofPoint A) b (ofPoint B)) :=
  smulAdd_go_rep hA hB (ofPoint_rep A) (ofPoint_rep B)
    (add_correct hA hB (ofPoint_rep A) (ofPoint_rep B)) a b _ _ _ trivial infinity_rep

end Jacobian

/-- **`Point.smulAdd` (used by verification) computes Shamir's double-and-add
on points.** -/
theorem Point.smulAdd_eq {A B : Point} (hA : A.OnCurve) (hB : B.OnCurve) (a b : Nat) :
    Point.smulAdd a A b B =
      Point.shamirSpec A B (A.addSpec B) a b (max a.log2 b.log2 + 1) .infinity :=
  Jacobian.toPoint_eq (Jacobian.smulAdd_rep hA hB a b)

end Secp256k1
