import Secp256k1.CT.SmulProofs

/-!
# The order of `G`

`n • G = 𝒪`, checked by the kernel.

The windowed algorithm `Point.windowSpec` with the base-16 digits of `n` is
evaluated in homogeneous projective coordinates with the complete formulas
`rcbAdd` / `rcbDouble` (no inversions), which are proved to represent the
group law (`rcbAdd_correct`, `rcbDouble_correct`). The kernel computes the
result's `Z` coordinate and finds `0`, hence the point is `𝒪`.

Combined with the primality of `n` and with associativity (proved with Mathlib
in the `proofs/` package), this shows that `G` has order exactly `n`, so
`d • G ≠ 𝒪` for every private key `d ∈ [1, n-1]`.
-/

namespace Secp256k1

/-- Homogeneous projective triples `(X : Y : Z)` over `𝔽ₚ`. -/
abbrev Proj := Fp × Fp × Fp

namespace Proj

/-- `P` represents the point `A`. -/
def Rep (A : Point) (P : Proj) : Prop := A.ProjRep P.1 P.2.1 P.2.2

def add (P Q : Proj) : Proj := rcbAdd P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2

def dbl (P : Proj) : Proj := rcbDouble P.1 P.2.1 P.2.2

/-- `(0 : 1 : 0)`, representing `𝒪`. -/
def zero : Proj := (0, 1, 0)

/-- Mirrors `Point.mulSpec`. -/
def mul (A : Proj) : Nat → Proj
  | 0 => zero
  | i + 1 => add (mul A i) A

/-- Mirrors `Point.windowSpec`. -/
def window (A : Proj) (digit : Nat → Nat) : Nat → Proj → Proj
  | 0, acc => acc
  | w + 1, acc => window A digit w (add (dbl (dbl (dbl (dbl acc)))) (mul A (digit w)))

theorem zero_rep : Rep .infinity zero := ⟨rfl, rfl, by decide⟩

theorem add_rep {A B : Point} {P Q : Proj} (hA : A.OnCurve) (hB : B.OnCurve)
    (hP : Rep A P) (hQ : Rep B Q) : Rep (A.addSpec B) (add P Q) :=
  rcbAdd_correct hA hB hP hQ

theorem dbl_rep {A : Point} {P : Proj} (hA : A.OnCurve) (hP : Rep A P) : Rep A.dbl (dbl P) :=
  rcbDouble_correct hA hP

theorem mul_rep {A : Point} {P : Proj} (hA : A.OnCurve) (hP : Rep A P) :
    ∀ i, Rep (A.mulSpec i) (mul P i)
  | 0 => zero_rep
  | i + 1 => add_rep (Point.mulSpec_onCurve hA i) hA (mul_rep hA hP i) hP

theorem window_rep {A : Point} {P : Proj} (hA : A.OnCurve) (hP : Rep A P) (digit : Nat → Nat) :
    ∀ (w : Nat) (B : Point) (Q : Proj), B.OnCurve → Rep B Q →
      Rep (A.windowSpec digit w B) (window P digit w Q)
  | 0, _, _, _, hQ => hQ
  | w + 1, B, Q, hB, hQ => by
    have h1 := Point.dbl_onCurve hB
    have h2 := Point.dbl_onCurve h1
    have h3 := Point.dbl_onCurve h2
    have h4 := Point.dbl_onCurve h3
    exact window_rep hA hP digit w _ _ (addSpec_onCurve h4 (Point.mulSpec_onCurve hA _))
      (add_rep h4 (Point.mulSpec_onCurve hA _)
        (dbl_rep h3 (dbl_rep h2 (dbl_rep h1 (dbl_rep hB hQ)))) (mul_rep hA hP _))

/-- A representative with `Z = 0` represents `𝒪`. -/
theorem Rep.eq_infinity {A : Point} {P : Proj} (h : Rep A P) (hZ : P.2.2 = 0) :
    A = .infinity := by
  cases A with
  | infinity => rfl
  | affine _ _ => exact absurd hZ h.1

/-- If the projective windowed algorithm ends with `Z = 0`, the windowed
algorithm on points returns `𝒪`. (Stated generically so that elaborating the
concrete instance does not unfold the computation.) -/
theorem window_eq_infinity {A : Point} {P : Proj} (hA : A.OnCurve) (hP : Rep A P)
    (digit : Nat → Nat) (w : Nat) (hZ : (window P digit w zero).2.2 = 0) :
    A.windowSpec digit w .infinity = .infinity :=
  (window_rep hA hP digit w .infinity zero trivial zero_rep).eq_infinity hZ

end Proj

/-- `G` in projective coordinates. -/
def Gproj : Proj := (Fp.ofNat Gx, Fp.ofNat Gy, 1)

theorem Gproj_rep : Proj.Rep G Gproj := ⟨by decide, by decide, by decide⟩

/-- The base-16 digits of `n`. -/
def nDigit (j : Nat) : Nat := n / 16 ^ j % 16

-- The 64 windows unfold to a deep term.
set_option maxRecDepth 100000 in
/-- The kernel evaluates `n • G` in projective coordinates and finds `Z = 0`. -/
theorem window_n_Z : (Proj.window Gproj nDigit 64 Proj.zero).2.2 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
/-- **`n • G = 𝒪`**, as the windowed algorithm on the digits of `n`. -/
theorem windowSpec_n : G.windowSpec nDigit 64 .infinity = .infinity :=
  Proj.window_eq_infinity G_onCurve Gproj_rep nDigit 64 window_n_Z

end Secp256k1
