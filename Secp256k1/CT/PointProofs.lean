import Secp256k1.CT.Proofs
import Secp256k1.CT.Point
import Secp256k1.GroupLaw

/-!
# The constant-time point arithmetic implements the group law

Connects the constant-time projective formulas `CT.PPoint.add` and
`CT.PPoint.double` (on Montgomery-form limbs) with the formulas `rcbAdd` and
`rcbDouble` on `𝔽ₚ`, which `Secp256k1.GroupLaw` proves correct:

* `Fe.R a x`: `a` is a valid field element whose value is `x : 𝔽ₚ`;
  `Fe.R.add`, `Fe.R.sub`, `Fe.R.mul` show that the limb arithmetic computes
  the field operations (from the correctness theorems in `CT.Proofs`).
* `PPoint.Represents P A`: the coordinates of `P` are valid and form a
  projective representative of the curve point `A`.
* `PPoint.add_correct`, `PPoint.double_correct`: the constant-time formulas
  map representatives of `A` and `B` to a representative of `addSpec A B`.
* `PPoint.select_one` / `select_zero`, `PPoint.infinity_represents`,
  `PPoint.ofPoint_represents`: the remaining building blocks of the scalar
  multiplication.

Not covered here: that the windowed scalar multiplication computes `k • P`,
which additionally needs associativity of the group law.
-/

namespace Secp256k1.CT

/-! ## Field elements -/

theorem Fe.toNat_lt (a : Fe) (ha : a.Valid) : a.toNat < p :=
  (pMod.fromMont_spec pMod_valid a.mont ha.1).2.1

theorem Fe.toFp_val (a : Fe) (ha : a.Valid) : a.toFp.val = a.toNat := by
  show (Fin.ofNat p a.toNat).val = a.toNat
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt (a.toNat_lt ha)]

/-- `a` is a valid field element with value `x`. -/
def Fe.R (a : Fe) (x : Fp) : Prop := a.Valid ∧ a.toFp = x

theorem Fe.R.add {a b : Fe} {x y : Fp} (ha : a.R x) (hb : b.R y) : (a + b).R (x + y) := by
  have ⟨v, e⟩ := Fe.add_spec a b ha.1 hb.1
  refine ⟨v, Fin.ext ?_⟩
  rw [Fe.toFp_val _ v, e, Fin.val_add, ← ha.2, ← hb.2, Fe.toFp_val _ ha.1, Fe.toFp_val _ hb.1]

theorem Fe.R.sub {a b : Fe} {x y : Fp} (ha : a.R x) (hb : b.R y) : (a - b).R (x - y) := by
  have ⟨v, e⟩ := Fe.sub_spec a b ha.1 hb.1
  have hb' := b.toNat_lt hb.1
  refine ⟨v, Fin.ext ?_⟩
  rw [Fe.toFp_val _ v, e, Fin.val_sub, ← ha.2, ← hb.2, Fe.toFp_val _ ha.1, Fe.toFp_val _ hb.1,
    show a.toNat + p - b.toNat = p - b.toNat + a.toNat by omega]

theorem Fe.R.mul {a b : Fe} {x y : Fp} (ha : a.R x) (hb : b.R y) : (a * b).R (x * y) := by
  have ⟨v, e⟩ := Fe.mul_spec a b ha.1 hb.1
  refine ⟨v, Fin.ext ?_⟩
  rw [Fe.toFp_val _ v, e, Fin.val_mul, ← ha.2, ← hb.2, Fe.toFp_val _ ha.1, Fe.toFp_val _ hb.1]

theorem Fe.R.neg {a : Fe} {x : Fp} (ha : a.R x) : (-a).R (-x) := by
  have ⟨v, e⟩ := Fe.neg_spec a ha.1
  refine ⟨v, Fin.ext ?_⟩
  rw [Fe.toFp_val _ v, e, Fin.neg_def, ← ha.2]
  simp only [Fe.toFp_val _ ha.1]

theorem U256.ofNat_limb (x i : Nat) :
    ((x >>> (32 * i)) % 2 ^ 32).toUInt64.toNat = x / 2 ^ (32 * i) % 2 ^ 32 := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]; omega

/-- `U256.ofNat` splits a number into its eight 32-bit limbs. -/
theorem U256.ofNat_spec (x : Nat) :
    (U256.ofNat x).Valid ∧ (U256.ofNat x).toNat = x % 2 ^ 256 := by
  simp only [U256.Valid, U256.toNat, U256.ofNat, U256.ofNat_limb]
  omega

/-- Constants built with `Fe.ofNat` have the expected value. -/
theorem Fe.ofNat_R (v : Nat) (hv : v < p) : (Fe.ofNat v).R (Fp.ofNat v) := by
  have hM := pMod_valid
  have ⟨hu, hval⟩ := U256.ofNat_spec v
  have hp : p < 2 ^ 256 := by decide
  rw [Nat.mod_eq_of_lt (by omega)] at hval
  have hr := pMod.toMont_repr hM _ hu
  rw [hval] at hr
  have ⟨_, fe⟩ := pMod.fromMont_repr hM hr
  show Fe.R ⟨pMod.toMont (U256.ofNat (v % p))⟩ (Fp.ofNat v)
  rw [Nat.mod_eq_of_lt hv]
  refine ⟨⟨hr.1, hr.lt hM⟩, ?_⟩
  show Fp.ofNat (pMod.fromMont (pMod.toMont (U256.ofNat v))).toNat = Fp.ofNat v
  rw [fe, Nat.mod_eq_of_lt (show v < pMod.value from hv)]

theorem Fe.zero_R : Fe.zero.R 0 := by
  have hM := pMod_valid
  have hr : pMod.Repr U256.zero 0 := ⟨by simp [U256.zero, U256.Valid], by decide⟩
  have ⟨_, fe⟩ := pMod.fromMont_repr hM hr
  refine ⟨⟨hr.1, hr.lt hM⟩, ?_⟩
  show Fp.ofNat (pMod.fromMont U256.zero).toNat = 0
  rw [fe]; decide

theorem Fe.one_R : Fe.one.R 1 := by
  have hM := pMod_valid
  have hr := pMod.one_repr hM
  have ⟨_, fe⟩ := pMod.fromMont_repr hM hr
  refine ⟨⟨hr.1, hr.lt hM⟩, ?_⟩
  show Fp.ofNat (pMod.fromMont pMod.one).toNat = 1
  rw [fe]; decide

theorem Fp.ofNat_val (x : Fp) : Fp.ofNat x.val = x := by
  apply Fin.ext
  show (Fin.ofNat p x.val).val = x.val
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt x.isLt]

/-! ## Points -/

theorem PPoint.b3_R : PPoint.b3.R 21 := by
  have h := Fe.ofNat_R 21 (by decide)
  exact ⟨h.1, h.2.trans (by decide)⟩

/-- The coordinates of `PPoint.add` are given by the `rcbAdd` formulas. -/
theorem PPoint.add_R {P Q : PPoint} {X1 Y1 Z1 X2 Y2 Z2 : Fp}
    (hX1 : P.X.R X1) (hY1 : P.Y.R Y1) (hZ1 : P.Z.R Z1)
    (hX2 : Q.X.R X2) (hY2 : Q.Y.R Y2) (hZ2 : Q.Z.R Z2) :
    (P.add Q).X.R (rcbAdd X1 Y1 Z1 X2 Y2 Z2).1 ∧ (P.add Q).Y.R (rcbAdd X1 Y1 Z1 X2 Y2 Z2).2.1 ∧
      (P.add Q).Z.R (rcbAdd X1 Y1 Z1 X2 Y2 Z2).2.2 := by
  have hb3 := PPoint.b3_R
  dsimp only [PPoint.add, rcbAdd]
  refine ⟨?_, ?_, ?_⟩ <;>
    repeat (with_reducible first | assumption | apply Fe.R.add | apply Fe.R.sub | apply Fe.R.mul)

/-- The coordinates of `PPoint.double` are given by the `rcbDouble` formulas. -/
theorem PPoint.double_R {P : PPoint} {X Y Z : Fp} (hX : P.X.R X) (hY : P.Y.R Y) (hZ : P.Z.R Z) :
    P.double.X.R (rcbDouble X Y Z).1 ∧ P.double.Y.R (rcbDouble X Y Z).2.1 ∧
      P.double.Z.R (rcbDouble X Y Z).2.2 := by
  have hb3 := PPoint.b3_R
  dsimp only [PPoint.double, rcbDouble]
  refine ⟨?_, ?_, ?_⟩ <;>
    repeat (with_reducible first | assumption | apply Fe.R.add | apply Fe.R.sub | apply Fe.R.mul)

/-- `P` has valid coordinates forming a projective representative of `A`. -/
def PPoint.Represents (P : PPoint) (A : Point) : Prop :=
  P.X.Valid ∧ P.Y.Valid ∧ P.Z.Valid ∧ A.ProjRep P.X.toFp P.Y.toFp P.Z.toFp

/-- **Constant-time addition implements the group law.** -/
theorem PPoint.add_correct {P Q : PPoint} {A B : Point} (hA : A.OnCurve) (hB : B.OnCurve)
    (hP : P.Represents A) (hQ : Q.Represents B) : (P.add Q).Represents (A.addSpec B) := by
  obtain ⟨hx1, hy1, hz1, h1⟩ := hP
  obtain ⟨hx2, hy2, hz2, h2⟩ := hQ
  have ⟨rX, rY, rZ⟩ := PPoint.add_R ⟨hx1, rfl⟩ ⟨hy1, rfl⟩ ⟨hz1, rfl⟩ ⟨hx2, rfl⟩ ⟨hy2, rfl⟩
    ⟨hz2, rfl⟩
  refine ⟨rX.1, rY.1, rZ.1, ?_⟩
  rw [rX.2, rY.2, rZ.2]
  exact rcbAdd_correct hA hB h1 h2

/-- **Constant-time doubling implements the group law.** -/
theorem PPoint.double_correct {P : PPoint} {A : Point} (hA : A.OnCurve) (hP : P.Represents A) :
    P.double.Represents (A.addSpec A) := by
  obtain ⟨hx, hy, hz, h⟩ := hP
  have ⟨rX, rY, rZ⟩ := PPoint.double_R ⟨hx, rfl⟩ ⟨hy, rfl⟩ ⟨hz, rfl⟩
  refine ⟨rX.1, rY.1, rZ.1, ?_⟩
  rw [rX.2, rY.2, rZ.2]
  exact rcbDouble_correct hA h

theorem PPoint.infinity_represents : PPoint.infinity.Represents .infinity := by
  have h0 := Fe.zero_R
  have h1 := Fe.one_R
  refine ⟨h0.1, h1.1, h0.1, ?_⟩
  show Fe.zero.toFp = 0 ∧ Fe.zero.toFp = 0 ∧ Fe.one.toFp ≠ 0
  rw [h0.2, h1.2]
  exact ⟨rfl, rfl, by decide⟩

theorem PPoint.ofPoint_represents (A : Point) : (PPoint.ofPoint A).Represents A := by
  cases A with
  | infinity => exact PPoint.infinity_represents
  | affine x y =>
    have hx := Fe.ofNat_R x.val x.isLt
    have hy := Fe.ofNat_R y.val y.isLt
    have h1 := Fe.one_R
    refine ⟨hx.1, hy.1, h1.1, ?_⟩
    show (PPoint.ofPoint (.affine x y)).Z.toFp ≠ 0 ∧ _
    simp only [PPoint.ofPoint]
    rw [hx.2, hy.2, h1.2, Fp.ofNat_val, Fp.ofNat_val]
    exact ⟨by decide, by grind, by grind⟩

theorem Fe.select_one (a b : Fe) : Fe.select (maskOf 1) a b = a := by
  cases a; simp [Fe.select, U256.select_one]

theorem Fe.select_zero (a b : Fe) : Fe.select (maskOf 0) a b = b := by
  cases b; simp [Fe.select, U256.select_zero]

/-- The masked selection of points picks the first point for an all-ones mask. -/
theorem PPoint.select_one (P Q : PPoint) : PPoint.select (maskOf 1) P Q = P := by
  cases P; simp [PPoint.select, Fe.select_one]

/-- The masked selection of points picks the second point for a zero mask. -/
theorem PPoint.select_zero (P Q : PPoint) : PPoint.select (maskOf 0) P Q = Q := by
  cases Q; simp [PPoint.select, Fe.select_zero]

end Secp256k1.CT
