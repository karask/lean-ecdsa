import Secp256k1.CT.PointProofs
import Secp256k1.ECDSA

/-!
# The constant-time scalar multiplication

Proves that the constant-time table construction, table lookup and windowed
loop of `CT.PPoint` compute the expected combination of group operations:

* `Point.mulSpec A i`: `i • A` by repeated addition (`(i + 1) • A = i • A + A`).
* `Point.windowSpec A digit w acc`: the windowed algorithm on points
  (`acc ↦ 16·acc + (digit w) • A`, with `16·acc` as four doublings).
* `PPoint.lookup_eq`: the constant-time lookup returns `T[idx]`.
* `PPoint.table_correct`: `table P` holds representatives of `0 • A, …, 15 • A`.
* `PPoint.smulTable_correct`, `PPoint.smulG_correct`, `PPoint.smulGBlind_correct`: the constant-time
  scalar multiplication represents `windowSpec` applied to the base-16 digits
  of the scalar (`Scalar.nibble_toNat`).

That `windowSpec` equals `k • A` uses associativity of the group law, and is
proved with Mathlib in the separate `proofs/` package.
-/

namespace Secp256k1

namespace Point

/-- `i • A` by repeated addition. -/
def mulSpec (A : Point) : Nat → Point
  | 0 => .infinity
  | i + 1 => addSpec (A.mulSpec i) A

/-- `2 • X` as `X + X`. -/
def dbl (X : Point) : Point := addSpec X X

/-- The windowed scalar multiplication on points: for each window from the
most significant, `acc ↦ 16·acc + (digit w) • A`. -/
def windowSpec (A : Point) (digit : Nat → Nat) : Nat → Point → Point
  | 0, acc => acc
  | w + 1, acc => windowSpec A digit w (addSpec (dbl (dbl (dbl (dbl acc)))) (A.mulSpec (digit w)))

theorem mulSpec_onCurve {A : Point} (hA : A.OnCurve) : ∀ i, (A.mulSpec i).OnCurve
  | 0 => trivial
  | i + 1 => addSpec_onCurve (mulSpec_onCurve hA i) hA

theorem dbl_onCurve {X : Point} (h : X.OnCurve) : X.dbl.OnCurve := addSpec_onCurve h h

end Point

theorem G_onCurve : G.OnCurve := by
  have h := G_isValid
  simp only [G, Point.isValid, Point.isOnCurve, beq_iff_eq] at h
  exact h

namespace CT

/-! ## Base-16 digits of a scalar -/

theorem U256.limb_toNat (a : U256) (ha : a.Valid) (q : Nat) (hq : q < 8) :
    (a.limb q).toNat = a.toNat / 2 ^ (32 * q) % 2 ^ 32 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ha
  have : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [U256.limb, U256.toNat] <;> omega

theorem nibble_of_word (K r : Nat) (hr : r < 8) :
    K / 2 ^ (4 * r) % 16 = K % 2 ^ 32 / 2 ^ (4 * r) % 16 := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- **The windows of the scalar multiplication are the base-16 digits of `k`.** -/
theorem Scalar.nibble_toNat (k : Scalar) (hk : k.val.Valid) (w : Nat) (hw : w < 64) :
    (k.nibble w).toNat = k.toNat / 16 ^ w % 16 := by
  have hq : w / 8 < 8 := by omega
  have hr : w % 8 < 8 := Nat.mod_lt _ (by decide)
  have hshift : (4 * (w % 8)).toUInt64.toNat % 64 = 4 * (w % 8) := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  simp only [Scalar.nibble, UInt64.toNat_and, UInt64.toNat_shiftRight, hshift,
    Nat.shiftRight_eq_div_pow]
  have : (0xF : UInt64).toNat = 2 ^ 4 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod, U256.limb_toNat _ hk _ hq,
    ← nibble_of_word _ _ hr, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have hw' : 32 * (w / 8) + 4 * (w % 8) = 4 * w := by omega
  rw [hw', Nat.pow_mul]
  rfl

theorem Scalar.nibble_lt (k : Scalar) (w : Nat) : (k.nibble w).toNat < 16 := by
  simp only [Scalar.nibble, UInt64.toNat_and]
  have : (0xF : UInt64).toNat = 2 ^ 4 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

/-! ## Base-16 digits of a 288-bit value (scalar blinding) -/

/-- Limbs below `2³²`. -/
def U288.Valid (t : U288) : Prop := t.low.Valid ∧ t.l8.toNat < 2 ^ 32

theorem U288.limb_toNat (t : U288) (ht : t.Valid) (q : Nat) (hq : q < 9) :
    (t.limb q).toNat = t.toNat / 2 ^ (32 * q) % 2 ^ 32 := by
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := ht
  simp only [U288.low] at h0 h1 h2 h3 h4 h5 h6 h7
  have : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [U288.limb, U288.toNat, U288.low, U256.toNat] <;> omega

theorem U288.nibble_toNat (t : U288) (ht : t.Valid) (w : Nat) (hw : w < 72) :
    (t.nibble w).toNat = t.toNat / 16 ^ w % 16 := by
  have hq : w / 8 < 9 := by omega
  have hr : w % 8 < 8 := Nat.mod_lt _ (by decide)
  have hshift : (4 * (w % 8)).toUInt64.toNat % 64 = 4 * (w % 8) := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  simp only [U288.nibble, UInt64.toNat_and, UInt64.toNat_shiftRight, hshift,
    Nat.shiftRight_eq_div_pow]
  have : (0xF : UInt64).toNat = 2 ^ 4 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod, U288.limb_toNat _ ht _ hq,
    ← nibble_of_word _ _ hr, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have hw' : 32 * (w / 8) + 4 * (w % 8) = 4 * w := by omega
  rw [hw', Nat.pow_mul]

theorem U288.nibble_lt (t : U288) (w : Nat) : (t.nibble w).toNat < 16 := by
  simp only [U288.nibble, UInt64.toNat_and]
  have : (0xF : UInt64).toNat = 2 ^ 4 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

/-- **The blinded scalar is `k + m·n`.** -/
theorem Scalar.blindedWide_spec (k : Scalar) (hk : k.val.Valid) {m : UInt64}
    (hm : m.toNat < 2 ^ 32) :
    (k.blindedWide m).Valid ∧ (k.blindedWide m).toNat = k.toNat + m.toNat * n := by
  have ⟨e, h8⟩ := U256.mulAddRow_toNat k.val m nMod.m hk hm nMod_valid.m_valid
  refine ⟨⟨mulAddRow_low_valid _ _ _, h8⟩, ?_⟩
  rw [Scalar.blindedWide, e, nMod_valid.m_eq]
  rfl

namespace PPoint

/-! ## Lookup -/

theorem lookup_go_eq (T : Array PPoint) (idx : UInt64) (hidx : idx.toNat < T.size)
    (hsize : T.size < 2 ^ 64) :
    ∀ (m j : Nat), T.size - j = m → ∀ acc : PPoint,
      (idx.toNat < j → acc = T[idx.toNat]) → lookup.go T idx j acc = T[idx.toNat] := by
  intro m
  induction m with
  | zero =>
    intro j hj acc hacc
    unfold lookup.go
    simp only [show ¬ j < T.size by omega, ↓reduceDIte]
    exact hacc (by omega)
  | succ m ih =>
    intro j hj acc hacc
    unfold lookup.go
    have hjs : j < T.size := by omega
    simp only [hjs, ↓reduceDIte]
    apply ih (j + 1) (by omega)
    intro hlt
    by_cases hje : j = idx.toNat
    · subst hje
      rw [eqMask_of_eq (by simp), select_one]
    · have hne : j.toUInt64 ≠ idx := by
        intro h; apply hje; rw [← h]; simp; omega
      rw [eqMask_of_ne hne, select_zero]
      exact hacc (by omega)

/-- **The constant-time lookup returns `T[idx]`.** -/
theorem lookup_eq (T : Array PPoint) (idx : UInt64) (h : idx.toNat < T.size)
    (hsize : T.size < 2 ^ 64) : lookup T idx = T[idx.toNat] :=
  lookup_go_eq T idx h hsize _ 0 rfl infinity (fun h => absurd h (by omega))

/-! ## Table -/

theorem table_go_correct {P : PPoint} {A : Point} (hA : A.OnCurve) (hP : P.Represents A) :
    ∀ (k : Nat) (acc : Array PPoint) (last : PPoint), 2 ≤ acc.size →
      (∀ i (h : i < acc.size), acc[i].Represents (A.mulSpec i)) →
      last.Represents (A.mulSpec (acc.size - 1)) →
      (table.go P k acc last).size = acc.size + k ∧
      ∀ i (h : i < (table.go P k acc last).size),
        (table.go P k acc last)[i].Represents (A.mulSpec i)
  | 0, acc, last, _, hacc, _ => ⟨rfl, hacc⟩
  | k + 1, acc, last, h2, hacc, hlast => by
    have hnext : (last.add P).Represents (A.mulSpec acc.size) := by
      have h := add_correct (Point.mulSpec_onCurve hA _) hA hlast hP
      have he : A.mulSpec acc.size = (A.mulSpec (acc.size - 1)).addSpec A := by
        rw [show acc.size = (acc.size - 1) + 1 by omega]; rfl
      rw [he]; exact h
    have hpush : ∀ i (h : i < (acc.push (last.add P)).size),
        (acc.push (last.add P))[i].Represents (A.mulSpec i) := by
      intro i hi
      rw [Array.getElem_push]
      split
      · exact hacc i _
      · have : i = acc.size := by simp at hi; omega
        subst this; exact hnext
    have hlast' : (last.add P).Represents (A.mulSpec ((acc.push (last.add P)).size - 1)) := by
      rw [Array.size_push, Nat.add_sub_cancel]; exact hnext
    obtain ⟨hs, hi⟩ := table_go_correct hA hP k (acc.push (last.add P)) (last.add P)
      (by rw [Array.size_push]; omega) hpush hlast'
    -- Unfold via `eq_def`: the generated equation lemma is very slow to build here.
    have hgo : table.go P (k + 1) acc last = table.go P k (acc.push (last.add P)) (last.add P) := by
      conv => lhs; rw [table.go.eq_def]
    rw [hgo]
    exact ⟨by rw [hs, Array.size_push]; omega, hi⟩

/-- **The table holds representatives of `0 • A, 1 • A, …, 15 • A`.** -/
theorem table_correct {P : PPoint} {A : Point} (hA : A.OnCurve) (hP : P.Represents A) :
    (table P).size = 16 ∧ ∀ i (h : i < (table P).size), (table P)[i].Represents (A.mulSpec i) := by
  have hinit : ∀ i (h : i < (#[infinity, P] : Array PPoint).size),
      (#[infinity, P] : Array PPoint)[i].Represents (A.mulSpec i) := by
    intro i hi
    have : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases this with rfl | rfl
    · exact infinity_represents
    · exact hP
  obtain ⟨hs, hi⟩ := table_go_correct hA hP 14 #[infinity, P] P (by simp) hinit hP
  have ht : table P = table.go P 14 #[infinity, P] P := by
    conv => lhs; rw [table.eq_def]
  rw [ht]
  exact ⟨by rw [hs]; rfl, hi⟩

/-! ## The windowed loop -/

theorem smulTable_go_correct {T : Array PPoint} {A : Point} (hA : A.OnCurve) (hT : T.size = 16)
    (hTi : ∀ i (h : i < T.size), T[i].Represents (A.mulSpec i)) (k : Scalar) :
    ∀ (w : Nat) (acc : PPoint) (B : Point), B.OnCurve → acc.Represents B →
      (smulTable.go T k w acc).Represents (A.windowSpec (fun w => (k.nibble w).toNat) w B)
  | 0, _, _, _, h => h
  | w + 1, acc, B, hB, h => by
    have hB1 := Point.dbl_onCurve hB
    have hB2 := Point.dbl_onCurve hB1
    have hB3 := Point.dbl_onCurve hB2
    have hB4 := Point.dbl_onCurve hB3
    have h4 := double_correct hB3 (double_correct hB2 (double_correct hB1 (double_correct hB h)))
    have hidx : (k.nibble w).toNat < T.size := hT ▸ Scalar.nibble_lt k w
    have hlk := lookup_eq T (k.nibble w) hidx (by rw [hT]; decide)
    have hadd := add_correct hB4 (Point.mulSpec_onCurve hA _) h4 (hTi _ hidx)
    have hgo : smulTable.go T k (w + 1) acc =
        smulTable.go T k w (acc.double.double.double.double.add (lookup T (k.nibble w))) := by
      conv => lhs; rw [smulTable.go.eq_def]
    rw [hgo, hlk]
    simp only [Point.windowSpec]
    exact smulTable_go_correct hA hT hTi k w _ _ (addSpec_onCurve hB4 (Point.mulSpec_onCurve hA _))
      hadd

theorem smulDigits_correct {T : Array PPoint} {A : Point} (hA : A.OnCurve) (hT : T.size = 16)
    (hTi : ∀ i (h : i < T.size), T[i].Represents (A.mulSpec i)) (digit : Nat → UInt64)
    (hd : ∀ w, (digit w).toNat < 16) :
    ∀ (w : Nat) (acc : PPoint) (B : Point), B.OnCurve → acc.Represents B →
      (smulDigits T digit w acc).Represents (A.windowSpec (fun w => (digit w).toNat) w B)
  | 0, _, _, _, h => h
  | w + 1, acc, B, hB, h => by
    have hB1 := Point.dbl_onCurve hB
    have hB2 := Point.dbl_onCurve hB1
    have hB3 := Point.dbl_onCurve hB2
    have hB4 := Point.dbl_onCurve hB3
    have h4 := double_correct hB3 (double_correct hB2 (double_correct hB1 (double_correct hB h)))
    have hidx : (digit w).toNat < T.size := hT ▸ hd w
    have hlk := lookup_eq T (digit w) hidx (by rw [hT]; decide)
    have hadd := add_correct hB4 (Point.mulSpec_onCurve hA _) h4 (hTi _ hidx)
    have hgo : smulDigits T digit (w + 1) acc =
        smulDigits T digit w (acc.double.double.double.double.add (lookup T (digit w))) := by
      conv => lhs; rw [smulDigits.eq_def]
    rw [hgo, hlk]
    simp only [Point.windowSpec]
    exact smulDigits_correct hA hT hTi digit hd w _ _
      (addSpec_onCurve hB4 (Point.mulSpec_onCurve hA _)) hadd

/-- **Constant-time `k • P` follows the windowed algorithm.** -/
theorem smul_correct {P : PPoint} {A : Point} (hA : A.OnCurve) (hP : P.Represents A) (k : Scalar) :
    (smul k P).Represents (A.windowSpec (fun w => (k.nibble w).toNat) 64 .infinity) := by
  obtain ⟨hs, hi⟩ := table_correct hA hP
  exact smulTable_go_correct hA hs hi k 64 infinity .infinity trivial infinity_represents

/-- **Constant-time `k • G` follows the windowed algorithm.** -/
theorem smulG_correct (k : Scalar) :
    (smulG k).Represents (G.windowSpec (fun w => (k.nibble w).toNat) 64 .infinity) :=
  smul_correct G_onCurve (ofPoint_represents G) k

end PPoint

/-! ## Conversion to affine coordinates -/

theorem U256.isZero_eq_one {a : U256} (ha : a.Valid) (h : a.toNat = 0) : a.isZero = 1 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ha
  have hz : ∀ x : UInt64, x.toNat = 0 → x = 0 := fun x hx => UInt64.toNat_inj.mp (by rw [hx]; rfl)
  simp only [U256.toNat] at h
  unfold U256.isZero
  rw [hz a.l0 (by omega), hz a.l1 (by omega), hz a.l2 (by omega), hz a.l3 (by omega),
    hz a.l4 (by omega), hz a.l5 (by omega), hz a.l6 (by omega), hz a.l7 (by omega)]
  decide

theorem U256.isZero_eq_zero {a : U256} (h : a.toNat ≠ 0) : a.isZero = 0 := by
  unfold U256.isZero
  apply isZeroBit_ne
  intro h0
  simp only [UInt64.or_eq_zero_iff] at h0
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h0
  apply h
  simp only [U256.toNat, h0, h1, h2, h3, h4, h5, h6, h7, UInt64.toNat_zero]

/-- A valid field element is zero exactly when its Montgomery form is. -/
theorem Fe.mont_toNat_eq_zero {a : Fe} (ha : a.Valid) : a.mont.toNat = 0 ↔ a.toNat = 0 := by
  have hM := pMod_valid
  have ⟨_, hlt, he⟩ := pMod.fromMont_spec hM a.mont ha.1
  have hval : pMod.value = p := rfl
  rw [hval] at hlt he
  constructor
  · intro h0
    rw [h0] at he
    apply mod_cancel (k := 2 ^ 256) (m := p) hM.coprime hlt (by decide)
    rw [Nat.mul_comm, show 2 ^ 256 * 0 % p = 0 % p from rfl]
    exact he
  · intro h0
    have : a.mont.toNat % p = 0 := by
      rw [← he]; show a.toNat * 2 ^ 256 % p = 0; rw [h0]; rfl
    rwa [Nat.mod_eq_of_lt ha.2] at this

theorem Fe.isZero_eq_one {a : Fe} {x : Fp} (ha : a.R x) (hx : x = 0) : a.isZero = 1 := by
  apply U256.isZero_eq_one ha.1.1
  rw [Fe.mont_toNat_eq_zero ha.1]
  have := congrArg Fin.val (ha.2.trans hx)
  rwa [Fe.toFp_val _ ha.1] at this

theorem Fe.isZero_eq_zero {a : Fe} {x : Fp} (ha : a.R x) (hx : x ≠ 0) : a.isZero = 0 := by
  apply U256.isZero_eq_zero
  rw [ne_eq, Fe.mont_toNat_eq_zero ha.1]
  intro h; apply hx; rw [← ha.2]; apply Fin.ext; rw [Fe.toFp_val _ ha.1, h]; rfl

theorem Fe.R.inv {a : Fe} {x : Fp} (ha : a.R x) : (Fe.inv a).R (Fp.inv x) := by
  have ⟨v, e⟩ := Fe.inv_spec a ha.1
  refine ⟨v, Fin.ext ?_⟩
  rw [Fe.toFp_val _ v, e, Fp.val_inv, ← ha.2, Fe.toFp_val _ ha.1]

namespace PPoint

/-- **Conversion to affine coordinates returns the represented point.** -/
theorem toPoint_eq {P : PPoint} {A : Point} (hP : P.Represents A) : P.toPoint = A := by
  obtain ⟨hx, hy, hz, hrep⟩ := hP
  have rX : P.X.R P.X.toFp := ⟨hx, rfl⟩
  have rY : P.Y.R P.Y.toFp := ⟨hy, rfl⟩
  have rZ : P.Z.R P.Z.toFp := ⟨hz, rfl⟩
  cases A with
  | infinity =>
    obtain ⟨_, hZ, _⟩ := hrep
    simp only [toPoint, toAffine, declassify, Fe.isZero_eq_one rZ hZ]
    rfl
  | affine x y =>
    obtain ⟨hZ, hX, hY⟩ := hrep
    simp only [toPoint, toAffine, declassify, Fe.isZero_eq_zero rZ hZ]
    have hzi := Fp.mul_inv_cancel hZ
    rw [(Fe.R.mul rX (Fe.R.inv rZ)).2, (Fe.R.mul rY (Fe.R.inv rZ)).2, hX, hY]
    congr 1 <;> grind

end PPoint

/-! ## Randomised projective coordinates -/

theorem Fe.ofBytes_valid (bs : ByteArray) : (Fe.ofBytes bs).Valid := by
  have ⟨v, e⟩ := pMod.toMont_spec pMod_valid _ (U256.ofBytes_valid bs)
  refine ⟨v, ?_⟩
  show (pMod.toMont (U256.ofBytes bs)).toNat < p
  rw [e]; exact Nat.mod_lt _ (by decide)

/-- Replacing `0` by `1` gives a non-zero field element. -/
theorem Fe.select_nonzero {z : Fe} (hz : z.Valid) :
    ∃ w, (Fe.select (maskOf z.isZero) Fe.one z).R w ∧ w ≠ 0 := by
  have rz : z.R z.toFp := ⟨hz, rfl⟩
  by_cases h0 : z.toFp = 0
  · rw [Fe.isZero_eq_one rz h0]
    refine ⟨1, ?_, by decide⟩
    show (⟨U256.select (maskOf 1) Fe.one.mont z.mont⟩ : Fe).R 1
    rw [U256.select_one]; exact Fe.one_R
  · rw [Fe.isZero_eq_zero rz h0]
    refine ⟨z.toFp, ?_, h0⟩
    show (⟨U256.select (maskOf 0) Fe.one.mont z.mont⟩ : Fe).R _
    rw [U256.select_zero]; exact rz

namespace PPoint

/-- Scaling the coordinates by a non-zero factor represents the same point. -/
theorem scale_represents {P : PPoint} {A : Point} (hP : P.Represents A) {z : Fe} {w : Fp}
    (hz : z.R w) (hw : w ≠ 0) : (scale z P).Represents A := by
  obtain ⟨hx, hy, hzv, hrep⟩ := hP
  have rX := Fe.R.mul hz ⟨hx, rfl⟩
  have rY := Fe.R.mul hz ⟨hy, rfl⟩
  have rZ := Fe.R.mul hz ⟨hzv, rfl⟩
  refine ⟨rX.1, rY.1, rZ.1, ?_⟩
  show A.ProjRep (z * P.X).toFp (z * P.Y).toFp (z * P.Z).toFp
  rw [rX.2, rY.2, rZ.2]
  exact hrep.smul hw

theorem blindInfinity_represents {z : Fe} {w : Fp} (hz : z.R w) (hw : w ≠ 0) :
    (⟨Fe.zero, z, Fe.zero⟩ : PPoint).Represents .infinity := by
  have h0 := Fe.zero_R
  refine ⟨h0.1, hz.1, h0.1, ?_⟩
  show Fe.zero.toFp = 0 ∧ Fe.zero.toFp = 0 ∧ z.toFp ≠ 0
  rw [h0.2, hz.2]; exact ⟨rfl, rfl, hw⟩

-- The 72-window specification unfolds a 72-step recursion.
set_option maxRecDepth 10000 in
/-- **Blinded `k • G` follows the windowed algorithm on the digits of `k + m·n`**,
for any coordinate blinding factor `z`. (That this is `k • G` uses `n • G = 𝒪`;
see `Secp256k1Proofs.toW_blindSpec`.) -/
theorem smulGBlind_correct (k : Scalar) {z : Fe} (hz : z.Valid) (m : UInt64) :
    (smulGBlind k z m).Represents
      (G.windowSpec (fun w => ((k.blindedWide m).nibble w).toNat) 72 .infinity) := by
  obtain ⟨w, hw, hw0⟩ := Fe.select_nonzero hz
  have hP := scale_represents (ofPoint_represents G) hw hw0
  obtain ⟨hs, hi⟩ := table_correct G_onCurve hP
  exact smulDigits_correct G_onCurve hs hi _ (U288.nibble_lt _) 72 _ .infinity trivial
    (blindInfinity_represents hw hw0)

end PPoint

end CT

end Secp256k1

namespace Secp256k1.ECDSA

/-- Whenever the computed point is a valid public key (i.e. not `𝒪`), `publicKey`
returns the point computed by the constant-time scalar multiplication. -/
theorem PrivateKey.publicKey_point (sk : PrivateKey)
    (h : (CT.PPoint.smulGBlind sk.scalar (CT.blindingFactor sk.scalar CT.keyBlindTag)
      (CT.blindingWord sk.scalar CT.keyWordTag)).toPoint.isValid = true) :
    sk.publicKey.point =
      (CT.PPoint.smulGBlind sk.scalar (CT.blindingFactor sk.scalar CT.keyBlindTag)
        (CT.blindingWord sk.scalar CT.keyWordTag)).toPoint :=
  PublicKey.ofPointD_point h

end Secp256k1.ECDSA
