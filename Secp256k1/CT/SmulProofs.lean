import Secp256k1.CT.PointProofs

/-!
# The constant-time scalar multiplication

Proves that the constant-time table construction, table lookup and windowed
loop of `CT.PPoint` compute the expected combination of group operations:

* `Point.mulSpec A i`: `i • A` by repeated addition (`(i + 1) • A = i • A + A`).
* `Point.windowSpec A digit w acc`: the windowed algorithm on points
  (`acc ↦ 16·acc + (digit w) • A`, with `16·acc` as four doublings).
* `PPoint.lookup_eq`: the constant-time lookup returns `T[idx]`.
* `PPoint.table_correct`: `table P` holds representatives of `0 • A, …, 15 • A`.
* `PPoint.smulTable_correct`, `PPoint.smulG_correct`: the constant-time
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

namespace CT

/-! ## Masks, without `bv_decide` -/

theorem isZeroBit_zero : isZeroBit 0 = 1 := by decide

theorem isZeroBit_ne {x : UInt64} (hx : x ≠ 0) : isZeroBit x = 0 := by
  have hx' : x.toNat ≠ 0 := fun h => hx (UInt64.toNat_inj.mp (by rw [h]; rfl))
  have hlt := x.toNat_lt
  have hneg : (0 - x).toNat = 2 ^ 64 - x.toNat := by
    rw [UInt64.toNat_sub]; simp only [UInt64.toNat_zero, Nat.add_zero]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hor : ((x ||| (0 - x)) >>> 63).toNat = 1 := by
    rw [UInt64.toNat_shiftRight, UInt64.toNat_or, hneg]
    have h1 : x.toNat ≤ x.toNat ||| (2 ^ 64 - x.toNat) := Nat.left_le_or
    have h2 : 2 ^ 64 - x.toNat ≤ x.toNat ||| (2 ^ 64 - x.toNat) := Nat.right_le_or
    have h3 : x.toNat ||| (2 ^ 64 - x.toNat) < 2 ^ 64 := Nat.or_lt_two_pow hlt (by omega)
    simp only [show (63 : UInt64).toNat % 64 = 63 by decide, Nat.shiftRight_eq_div_pow]
    omega
  have : (x ||| (0 - x)) >>> 63 = 1 := UInt64.toNat_inj.mp (by rw [hor]; rfl)
  unfold isZeroBit; rw [this]; decide

/-- `eqMask` is all-ones exactly on equal inputs (kernel-checked version of
`eqMask_eq`). -/
theorem eqMask_of_eq {a b : UInt64} (h : a = b) : eqMask a b = maskOf 1 := by
  subst h; unfold eqMask; rw [UInt64.xor_self, isZeroBit_zero]

theorem eqMask_of_ne {a b : UInt64} (h : a ≠ b) : eqMask a b = maskOf 0 := by
  unfold eqMask; rw [isZeroBit_ne (fun h' => h (UInt64.xor_eq_zero_iff.mp h'))]

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

/-! ## The windowed loop -/

theorem Scalar.nibble_lt (k : Scalar) (w : Nat) : (k.nibble w).toNat < 16 := by
  simp only [Scalar.nibble, UInt64.toNat_and]
  have : (0xF : UInt64).toNat = 2 ^ 4 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

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

/-- **Constant-time `k • P` follows the windowed algorithm.** -/
theorem smul_correct {P : PPoint} {A : Point} (hA : A.OnCurve) (hP : P.Represents A) (k : Scalar) :
    (smul k P).Represents (A.windowSpec (fun w => (k.nibble w).toNat) 64 .infinity) := by
  obtain ⟨hs, hi⟩ := table_correct hA hP
  exact smulTable_go_correct hA hs hi k 64 infinity .infinity trivial infinity_represents

theorem G_onCurve : G.OnCurve := by
  have h := G_isValid
  simp only [G, Point.isValid, Point.isOnCurve, beq_iff_eq] at h
  exact h

/-- **Constant-time `k • G` follows the windowed algorithm.** -/
theorem smulG_correct (k : Scalar) :
    (smulG k).Represents (G.windowSpec (fun w => (k.nibble w).toNat) 64 .infinity) :=
  smul_correct G_onCurve (ofPoint_represents G) k

end PPoint

end CT

end Secp256k1
