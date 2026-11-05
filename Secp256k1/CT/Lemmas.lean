import Secp256k1.CT.U256

/-!
# Word-level lemmas for the constant-time arithmetic

Machine-checked facts about the 64-bit word tricks that `Secp256k1.CT`
relies on. The multi-limb arithmetic is proved correct in
`Secp256k1.CT.Proofs`.

All of them are proved from the `Nat` semantics of the word operations and use
only the standard axioms (no `bv_decide` or `native_decide`).
-/

namespace Secp256k1.CT

/-! ## Masks -/

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

/-- `eqMask` is all-ones on equal inputs. -/
theorem eqMask_of_eq {a b : UInt64} (h : a = b) : eqMask a b = maskOf 1 := by
  subst h; unfold eqMask; rw [UInt64.xor_self, isZeroBit_zero]

theorem eqMask_of_ne {a b : UInt64} (h : a ≠ b) : eqMask a b = maskOf 0 := by
  unfold eqMask; rw [isZeroBit_ne (fun h' => h (UInt64.xor_eq_zero_iff.mp h'))]

/-- `isZeroBit` is the indicator of `x = 0`. -/
theorem isZeroBit_eq (x : UInt64) : isZeroBit x = if x = 0 then 1 else 0 := by
  split
  · subst x; exact isZeroBit_zero
  · exact isZeroBit_ne ‹_›

/-- An all-ones mask selects the first argument. -/
theorem selectWord_maskOf_one (a b : UInt64) : selectWord (maskOf 1) a b = a := by
  apply UInt64.toNat_inj.mp
  have h1 : (maskOf 1).toNat = 2 ^ 64 - 1 := by decide
  have h2 : (~~~maskOf 1).toNat = 0 := by decide
  simp only [selectWord, UInt64.toNat_or, UInt64.toNat_and, h1, h2, Nat.and_zero, Nat.or_zero,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt a.toNat_lt]

/-- A zero mask selects the second argument. -/
theorem selectWord_maskOf_zero (a b : UInt64) : selectWord (maskOf 0) a b = b := by
  apply UInt64.toNat_inj.mp
  have h1 : (maskOf 0).toNat = 0 := by decide
  have h2 : (~~~maskOf 0).toNat = 2 ^ 64 - 1 := by decide
  simp only [selectWord, UInt64.toNat_or, UInt64.toNat_and, h1, h2, Nat.and_zero, Nat.zero_or,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt b.toNat_lt]

/-- `eqMask` is all-ones exactly on equal inputs. -/
theorem eqMask_eq (a b : UInt64) : eqMask a b = if a = b then maskOf 1 else maskOf 0 := by
  split
  · exact eqMask_of_eq ‹_›
  · exact eqMask_of_ne ‹_›

/-- The borrow extraction used by `U256.sub`: for 32-bit limbs and a borrow
bit, the top bit of the wrapped difference is the borrow out. -/
theorem borrow_eq (a b c : UInt64) (ha : a < 0x100000000) (hb : b < 0x100000000)
    (hc : c ≤ 1) : (a - b - c) >>> 63 = if a < b + c then 1 else 0 := by
  have ha' : a.toNat < 2 ^ 32 := UInt64.lt_iff_toNat_lt.1 ha
  have hb' : b.toNat < 2 ^ 32 := UInt64.lt_iff_toNat_lt.1 hb
  have hc' : c.toNat ≤ 1 := UInt64.le_iff_toNat_le.1 hc
  apply UInt64.toNat_inj.mp
  have hbc : (b + c).toNat = b.toNat + c.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  rw [UInt64.toNat_shiftRight, UInt64.toNat_sub, UInt64.toNat_sub,
    show (63 : UInt64).toNat % 64 = 63 by decide, Nat.shiftRight_eq_div_pow]
  split
  · rename_i h
    have h' : a.toNat < b.toNat + c.toNat := by rw [← hbc]; exact UInt64.lt_iff_toNat_lt.1 h
    show _ = 1
    omega
  · rename_i h
    have h' : b.toNat + c.toNat ≤ a.toNat := by
      rw [← hbc]; exact UInt64.le_iff_toNat_le.1 (UInt64.not_lt.1 h)
    show _ = 0
    omega

/-- A limb multiply-accumulate step `c + a·b + d` (as in `U256.mulAddRow`)
never overflows 64 bits when all inputs are 32-bit:
`(2³²-1)² + 2(2³²-1) = 2⁶⁴-1`. -/
theorem mac_toNat (a b c d : UInt64) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32)
    (hc : c.toNat < 2 ^ 32) (hd : d.toNat < 2 ^ 32) :
    (c + a * b + d).toNat = c.toNat + a.toNat * b.toNat + d.toNat := by
  have hab : a.toNat * b.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [UInt64.toNat_add, UInt64.toNat_mul]
  generalize a.toNat * b.toNat = P at *
  omega

end Secp256k1.CT
