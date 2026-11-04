import Std.Tactic.BVDecide
import Secp256k1.CT.U256

/-!
# Word-level lemmas for the constant-time arithmetic

Machine-checked facts about the 64-bit word tricks that `Secp256k1.CT`
relies on. The multi-limb arithmetic is proved correct in
`Secp256k1.CT.Proofs`.

`isZeroBit_eq`, `eqMask_eq` and `borrow_eq` are proved by bit-blasting
(`bv_decide`), whose certificate check trusts compiled code
(`Lean.ofReduceBool`). The other lemmas, and everything in
`Secp256k1.CT.Proofs`, use only the standard axioms.
-/

namespace Secp256k1.CT

/-- `isZeroBit` is the indicator of `x = 0`. -/
theorem isZeroBit_eq (x : UInt64) : isZeroBit x = if x = 0 then 1 else 0 := by
  unfold isZeroBit; split <;> bv_decide

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
  unfold eqMask maskOf isZeroBit; split <;> bv_decide

/-- The borrow extraction used by `U256.sub`: for 32-bit limbs and a borrow
bit, the top bit of the wrapped difference is the borrow out. -/
theorem borrow_eq (a b c : UInt64) (ha : a < 0x100000000) (hb : b < 0x100000000)
    (hc : c ≤ 1) : (a - b - c) >>> 63 = if a < b + c then 1 else 0 := by
  split <;> bv_decide

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
