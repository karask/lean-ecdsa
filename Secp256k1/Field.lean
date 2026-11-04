/-!
# Domain parameters and modular arithmetic

The secp256k1 domain parameters from SEC 2 (v2, §2.4.1), the prime field
`𝔽ₚ` and the scalar field `ℤ/nℤ`, both represented as `Fin`.

Lean's `Fin m` already implements `+`, `-` and `*` modulo `m`; this file adds
exponentiation, inversion (via Fermat's little theorem, both moduli are prime)
and square roots in `𝔽ₚ`.
-/

namespace Secp256k1

/-- The field prime `p = 2²⁵⁶ - 2³² - 977`. -/
def p : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

/-- The order of the base point `G` (the curve has cofactor 1). -/
def n : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- x-coordinate of the base point `G`. -/
def Gx : Nat := 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798

/-- y-coordinate of the base point `G`. -/
def Gy : Nat := 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

theorem p_eq : p = 2 ^ 256 - 2 ^ 32 - 977 := by decide

theorem n_lt_p : n < p := by decide

/-- `p ≡ 3 (mod 4)`, so square roots are `a^((p+1)/4)`. -/
theorem p_mod_four : p % 4 = 3 := by decide

theorem p_pos : 0 < p := by decide

theorem n_pos : 0 < n := by decide

instance : NeZero p := ⟨Nat.pos_iff_ne_zero.mp p_pos⟩

instance : NeZero n := ⟨Nat.pos_iff_ne_zero.mp n_pos⟩

/-- `b ^ e mod m` by left-to-right square-and-multiply. -/
def powMod (b e m : Nat) : Nat :=
  go (e.log2 + 1) (1 % m)
where
  /-- Process the low `i` bits of `e`, most significant first. -/
  go : Nat → Nat → Nat
    | 0, acc => acc
    | i + 1, acc =>
      let acc := acc * acc % m
      go i (if e.testBit i then acc * (b % m) % m else acc)

/-- Elements of the base field `𝔽ₚ`. -/
abbrev Fp := Fin p

/-- Elements of the scalar field `ℤ/nℤ`. -/
abbrev Fn := Fin n

namespace ModArith

variable {m : Nat} [NeZero m]

/-- Reduce a natural number into `Fin m`. -/
@[inline] def ofNat (a : Nat) : Fin m := Fin.ofNat m a

/-- Exponentiation in `ℤ/mℤ`. -/
@[inline] def pow (a : Fin m) (e : Nat) : Fin m := Fin.ofNat m (powMod a.val e m)

/-- Multiplicative inverse in `ℤ/mℤ` for prime `m` via `a^(m-2)`
(returns `0` for `a = 0`). -/
@[inline] def inv (a : Fin m) : Fin m := pow a (m - 2)

end ModArith

namespace Fp

/-- Reduce a natural number modulo `p`. -/
@[inline] def ofNat (a : Nat) : Fp := ModArith.ofNat a

@[inline] def pow (a : Fp) (e : Nat) : Fp := ModArith.pow a e

/-- Inverse in `𝔽ₚ` (with `inv 0 = 0`). -/
@[inline] def inv (a : Fp) : Fp := ModArith.inv a

/-- A square root of `a` in `𝔽ₚ`, if one exists. Uses `p ≡ 3 (mod 4)`. -/
def sqrt? (a : Fp) : Option Fp :=
  let r := pow a ((p + 1) / 4)
  if r * r = a then some r else none

/-- Whether the canonical representative is odd. -/
@[inline] def isOdd (a : Fp) : Bool := a.val % 2 = 1

end Fp

namespace Fn

/-- Reduce a natural number modulo `n`. -/
@[inline] def ofNat (a : Nat) : Fn := ModArith.ofNat a

/-- Inverse in `ℤ/nℤ` (with `inv 0 = 0`). -/
@[inline] def inv (a : Fn) : Fn := ModArith.inv a

end Fn

end Secp256k1
