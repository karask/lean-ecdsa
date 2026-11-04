import Secp256k1.CT.U256

/-!
# Constant-time field and scalar arithmetic

* `Fe`: elements of `𝔽ₚ`, stored in Montgomery form `a·R mod p`.
* `Scalar`: elements of `ℤ/nℤ`, stored in plain canonical form `< n` (so
  their bits can be read directly by the scalar multiplication).

All operations are built from the constant-time primitives in
`Secp256k1.CT.U256`. Functions marked "public values only" go through `Nat`
and must not be applied to secrets.
-/

namespace Secp256k1.CT

/-- An element of `𝔽ₚ` in Montgomery form (`mont = a·2²⁵⁶ mod p`, canonical). -/
structure Fe where
  mont : U256
  deriving Inhabited

namespace Fe

def zero : Fe := ⟨U256.zero⟩

def one : Fe := ⟨pMod.one⟩

/-- Reduce a 256-bit integer modulo `p`. Constant time. -/
def ofU256 (a : U256) : Fe := ⟨pMod.toMont a⟩

/-- The canonical representative in `[0, p)`. Constant time. -/
def toU256 (a : Fe) : U256 := pMod.fromMont a.mont

/-- From 32 big-endian bytes, reduced modulo `p`. Constant time. -/
def ofBytes (bs : ByteArray) : Fe := ofU256 (U256.ofBytes bs)

/-- 32 big-endian bytes of the canonical representative. Constant time. -/
def toBytes (a : Fe) : ByteArray := a.toU256.toBytes

/-- `x mod p`. **Public values only.** -/
def ofNat (x : Nat) : Fe := ofU256 (U256.ofNat (x % p))

/-- The canonical representative as a `Nat`. **Public values only.** -/
def toNat (a : Fe) : Nat := a.toU256.toNat

/-- The reference field element. **Public values only.** -/
def toFp (a : Fe) : Fp := Fp.ofNat a.toNat

@[inline] def add (a b : Fe) : Fe := ⟨pMod.add a.mont b.mont⟩
@[inline] def sub (a b : Fe) : Fe := ⟨pMod.sub a.mont b.mont⟩
@[inline] def neg (a : Fe) : Fe := ⟨pMod.neg a.mont⟩
@[inline] def mul (a b : Fe) : Fe := ⟨pMod.mul a.mont b.mont⟩

instance : Add Fe := ⟨add⟩
instance : Sub Fe := ⟨sub⟩
instance : Neg Fe := ⟨neg⟩
instance : Mul Fe := ⟨mul⟩

/-- `a^(p-2) = a⁻¹` (and `0` for `a = 0`). Fixed sequence of operations. -/
def inv (a : Fe) : Fe := ⟨pMod.pow a.mont (p - 2)⟩

/-- `1` if `a = 0`, else `0`. -/
@[inline] def isZero (a : Fe) : UInt64 := a.mont.isZero

/-- `1` if `a = b`, else `0`. -/
@[inline] def eq (a b : Fe) : UInt64 := U256.eq a.mont b.mont

/-- `mask = all-ones ? a : b`. -/
@[inline] def select (mask : UInt64) (a b : Fe) : Fe := ⟨U256.select mask a.mont b.mont⟩

end Fe

/-- An element of `ℤ/nℤ` in canonical form (`val < n`). The invariant is
maintained by every constructor in this namespace. -/
structure Scalar where
  val : U256
  deriving Inhabited

namespace Scalar

def zero : Scalar := ⟨U256.zero⟩

def one : Scalar := ⟨U256.one⟩

/-- Parse 32 big-endian bytes, rejecting values `≥ n`. The comparison is
constant time; only whether the input was in range is revealed. -/
def ofBytes? (bs : ByteArray) : Option Scalar :=
  if bs.size ≠ 32 then none
  else
    let v := U256.ofBytes bs
    if U256.lt v nMod.m == 1 then some ⟨v⟩ else none

/-- From 32 big-endian bytes, reduced modulo `n`. Constant time. -/
def ofBytesReduce (bs : ByteArray) : Scalar :=
  ⟨nMod.fromMont (nMod.toMont (U256.ofBytes bs))⟩

/-- 32 big-endian bytes. Constant time. -/
def toBytes (a : Scalar) : ByteArray := a.val.toBytes

/-- `x mod n`. **Public values only.** -/
def ofNat (x : Nat) : Scalar := ⟨U256.ofNat (x % n)⟩

/-- The value as a `Nat`. **Public values only.** -/
def toNat (a : Scalar) : Nat := a.val.toNat

@[inline] def add (a b : Scalar) : Scalar := ⟨nMod.add a.val b.val⟩
@[inline] def sub (a b : Scalar) : Scalar := ⟨nMod.sub a.val b.val⟩
@[inline] def neg (a : Scalar) : Scalar := ⟨nMod.neg a.val⟩

/-- `a · b mod n` as two Montgomery products: `(a·b·R⁻¹)·R²·R⁻¹ = a·b`. -/
def mul (a b : Scalar) : Scalar := ⟨nMod.mul (nMod.mul a.val b.val) nMod.r2⟩

instance : Add Scalar := ⟨add⟩
instance : Sub Scalar := ⟨sub⟩
instance : Neg Scalar := ⟨neg⟩
instance : Mul Scalar := ⟨mul⟩

/-- `a^(n-2) = a⁻¹ mod n` (and `0` for `a = 0`). Fixed sequence of operations. -/
def inv (a : Scalar) : Scalar :=
  ⟨nMod.fromMont (nMod.pow (nMod.toMont a.val) (n - 2))⟩

/-- `1` if `a = 0`, else `0`. -/
@[inline] def isZero (a : Scalar) : UInt64 := a.val.isZero

/-- `1` if `a = b`, else `0`. -/
@[inline] def eq (a b : Scalar) : UInt64 := U256.eq a.val b.val

/-- The 4-bit window `w ∈ [0, 64)` (bits `4w … 4w+3`). The position `w` is
public; the returned bits are not inspected by any branch. -/
@[inline] def nibble (a : Scalar) (w : Nat) : UInt64 :=
  (a.val.limb (w / 8) >>> (4 * (w % 8)).toUInt64) &&& 0xF

end Scalar

end Secp256k1.CT
