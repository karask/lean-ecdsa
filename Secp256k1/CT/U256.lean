import Secp256k1.Bytes
import Secp256k1.Field

/-!
# Constant-time 256-bit arithmetic

Fixed-width integers and Montgomery modular arithmetic designed to run in
time independent of the *values* they operate on:

* A `U256` is eight 32-bit limbs, each held in a `UInt64` so that a limb
  product plus two carries always fits (`(2³²-1)² + 2(2³²-1) = 2⁶⁴-1`).
* Every function performs a fixed sequence of word operations. There are no
  branches, early exits or table lookups that depend on limb values; choices
  are made with bit masks (`selectWord`).
* The only branches are on *public* data: loop counters and the bits of public
  exponents in `Modulus.pow`.

Nothing in this file prevents the Lean or C compiler from introducing
branches; that has to be checked on the generated code (see the README).

`U256.toNat` and `U256.ofNat` go through `Nat` and are **not** constant
time. They exist for public constants, specifications and tests only.
-/

namespace Secp256k1.CT

/-- Mask selecting the low 32 bits of a limb. -/
abbrev M32 : UInt64 := 0xFFFFFFFF

/-- `1` if `x = 0` and `0` otherwise, without branching:
for `x ≠ 0` the top bit of `x ||| -x` is set. -/
@[inline] def isZeroBit (x : UInt64) : UInt64 := ((x ||| (0 - x)) >>> 63) ^^^ 1

/-- `bit ∈ {0, 1}` ↦ all-zeros / all-ones. -/
@[inline] def maskOf (bit : UInt64) : UInt64 := 0 - bit

/-- `mask = all-ones ? a : b`, for `mask ∈ {0, 2⁶⁴-1}`. -/
@[inline] def selectWord (mask a b : UInt64) : UInt64 := (a &&& mask) ||| (b &&& ~~~mask)

/-- All-ones if `a = b`, else zero. -/
@[inline] def eqMask (a b : UInt64) : UInt64 := maskOf (isZeroBit (a ^^^ b))

/-- Marks a value that is derived from secrets but is public by design, such
as a signature component or whether a key is in range. It is the identity
function. Every place where secret-derived data may influence control flow or
be converted to `Nat` goes through `declassify`, so these places can be found
with `grep` (the valgrind check in `ctgrind/` makes the same values public). -/
@[inline] def declassify {α : Type} (a : α) : α := a

/-- A 256-bit integer as eight little-endian 32-bit limbs (each `< 2³²`). -/
structure U256 where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64
  l4 : UInt64
  l5 : UInt64
  l6 : UInt64
  l7 : UInt64
  deriving Inhabited

/-- A 288-bit intermediate result: eight limbs plus a ninth (carry/borrow) limb. -/
structure U288 where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64
  l4 : UInt64
  l5 : UInt64
  l6 : UInt64
  l7 : UInt64
  l8 : UInt64
  deriving Inhabited

/-- The low eight limbs. -/
@[inline] def U288.low (t : U288) : U256 := ⟨t.l0, t.l1, t.l2, t.l3, t.l4, t.l5, t.l6, t.l7⟩

namespace U256

def zero : U256 := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

def one : U256 := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩

/-- Limb `i` (`i` is public; out-of-range indices give `0`). -/
@[inline] def limb (a : U256) : Nat → UInt64
  | 0 => a.l0 | 1 => a.l1 | 2 => a.l2 | 3 => a.l3
  | 4 => a.l4 | 5 => a.l5 | 6 => a.l6 | 7 => a.l7
  | _ => 0

/-- The represented value. **Not constant time**: specifications and tests only. -/
def toNat (a : U256) : Nat :=
  a.l0.toNat + a.l1.toNat * 2 ^ 32 + a.l2.toNat * 2 ^ 64 + a.l3.toNat * 2 ^ 96 +
  a.l4.toNat * 2 ^ 128 + a.l5.toNat * 2 ^ 160 + a.l6.toNat * 2 ^ 192 + a.l7.toNat * 2 ^ 224

/-- `x mod 2²⁵⁶` as limbs. **Not constant time**: public values only. -/
def ofNat (x : Nat) : U256 :=
  let w (i : Nat) : UInt64 := ((x >>> (32 * i)) % 2 ^ 32).toUInt64
  ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩

/-- Read limb `i` from 32 big-endian bytes. -/
@[inline] def beWord (bs : ByteArray) (i : Nat) : UInt64 :=
  let o := 28 - 4 * i
  (bs[o]!.toUInt64 <<< 24) ||| (bs[o + 1]!.toUInt64 <<< 16) |||
  (bs[o + 2]!.toUInt64 <<< 8) ||| bs[o + 3]!.toUInt64

/-- Decode exactly 32 big-endian bytes (missing bytes read as `0`). Constant time. -/
def ofBytes (bs : ByteArray) : U256 :=
  ⟨beWord bs 0, beWord bs 1, beWord bs 2, beWord bs 3,
   beWord bs 4, beWord bs 5, beWord bs 6, beWord bs 7⟩

@[inline] def pushWord (out : ByteArray) (w : UInt64) : ByteArray :=
  out.push (w >>> 24).toUInt8 |>.push (w >>> 16).toUInt8 |>.push (w >>> 8).toUInt8
    |>.push w.toUInt8

/-- Encode as 32 big-endian bytes. Constant time. -/
def toBytes (a : U256) : ByteArray :=
  [a.l7, a.l6, a.l5, a.l4, a.l3, a.l2, a.l1, a.l0].foldl pushWord (.emptyWithCapacity 32)

/-- `mask = all-ones ? a : b`. -/
@[inline] def select (mask : UInt64) (a b : U256) : U256 :=
  ⟨selectWord mask a.l0 b.l0, selectWord mask a.l1 b.l1, selectWord mask a.l2 b.l2,
   selectWord mask a.l3 b.l3, selectWord mask a.l4 b.l4, selectWord mask a.l5 b.l5,
   selectWord mask a.l6 b.l6, selectWord mask a.l7 b.l7⟩

/-- `1` if `a = 0`, else `0`. -/
@[inline] def isZero (a : U256) : UInt64 :=
  isZeroBit (a.l0 ||| a.l1 ||| a.l2 ||| a.l3 ||| a.l4 ||| a.l5 ||| a.l6 ||| a.l7)

/-- `1` if `a = b`, else `0`. -/
@[inline] def eq (a b : U256) : UInt64 :=
  isZeroBit ((a.l0 ^^^ b.l0) ||| (a.l1 ^^^ b.l1) ||| (a.l2 ^^^ b.l2) ||| (a.l3 ^^^ b.l3) |||
    (a.l4 ^^^ b.l4) ||| (a.l5 ^^^ b.l5) ||| (a.l6 ^^^ b.l6) ||| (a.l7 ^^^ b.l7))

/-- `a + b`; the ninth limb is the carry (`0` or `1`). -/
def add (a b : U256) : U288 :=
  let t0 := a.l0 + b.l0
  let t1 := a.l1 + b.l1 + (t0 >>> 32)
  let t2 := a.l2 + b.l2 + (t1 >>> 32)
  let t3 := a.l3 + b.l3 + (t2 >>> 32)
  let t4 := a.l4 + b.l4 + (t3 >>> 32)
  let t5 := a.l5 + b.l5 + (t4 >>> 32)
  let t6 := a.l6 + b.l6 + (t5 >>> 32)
  let t7 := a.l7 + b.l7 + (t6 >>> 32)
  ⟨t0 &&& M32, t1 &&& M32, t2 &&& M32, t3 &&& M32,
   t4 &&& M32, t5 &&& M32, t6 &&& M32, t7 &&& M32, t7 >>> 32⟩

/-- `a - b mod 2²⁵⁶`; the ninth limb is the borrow (`1` iff `a < b`).
Each limb difference is computed with wrap-around, so a negative result shows
up as the top bit of the 64-bit word. -/
def sub (a b : U256) : U288 :=
  let t0 := a.l0 - b.l0
  let t1 := a.l1 - b.l1 - (t0 >>> 63)
  let t2 := a.l2 - b.l2 - (t1 >>> 63)
  let t3 := a.l3 - b.l3 - (t2 >>> 63)
  let t4 := a.l4 - b.l4 - (t3 >>> 63)
  let t5 := a.l5 - b.l5 - (t4 >>> 63)
  let t6 := a.l6 - b.l6 - (t5 >>> 63)
  let t7 := a.l7 - b.l7 - (t6 >>> 63)
  ⟨t0 &&& M32, t1 &&& M32, t2 &&& M32, t3 &&& M32,
   t4 &&& M32, t5 &&& M32, t6 &&& M32, t7 &&& M32, t7 >>> 63⟩

/-- `1` if `a < b`, else `0`. -/
@[inline] def lt (a b : U256) : UInt64 := (sub a b).l8

/-- `acc + x * y` for a single limb `x`. The result is below `2²⁸⁸`. -/
def mulAddRow (acc : U256) (x : UInt64) (y : U256) : U288 :=
  let t0 := acc.l0 + x * y.l0
  let t1 := acc.l1 + x * y.l1 + (t0 >>> 32)
  let t2 := acc.l2 + x * y.l2 + (t1 >>> 32)
  let t3 := acc.l3 + x * y.l3 + (t2 >>> 32)
  let t4 := acc.l4 + x * y.l4 + (t3 >>> 32)
  let t5 := acc.l5 + x * y.l5 + (t4 >>> 32)
  let t6 := acc.l6 + x * y.l6 + (t5 >>> 32)
  let t7 := acc.l7 + x * y.l7 + (t6 >>> 32)
  ⟨t0 &&& M32, t1 &&& M32, t2 &&& M32, t3 &&& M32,
   t4 &&& M32, t5 &&& M32, t6 &&& M32, t7 &&& M32, t7 >>> 32⟩

end U256

/-! ## Montgomery arithmetic modulo an odd 256-bit modulus -/

/-- Precomputed constants for Montgomery arithmetic modulo an odd `m`
with `2²⁵⁵ < m < 2²⁵⁶`, using `R = 2²⁵⁶`. -/
structure Modulus where
  /-- The modulus as a number. -/
  value : Nat
  /-- The modulus as limbs. -/
  m : U256
  /-- `-m⁻¹ mod 2³²`. -/
  mInv : UInt64
  /-- `R mod m` (the Montgomery form of `1`). -/
  one : U256
  /-- `R² mod m` (used to convert into Montgomery form). -/
  r2 : U256

namespace Modulus

/-- Build the constants for an odd modulus `2²⁵⁵ < m < 2²⁵⁶`. Uses `Nat`; only
for public moduli. Since the units mod `2³²` have order `2³¹`,
`m⁻¹ = m^(2³¹-1) mod 2³²`. -/
def ofNat (m : Nat) : Modulus where
  value := m
  m := U256.ofNat m
  mInv := (2 ^ 32 - powMod m (2 ^ 31 - 1) (2 ^ 32)).toUInt64
  one := U256.ofNat (2 ^ 256 % m)
  r2 := U256.ofNat (2 ^ 512 % m)

/-- Reduce `t < 2m` (given as nine limbs, top limb `0` or `1`) to `[0, m)`
by a masked conditional subtraction. -/
def condSub (M : Modulus) (t : U288) : U256 :=
  let d := U256.sub t.low M.m
  -- t ≥ m  ⟺  t has a ninth-limb bit, or the low part did not borrow.
  let useD := t.l8 ||| (d.l8 ^^^ 1)
  U256.select (maskOf useD) d.low t.low

/-- `a + b mod m` for `a, b < m`. -/
def add (M : Modulus) (a b : U256) : U256 := M.condSub (U256.add a b)

/-- `a - b mod m` for `a, b < m`: subtract, then add back `m` if it borrowed. -/
def sub (M : Modulus) (a b : U256) : U256 :=
  let d := U256.sub a b
  (U256.add d.low (U256.select (maskOf d.l8) M.m U256.zero)).low

/-- `-a mod m` for `a < m`. -/
def neg (M : Modulus) (a : U256) : U256 := M.sub U256.zero a

/-- One iteration of CIOS Montgomery multiplication: `t := (t + aᵢ·b + u·m) / 2³²`
with `u` chosen so that the division is exact. Keeps `t < 2m` when `b < m`. -/
@[inline] def montStep (M : Modulus) (b : U256) (t : U288) (ai : UInt64) : U288 :=
  let s := U256.mulAddRow t.low ai b
  let hi := s.l8 + t.l8
  let u := (s.l0 * M.mInv) &&& M32
  let r := U256.mulAddRow s.low u M.m
  -- r.l0 = 0 by the choice of u; shift everything down by one limb.
  let top := r.l8 + hi
  ⟨r.l1, r.l2, r.l3, r.l4, r.l5, r.l6, r.l7, top &&& M32, top >>> 32⟩

/-- Montgomery product `a · b · R⁻¹ mod m`, for any `a < 2²⁵⁶` and `b < m`. -/
def mul (M : Modulus) (a b : U256) : U256 :=
  let t : U288 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  let t := M.montStep b t a.l0
  let t := M.montStep b t a.l1
  let t := M.montStep b t a.l2
  let t := M.montStep b t a.l3
  let t := M.montStep b t a.l4
  let t := M.montStep b t a.l5
  let t := M.montStep b t a.l6
  let t := M.montStep b t a.l7
  M.condSub t

/-- `a · R mod m`: convert into Montgomery form. Accepts any `a < 2²⁵⁶`,
so this also reduces `a` modulo `m`. -/
@[inline] def toMont (M : Modulus) (a : U256) : U256 := M.mul a M.r2

/-- `a · R⁻¹ mod m`: convert out of Montgomery form. -/
@[inline] def fromMont (M : Modulus) (a : U256) : U256 := M.mul a U256.one

/-- `aᵉ` in Montgomery form, for `a` in Montgomery form and a **public**
exponent `e`. The sequence of operations depends only on `e`. -/
def pow (M : Modulus) (a : U256) (e : Nat) : U256 :=
  go (e.log2 + 1) M.one
where
  go : Nat → U256 → U256
    | 0, acc => acc
    | i + 1, acc =>
      let acc := M.mul acc acc
      go i (if e.testBit i then M.mul acc a else acc)

end Modulus

/-- Montgomery constants for the field prime `p`. -/
def pMod : Modulus := .ofNat p

/-- Montgomery constants for the group order `n`. -/
def nMod : Modulus := .ofNat n

end Secp256k1.CT
