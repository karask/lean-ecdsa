import Secp256k1.Curve
import Secp256k1.CT.Field

/-!
# Constant-time scalar multiplication

Points in homogeneous projective coordinates `(X : Y : Z) ↦ (X/Z, Y/Z)` with
the point at infinity `(0 : 1 : 0)`.

Addition and doubling use the *complete* formulas of Renes, Costello and
Batina, "Complete addition formulas for prime order elliptic curves"
(EUROCRYPT 2016), Algorithms 7 and 9 for `y² = x³ + b`. They are correct for
every pair of inputs, including `P + P`, `P + (-P)` and `𝒪`, so they need no
case distinctions (and therefore no secret-dependent branches).

Scalar multiplication uses a fixed 4-bit window: 64 iterations of four
doublings and one addition of a table entry, the entry being fetched by
scanning the whole table with masked selects. The sequence of operations is
the same for every 256-bit scalar.
-/

namespace Secp256k1.CT

/-- A point in projective coordinates. -/
structure PPoint where
  X : Fe
  Y : Fe
  Z : Fe
  deriving Inhabited

namespace PPoint

/-- `3·b = 21`. -/
def b3 : Fe := Fe.ofNat 21

/-- The point at infinity `(0 : 1 : 0)`. -/
def infinity : PPoint := ⟨Fe.zero, Fe.one, Fe.zero⟩

/-- From a reference affine point. **Public values only.** -/
def ofPoint : Point → PPoint
  | .infinity => infinity
  | .affine x y => ⟨Fe.ofNat x.val, Fe.ofNat y.val, Fe.one⟩

/-- Complete addition (RCB16, Algorithm 7; 12M + 2m₃ᵦ). -/
def add (P Q : PPoint) : PPoint :=
  let t0 := P.X * Q.X
  let t1 := P.Y * Q.Y
  let t2 := P.Z * Q.Z
  let t3 := P.X + P.Y
  let t4 := Q.X + Q.Y
  let t3 := t3 * t4
  let t4 := t0 + t1
  let t3 := t3 - t4
  let t4 := P.Y + P.Z
  let X3 := Q.Y + Q.Z
  let t4 := t4 * X3
  let X3 := t1 + t2
  let t4 := t4 - X3
  let X3 := P.X + P.Z
  let Y3 := Q.X + Q.Z
  let X3 := X3 * Y3
  let Y3 := t0 + t2
  let Y3 := X3 - Y3
  let X3 := t0 + t0
  let t0 := X3 + t0
  let t2 := b3 * t2
  let Z3 := t1 + t2
  let t1 := t1 - t2
  let Y3 := b3 * Y3
  let X3 := t4 * Y3
  let t2 := t3 * t1
  let X3 := t2 - X3
  let Y3 := Y3 * t0
  let t1 := t1 * Z3
  let Y3 := t1 + Y3
  let t0 := t0 * t3
  let Z3 := Z3 * t4
  let Z3 := Z3 + t0
  ⟨X3, Y3, Z3⟩

/-- Complete doubling (RCB16, Algorithm 9; 6M + 2S + 1m₃ᵦ). -/
def double (P : PPoint) : PPoint :=
  let t0 := P.Y * P.Y
  let Z3 := t0 + t0
  let Z3 := Z3 + Z3
  let Z3 := Z3 + Z3
  let t1 := P.Y * P.Z
  let t2 := P.Z * P.Z
  let t2 := b3 * t2
  let X3 := t2 * Z3
  let Y3 := t0 + t2
  let Z3 := t1 * Z3
  let t1 := t2 + t2
  let t2 := t1 + t2
  let t0 := t0 - t2
  let Y3 := t0 * Y3
  let Y3 := X3 + Y3
  let t1 := P.X * P.Y
  let X3 := t0 * t1
  let X3 := X3 + X3
  ⟨X3, Y3, Z3⟩

/-- `-P`. -/
def neg (P : PPoint) : PPoint := ⟨P.X, -P.Y, P.Z⟩

/-- `mask = all-ones ? P : Q`. -/
@[inline] def select (mask : UInt64) (P Q : PPoint) : PPoint :=
  ⟨Fe.select mask P.X Q.X, Fe.select mask P.Y Q.Y, Fe.select mask P.Z Q.Z⟩

/-- Affine coordinates `(X/Z, Y/Z)` with one constant-time inversion, and
`1` if the point is `𝒪` (then the coordinates are `0`). -/
def toAffine (P : PPoint) : Fe × Fe × UInt64 :=
  let zInv := P.Z.inv
  (P.X * zInv, P.Y * zInv, P.Z.isZero)

/-- Convert to a reference affine point. The conversion to `Nat` is variable
time, so use this only once the result may be revealed (public keys, the
nonce point `R` of a signature, whose coordinates are published as `r` and
the recovery id). -/
def toPoint (P : PPoint) : Point :=
  let (x, y, inf) := declassify P.toAffine
  if inf == 1 then .infinity else .affine x.toFp y.toFp

/-- The 16 multiples `0·P, 1·P, …, 15·P`. -/
def table (P : PPoint) : Array PPoint :=
  go 14 #[infinity, P] P
where
  go : Nat → Array PPoint → PPoint → Array PPoint
    | 0, acc, _ => acc
    | k + 1, acc, last => let next := last.add P; go k (acc.push next) next

/-- `T[idx]` for `idx ∈ [0, 16)`, reading every entry of the table. -/
def lookup (T : Array PPoint) (idx : UInt64) : PPoint :=
  go 0 infinity
where
  go : Nat → PPoint → PPoint
    | j, acc =>
      if h : j < T.size then go (j + 1) (select (eqMask j.toUInt64 idx) T[j] acc) else acc
  termination_by j => T.size - j

/-- `k • P` with a precomputed table `T = table P`: for each of the 64 windows,
from the most significant, four doublings then one table addition. -/
def smulTable (T : Array PPoint) (k : Scalar) : PPoint :=
  go 64 infinity
where
  go : Nat → PPoint → PPoint
    | 0, acc => acc
    | w + 1, acc =>
      let acc := acc.double.double.double.double
      go w (acc.add (lookup T (k.nibble w)))

/-- Constant-time `k • P`. -/
def smul (k : Scalar) (P : PPoint) : PPoint := smulTable (table P) k

/-- The window table for the base point `G`, computed once. -/
def gTable : Array PPoint := table (ofPoint G)

/-- Constant-time `k • G`. -/
def smulG (k : Scalar) : PPoint := smulTable gTable k

/-- `P` with its projective coordinates multiplied by `z` (the same point for `z ≠ 0`). -/
def scale (z : Fe) (P : PPoint) : PPoint := ⟨z * P.X, z * P.Y, z * P.Z⟩

/-- `G` as a constant-time point. -/
def gPoint : PPoint := ofPoint G

/-- Constant-time `k • G` with randomised projective coordinates (Coron's
countermeasure against differential power analysis). The table is built from
`(z·Gx : z·Gy : z)` and the accumulator starts at `(0 : z : 0)`, so every
intermediate coordinate, including the selected table entries, carries a factor
unknown to an observer. `z = 0` is replaced by `1`. The result represents the
same point as `smulG k` (`PPoint.smulGBlind_correct`). -/
def smulGBlind (k : Scalar) (z : Fe) : PPoint :=
  let z := Fe.select (maskOf z.isZero) Fe.one z
  smulTable.go (table (scale z gPoint)) k 64 ⟨Fe.zero, z, Fe.zero⟩

end PPoint

end Secp256k1.CT
