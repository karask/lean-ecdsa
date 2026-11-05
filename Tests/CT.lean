import Secp256k1
import Tests.Harness

/-!
# Tests for the constant-time arithmetic

Every operation of `Secp256k1.CT` is compared with the reference
implementation (`Fin p`, `Fin n`, `Secp256k1.Point`) on edge cases and
pseudo-random inputs.
-/

open Secp256k1 Secp256k1.CT

namespace Tests

/-- Deterministic pseudo-random 256-bit values. -/
def prng (i : Nat) : Nat := bytesToNat (SHA256.hash (natToBytes i 8))

/-- Values around limb and modulus boundaries plus pseudo-random ones, reduced mod `m`. -/
def sampleValues (m : Nat) : List Nat :=
  let edges := [0, 1, 2, 3, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1, 2 ^ 64 - 1, 2 ^ 128, 2 ^ 224 - 1,
    2 ^ 255, 2 ^ 255 - 1, m / 2, m / 2 + 1, m - 3, m - 2, m - 1,
    2 ^ 256 - 1 - 2 ^ 32]
  (edges ++ (List.range 12).map prng).map (· % m)

def testU256 : TestM Unit := do
  section_ "Constant-time: 256-bit words"
  let vals := [0, 1, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 255, 2 ^ 256 - 1, p, n] ++ (List.range 6).map prng
  for a in vals do
    let A := U256.ofNat a
    check s!"U256 toNat/ofNat {a}" (A.toNat == a)
    check s!"U256 toBytes {a}" (A.toBytes.data == (natToBytes a 32).data)
    check s!"U256 ofBytes {a}" ((U256.ofBytes (natToBytes a 32)).toNat == a)
    check s!"U256 isZero {a}" (A.isZero == if a == 0 then 1 else 0)
    for b in vals do
      let B := U256.ofNat b
      let s := U256.add A B
      check s!"U256 add" (s.low.toNat + s.l8.toNat * 2 ^ 256 == a + b && s.l8 ≤ 1)
      let d := U256.sub A B
      check s!"U256 sub" (d.low.toNat == (a + 2 ^ 256 - b) % 2 ^ 256 &&
        d.l8 == if a < b then 1 else 0)
      check s!"U256 lt" (U256.lt A B == if a < b then 1 else 0)
      check s!"U256 eq" (U256.eq A B == if a == b then 1 else 0)
      check s!"U256 select" ((U256.select (maskOf 1) A B).toNat == a &&
        (U256.select (maskOf 0) A B).toNat == b)
      for x in [0, 1, 0xFFFFFFFF, (prng a % 2 ^ 32)] do
        let r := U256.mulAddRow A x.toUInt64 B
        check s!"U256 mulAddRow" (r.low.toNat + r.l8.toNat * 2 ^ 256 == a + x * b)

def testModulus : TestM Unit := do
  section_ "Constant-time: Montgomery constants"
  for (name, M) in [("p", pMod), ("n", nMod)] do
    check s!"{name}: m·mInv ≡ -1 (mod 2³²)" ((M.m.l0 * M.mInv) &&& M32 == M32)
    check s!"{name}: one = R mod m" (M.one.toNat == 2 ^ 256 % M.value)
    check s!"{name}: r2 = R² mod m" (M.r2.toNat == 2 ^ 512 % M.value)
    check s!"{name}: m" (M.m.toNat == M.value)

def testFe : TestM Unit := do
  section_ "Constant-time: field 𝔽ₚ vs Fin p"
  let vals := sampleValues p
  for a in vals do
    let A := Fe.ofNat a
    let a' := Fp.ofNat a
    check s!"Fe roundtrip {a}" (A.toNat == a)
    check s!"Fe bytes {a}" ((Fe.ofBytes (natToBytes a 32)).toNat == a &&
      A.toBytes.data == (natToBytes a 32).data)
    check s!"Fe neg {a}" ((-A).toNat == (-a').val)
    check s!"Fe inv {a}" (A.inv.toNat == (Fp.inv a').val)
    check s!"Fe isZero {a}" (A.isZero == if a == 0 then 1 else 0)
    for b in vals do
      let B := Fe.ofNat b
      let b' := Fp.ofNat b
      check s!"Fe add {a} {b}" ((A + B).toNat == (a' + b').val)
      check s!"Fe sub {a} {b}" ((A - B).toNat == (a' - b').val)
      check s!"Fe mul {a} {b}" ((A * B).toNat == (a' * b').val)
      check s!"Fe eq {a} {b}" (Fe.eq A B == if a == b then 1 else 0)
  -- Non-canonical 256-bit inputs are reduced.
  for x in [p, p + 1, 2 ^ 256 - 1] do
    check s!"Fe reduces {x}" ((Fe.ofBytes (natToBytes x 32)).toNat == x % p)

def testScalar : TestM Unit := do
  section_ "Constant-time: scalars ℤ/nℤ vs Fin n"
  let vals := sampleValues n
  for a in vals do
    let A := Scalar.ofNat a
    let a' := Fn.ofNat a
    check s!"Scalar roundtrip {a}" (A.toNat == a)
    check s!"Scalar ofBytes? {a}" ((Scalar.ofBytes? (natToBytes a 32)).map (·.toNat) == some a)
    check s!"Scalar neg {a}" ((-A).toNat == (-a').val)
    check s!"Scalar inv {a}" (A.inv.toNat == (Fn.inv a').val)
    check s!"Scalar nibbles {a}" <|
      ((List.range 64).foldr (fun w acc => acc * 16 + (A.nibble w).toNat) 0) == a
    for b in vals do
      let B := Scalar.ofNat b
      let b' := Fn.ofNat b
      check s!"Scalar add {a} {b}" ((A + B).toNat == (a' + b').val)
      check s!"Scalar sub {a} {b}" ((A - B).toNat == (a' - b').val)
      check s!"Scalar mul {a} {b}" ((A * B).toNat == (a' * b').val)
  for x in [n, n + 1, 2 ^ 256 - 1] do
    check s!"Scalar ofBytes? rejects {x}" (Scalar.ofBytes? (natToBytes x 32)).isNone
    check s!"Scalar ofBytesReduce {x}" ((Scalar.ofBytesReduce (natToBytes x 32)).toNat == x % n)
  check "Scalar ofBytes? wrong length" (Scalar.ofBytes? (natToBytes 1 31)).isNone

def testPoints : TestM Unit := do
  section_ "Constant-time: complete point formulas and scalar multiplication"
  let pts : List Point := [.infinity, G, -G, (2 : Nat) • G, (n - 2) • G] ++
    (List.range 6).map (fun i => (prng (100 + i) % n) • G)
  -- Projective representatives with Z ≠ 1, to exercise the general formulas.
  let scaled (P : Point) (z : Nat) : PPoint :=
    let Q := PPoint.ofPoint P
    let Z := Fe.ofNat z
    ⟨Q.X * Z, Q.Y * Z, Q.Z * Z⟩
  for (P, i) in pts.zipIdx do
    let PP := scaled P (prng (200 + i) % p)
    check s!"toPoint/ofPoint {i}" ((PPoint.ofPoint P).toPoint == P && PP.toPoint == P)
    check s!"double {i}" (PP.double.toPoint == P + P)
    check s!"add self {i}" ((PP.add PP).toPoint == P + P)
    check s!"add neg {i}" ((PP.add PP.neg).toPoint == .infinity)
    for (Q, j) in pts.zipIdx do
      let QQ := scaled Q (prng (300 + j) % p)
      check s!"add {i} {j}" ((PP.add QQ).toPoint == P + Q)
  section_ "Constant-time: k • G and k • P vs reference"
  let scalars := [0, 1, 2, 3, 15, 16, 17, 255, 256, 2 ^ 32, 2 ^ 128, 2 ^ 255,
    n / 2, n - 16, n - 15, n - 2, n - 1] ++ (List.range 12).map (fun i => prng (400 + i) % n)
  for k in scalars do
    check s!"smulG {k}" ((PPoint.smulG (Scalar.ofNat k)).toPoint == k • G)
  -- Randomised projective coordinates give the same point for any blinding factor,
  -- including `0` (replaced by `1`) and values that are not reduced modulo `p`.
  let blinds := [0, 1, 2, p - 1] ++ (List.range 4).map (fun i => prng (450 + i) % p)
  for (k, i) in (scalars.take 12).zipIdx do
    let z := blinds[i % blinds.length]!
    let m : UInt64 := [0, 1, 0xFFFFFFFF, 0x12345678][i % 4]!
    check s!"smulGBlind {k} z={z % 1000} m={m}"
      ((PPoint.smulGBlind (Scalar.ofNat k) (Fe.ofNat z) m).toPoint == k • G)
  -- Multiplicative blinding of `s` gives the unblinded value, including `k = 0`.
  for i in [0:8] do
    let d := Scalar.ofNat (prng (470 + i) % n)
    let k := Scalar.ofNat (if i == 0 then 0 else prng (480 + i) % n)
    let e := Scalar.ofNat (prng (490 + i) % n)
    let c := signCore d k e
    check s!"blinded s {i}" (c.s.toNat == (k.inv * (e + c.r * d)).toNat)
    -- The blinding randomness `aux` does not change the result.
    let c' := signCore d k e (natToBytes (prng (500 + i)) 32)
    check s!"aux-independent {i}" (c'.r.toNat == c.r.toNat && c'.s.toNat == c.s.toNat &&
      c'.recId == c.recId && c'.ok == c.ok)
  check "smulGBlind unreduced z"
    ((PPoint.smulGBlind (Scalar.ofNat 12345) (Fe.ofBytes (ByteArray.replicate 32 0xff)) 7).toPoint
      == (12345 : Nat) • G)
  let P := (prng 500 % n) • G
  let T := PPoint.table (PPoint.ofPoint P)
  check "table size" (T.size == 16)
  for k in scalars.take 20 do
    check s!"smul {k}" ((PPoint.smulTable T (Scalar.ofNat k)).toPoint == k • P)
  for j in [0:16] do
    check s!"lookup {j}" ((PPoint.lookup T j.toUInt64).toPoint == j • P)

def testConstantTime : TestM Unit := do
  testU256
  testModulus
  testFe
  testScalar
  testPoints

end Tests
