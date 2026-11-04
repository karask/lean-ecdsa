import Secp256k1

/-!
# Constant-time check of the compiled code (valgrind)

Run with `./run.sh` (see `README.md`).

Every operation that handles the private key or the nonce is run on secret
bytes that have been marked *undefined* for valgrind's memcheck. memcheck then
reports any conditional branch or memory address in the **machine code** that
depends on those bytes, wherever it comes from: the Lean compiler, the C
compiler, or the Lean runtime. Only the final outputs, which are public by
design, are marked defined again before they are compared.

`--control` instead runs the variable-time reference arithmetic on the same
secrets. memcheck must report errors there; this shows that the check is able
to detect secret-dependent branches.
-/

open Secp256k1 Secp256k1.CT

/-- Mark the bytes as secret (undefined for memcheck). -/
@[extern "ctgrind_classify"] opaque markSecret (bytes : @& ByteArray) : IO Unit

/-- Mark the bytes as public (defined for memcheck). -/
@[extern "ctgrind_declassify"] opaque markPublic (bytes : @& ByteArray) : IO Unit

@[extern "ctgrind_running_on_valgrind"] opaque runningOnValgrind : Unit → Bool

namespace CTGrind

def affineBytes (P : PPoint) : ByteArray :=
  let (x, y, inf) := P.toAffine
  (x.toBytes ++ y.toBytes).push inf.toUInt8

def coreBytes (c : SignCore) : ByteArray :=
  ((c.r.toBytes ++ c.s.toBytes).push c.recId.toUInt8).push c.ok.toUInt8

def message : ByteArray := SHA256.hash "ctgrind message".toUTF8

def publicPoint : PPoint := PPoint.ofPoint ((0xC0FFEE : Nat) • G)

/-- Operations on a private key `d` and a nonce `k` (32 bytes each) that must
not branch on them. -/
def constantTimeCases : List (String × (ByteArray → ByteArray → ByteArray)) := [
  ("public key d • G (with affine conversion)", fun d _ =>
    affineBytes (PPoint.smulG ⟨U256.ofBytes d⟩)),
  ("k • P for a public point P", fun _ k =>
    affineBytes (PPoint.smul ⟨U256.ofBytes k⟩ publicPoint)),
  ("ECDSA signing core (R = k • G, r, s, recovery id, ok flag)", fun d k =>
    coreBytes (signCore ⟨U256.ofBytes d⟩ ⟨U256.ofBytes k⟩
      (Scalar.ofNat (ECDSA.hashToScalar message)))),
  ("RFC 6979 nonce generation (HMAC-SHA-256 keyed by d)", fun d _ =>
    (RFC6979.init d message).generate.1),
  ("RFC 6979 retry path (reseed and generate)", fun d _ =>
    (RFC6979.init d message).generate.2.reseed.generate.1),
  ("scalar range check k < n", fun _ k =>
    let (v, inRange) := Scalar.ofBytesChecked k
    v.toBytes.push inRange.toUInt8),
  ("scalar arithmetic k⁻¹ · (e + d)", fun d k =>
    let kS : Scalar := ⟨U256.ofBytes k⟩
    (kS.inv * (Scalar.ofNat 12345 + ⟨U256.ofBytes d⟩)).toBytes),
  ("private key bytes round trip", fun d _ => (Scalar.reduce (U256.ofBytes d)).toBytes),
  ("field inverse", fun d _ => (Fe.ofBytes d).inv.toBytes)]

/-- The variable-time reference arithmetic on the same secrets (positive control). -/
def controlCases : List (String × (ByteArray → ByteArray → ByteArray)) := [
  ("reference k • G (Nat, double-and-add)", fun _ k =>
    (Point.smul (bytesToNat k) G).toBytes),
  ("reference k⁻¹ mod n (Nat)", fun _ k =>
    natToBytes (Fn.inv (Fn.ofNat (bytesToNat k))).val 32)]

/-- Run each case on fresh secret copies of `d` and `k`. Inputs are read back
from references after being marked, so the computation cannot be scheduled
before the marking. -/
def runCases (cases : List (String × (ByteArray → ByteArray → ByteArray)))
    (d k : ByteArray) : IO Bool := do
  let mut ok := true
  for (name, f) in cases do
    let expected := f d k
    let dRef ← IO.mkRef (d.extract 0 d.size)
    let kRef ← IO.mkRef (k.extract 0 k.size)
    markSecret (← dRef.get)
    markSecret (← kRef.get)
    let out := f (← dRef.get) (← kRef.get)
    markPublic out
    let same := out == expected
    IO.println s!"  {if same then "ok  " else "FAIL"} {name}"
    ok := ok && same
  return ok

end CTGrind

open CTGrind in
def main (args : List String) : IO UInt32 := do
  if !runningOnValgrind () then
    IO.eprintln "warning: not running under valgrind, so nothing is being checked (use ./run.sh)"
  let d := SHA256.hash "ctgrind private key".toUTF8
  let k := SHA256.hash "ctgrind nonce".toUTF8
  -- Both values happen to be valid scalars (checked here, before they are marked).
  unless bytesToNat d < n && bytesToNat k < n && bytesToNat d ≠ 0 && bytesToNat k ≠ 0 do
    IO.eprintln "test secrets out of range"
    return 1
  let control := args.contains "--control"
  IO.println (if control then "Variable-time reference arithmetic (memcheck must report errors):"
    else "Constant-time operations (memcheck must report no errors):")
  let ok ← runCases (if control then controlCases else constantTimeCases) d k
  return if ok then 0 else 1
