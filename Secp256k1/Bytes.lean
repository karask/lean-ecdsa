/-!
# Byte utilities

Big-endian conversions between natural numbers and byte arrays, plus hex
encoding/decoding. These are the octet-string conversions used throughout
SEC 1 and RFC 6979.
-/

namespace Secp256k1

/-- Interpret a byte array as a big-endian unsigned integer (SEC 1 `OS2IP`). -/
def bytesToNat (bs : ByteArray) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Encode `x mod 256^len` as exactly `len` big-endian bytes (SEC 1 `I2OSP`). -/
def natToBytes (x len : Nat) : ByteArray :=
  (go len x []).toByteArray
where
  go : Nat → Nat → List UInt8 → List UInt8
    | 0, _, acc => acc
    | k + 1, v, acc => go k (v / 256) ((v % 256).toUInt8 :: acc)

/-- Number of bytes in the minimal big-endian encoding of `x` (`0` for `x = 0`). -/
def byteLength (x : Nat) : Nat :=
  if x = 0 then 0 else x.log2 / 8 + 1

/-- Minimal big-endian encoding of `x` (empty for `x = 0`). -/
def natToMinimalBytes (x : Nat) : ByteArray :=
  natToBytes x (byteLength x)

/-- A byte array of `len` copies of `b`. -/
def ByteArray.replicate (len : Nat) (b : UInt8) : ByteArray :=
  ⟨Array.replicate len b⟩

theorem natToBytes_go_length (k v : Nat) (acc : List UInt8) :
    (natToBytes.go k v acc).length = k + acc.length := by
  induction k generalizing v acc with
  | zero => simp [natToBytes.go]
  | succ k ih => simp [natToBytes.go, ih]; omega

theorem natToBytes_size (x len : Nat) : (natToBytes x len).size = len := by
  simp [natToBytes, natToBytes_go_length]

namespace Hex

/-- Value of a single hexadecimal digit. -/
def digit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Decode a hex string (even length, no `0x` prefix, either case). -/
def decode? (s : String) : Option ByteArray :=
  go s.toList .empty
where
  go : List Char → ByteArray → Option ByteArray
    | [], acc => some acc
    | [_], _ => none
    | hi :: lo :: rest, acc => do
      let a ← digit? hi
      let b ← digit? lo
      go rest (acc.push (a * 16 + b).toUInt8)

/-- Decode a hex string, returning the empty array on malformed input.
Intended for literals in tests and examples. -/
def decode! (s : String) : ByteArray :=
  (decode? s).getD .empty

private def nibble (v : Nat) : Char :=
  if v < 10 then Char.ofNat ('0'.toNat + v) else Char.ofNat ('a'.toNat + v - 10)

/-- Lower-case hex encoding of a byte array. -/
def encode (bs : ByteArray) : String :=
  bs.foldl (fun s b => (s.push (nibble (b.toNat / 16))).push (nibble (b.toNat % 16))) ""

end Hex

end Secp256k1
