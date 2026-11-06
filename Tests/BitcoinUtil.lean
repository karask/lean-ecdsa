import Secp256k1

/-!
# Bitcoin encodings for the tests

Just enough of Bitcoin's encodings to run Bitcoin Core's key tests: the
double SHA-256 `Hash`, Base58Check, WIF private keys, RIPEMD-160 and P2PKH
addresses. These are test helpers, checked against their own published
vectors in `Tests/BitcoinCore.lean`; the library does not depend on them.
-/

namespace Tests.Bitcoin

open Secp256k1

/-- Bitcoin Core's `Hash`: SHA-256 applied twice. -/
def sha256d (bs : ByteArray) : ByteArray := SHA256.hash (SHA256.hash bs)

/-! ## Base58Check -/

def alphabet : String := "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

/-- Decode Base58 (leading `1`s are zero bytes). -/
def base58Decode? (s : String) : Option ByteArray := do
  let chars := s.toList
  let zeros := (chars.takeWhile (· == '1')).length
  let mut v : Nat := 0
  for c in chars do
    let some i := alphabet.toList.idxOf? c | none
    v := v * 58 + i
  let body := natToMinimalBytes v
  return ByteArray.replicate zeros 0 ++ body

/-- Encode Base58 (leading zero bytes become `1`s). -/
def base58Encode (bs : ByteArray) : String := Id.run do
  let zeros := (bs.data.toList.takeWhile (· == 0)).length
  let mut v := bytesToNat bs
  let mut out : List Char := []
  while v > 0 do
    out := alphabet.toList[v % 58]! :: out
    v := v / 58
  return String.ofList (List.replicate zeros '1' ++ out)

/-- Decode Base58Check: the payload, if the 4-byte checksum matches. -/
def base58CheckDecode? (s : String) : Option ByteArray := do
  let bs ← base58Decode? s
  if bs.size < 4 then none
  let payload := bs.extract 0 (bs.size - 4)
  if (sha256d payload).extract 0 4 == bs.extract (bs.size - 4) bs.size then some payload else none

def base58CheckEncode (payload : ByteArray) : String :=
  base58Encode (payload ++ (sha256d payload).extract 0 4)

/-- Decode a mainnet WIF private key: the key and whether its public key is
serialised compressed. -/
def decodeWIF? (s : String) : Option (ECDSA.PrivateKey × Bool) := do
  let p ← base58CheckDecode? s
  if p.size = 33 && p[0]! == 0x80 then
    return (← ECDSA.PrivateKey.ofBytes? (p.extract 1 33), false)
  else if p.size = 34 && p[0]! == 0x80 && p[33]! == 0x01 then
    return (← ECDSA.PrivateKey.ofBytes? (p.extract 1 33), true)
  else none

/-! ## RIPEMD-160 -/

namespace RIPEMD160

def rl : Array Nat := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]

def rr : Array Nat := #[
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]

def sl : Array UInt32 := #[
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]

def sr : Array UInt32 := #[
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]

def kl : Array UInt32 := #[0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]
def kr : Array UInt32 := #[0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000]

def rol (x k : UInt32) : UInt32 := (x <<< k) ||| (x >>> (32 - k))

/-- The boolean function of round group `g`. -/
def f (g : Nat) (x y z : UInt32) : UInt32 :=
  match g with
  | 0 => x ^^^ y ^^^ z
  | 1 => (x &&& y) ||| (~~~x &&& z)
  | 2 => (x ||| ~~~y) ^^^ z
  | 3 => (x &&& z) ||| (y &&& ~~~z)
  | _ => x ^^^ (y ||| ~~~z)

/-- The little-endian 32-bit word at byte offset `j`. -/
def word (bs : ByteArray) (j : Nat) : UInt32 :=
  bs[j]!.toUInt32 ||| (bs[j + 1]!.toUInt32 <<< 8) ||| (bs[j + 2]!.toUInt32 <<< 16) |||
    (bs[j + 3]!.toUInt32 <<< 24)

def compress (h : Array UInt32) (bs : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let x := (List.range 16).toArray.map fun i => word bs (off + 4 * i)
  let mut a := h[0]!; let mut b := h[1]!; let mut c := h[2]!; let mut d := h[3]!
  let mut e := h[4]!
  let mut a' := a; let mut b' := b; let mut c' := c; let mut d' := d; let mut e' := e
  for j in [0:80] do
    let t := rol (a + f (j / 16) b c d + x[rl[j]!]! + kl[j / 16]!) sl[j]! + e
    a := e; e := d; d := rol c 10; c := b; b := t
    let t' := rol (a' + f (4 - j / 16) b' c' d' + x[rr[j]!]! + kr[j / 16]!) sr[j]! + e'
    a' := e'; e' := d'; d' := rol c' 10; c' := b'; b' := t'
  return #[h[1]! + c + d', h[2]! + d + e', h[3]! + e + a', h[4]! + a + b', h[0]! + b + c']

def hash (msg : ByteArray) : ByteArray := Id.run do
  let m := msg.push 0x80
  let m := m ++ ByteArray.replicate ((120 - m.size % 64) % 64) 0
  let len := msg.size * 8
  let m := m ++ ByteArray.mk ((List.range 8).toArray.map fun i => (len >>> (8 * i)).toUInt8)
  let mut h : Array UInt32 := #[0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]
  for i in [0:m.size / 64] do
    h := compress h m (64 * i)
  let mut out := ByteArray.empty
  for w in h do
    out := out.push w.toUInt8 |>.push (w >>> 8).toUInt8 |>.push (w >>> 16).toUInt8
      |>.push (w >>> 24).toUInt8
  return out

end RIPEMD160

/-- The P2PKH address of a serialised public key. -/
def p2pkh (pub : ByteArray) : String :=
  base58CheckEncode (ByteArray.mk #[0x00] ++ RIPEMD160.hash (SHA256.hash pub))

/-- Bitcoin Core's `Hash` of a string. -/
def hashString (s : String) : ByteArray := sha256d s.toUTF8

end Tests.Bitcoin
