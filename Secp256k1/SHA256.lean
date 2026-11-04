import Secp256k1.Bytes

/-!
# SHA-256 and HMAC-SHA-256

A straightforward implementation of SHA-256 (FIPS 180-4) and HMAC (RFC 2104)
on `ByteArray`. These are needed to hash messages and to derive deterministic
nonces as specified in RFC 6979.
-/

namespace Secp256k1.SHA256

/-- Round constants: first 32 bits of the fractional parts of the cube roots
of the first 64 primes. -/
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Initial hash value: first 32 bits of the fractional parts of the square
roots of the first 8 primes. -/
def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Block size in bytes. -/
def blockSize : Nat := 64

/-- Digest size in bytes. -/
def digestSize : Nat := 32

@[inline] private def rotr (x : UInt32) (k : UInt32) : UInt32 :=
  (x >>> k) ||| (x <<< (32 - k))

/-- Message padding: append `0x80`, zeros, and the 64-bit big-endian bit length
so that the total length is a multiple of 64 bytes. -/
def pad (msg : ByteArray) : ByteArray :=
  let m := msg.push 0x80
  let zeros := (120 - m.size % 64) % 64
  m ++ ByteArray.replicate zeros 0 ++ natToBytes (msg.size * 8) 8

/-- The compression function applied to the 64-byte block of `data` starting
at offset `off`. -/
def compress (h : Array UInt32) (data : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for i in [0:16] do
    let j := off + 4 * i
    w := w.push ((data[j]!.toUInt32 <<< 24) ||| (data[j+1]!.toUInt32 <<< 16) |||
                 (data[j+2]!.toUInt32 <<< 8) ||| data[j+3]!.toUInt32)
  for i in [16:64] do
    let w15 := w[i-15]!
    let w2 := w[i-2]!
    let s0 := rotr w15 7 ^^^ rotr w15 18 ^^^ (w15 >>> 3)
    let s1 := rotr w2 17 ^^^ rotr w2 19 ^^^ (w2 >>> 10)
    w := w.push (w[i-16]! + s0 + w[i-7]! + s1)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for i in [0:64] do
    let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ (~~~e &&& g)
    let t1 := hh + S1 + ch + K[i]! + w[i]!
    let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d,
           h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-- SHA-256 digest of `msg` (32 bytes). -/
def hash (msg : ByteArray) : ByteArray :=
  let m := pad msg
  let state := (List.range (m.size / blockSize)).foldl
    (fun st i => compress st m (blockSize * i)) H0
  state.foldl (fun out word => out ++ natToBytes word.toNat 4) .empty

/-- HMAC-SHA-256 (RFC 2104) with the given key and message. -/
def hmac (key msg : ByteArray) : ByteArray :=
  let key := if key.size > blockSize then hash key else key
  let key := key ++ ByteArray.replicate (blockSize - key.size) 0
  let ipad : ByteArray := ⟨key.data.map (· ^^^ 0x36)⟩
  let opad : ByteArray := ⟨key.data.map (· ^^^ 0x5c)⟩
  hash (opad ++ hash (ipad ++ msg))

end Secp256k1.SHA256
