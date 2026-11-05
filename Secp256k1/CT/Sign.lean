import Secp256k1.CT.Point
import Secp256k1.SHA256

/-!
# Constant-time ECDSA signing core

The part of ECDSA signing that touches the private key `d` and the nonce
`k`, as a single function with no secret-dependent branches:

  `R = k • G`, `r = R.x mod n`, `s = k⁻¹ · (e + r·d) mod n`,

together with the recovery id and a success flag, all as constant-time values.
`k • G` uses randomised projective coordinates and a randomised scalar
(`PPoint.smulGBlind`), and `s`
is computed with multiplicative blinding as `(k·b)⁻¹ · (e·b + r·(d·b))`, with
blinding factors derived from `k` by HMAC-SHA-256.
The caller then declassifies the outputs, which are published as the
signature anyway.
-/

namespace Secp256k1.CT

/-- A secret blinding factor for the projective coordinates, derived
deterministically from a secret scalar with HMAC-SHA-256 (so signatures stay
deterministic). Unknown to an observer who does not know the scalar. -/
def blindingFactor (s : Scalar) (tag : ByteArray) : Fe := Fe.ofBytes (SHA256.hmac s.toBytes tag)

/-- A secret 32-bit word derived from a secret scalar with HMAC-SHA-256, for
scalar blinding (`k + m·n`). -/
def blindingWord (s : Scalar) (tag : ByteArray) : UInt64 :=
  (U256.ofBytes (SHA256.hmac s.toBytes tag)).l0

/-- Domain separation for the scalar blinding of the nonce. -/
def nonceWordTag : ByteArray := "secp256k1-lean/blind/nonce-scalar".toUTF8

/-- Domain separation for the scalar blinding of the private key. -/
def keyWordTag : ByteArray := "secp256k1-lean/blind/key-scalar".toUTF8

/-- Domain separation for the nonce's blinding factor. -/
def nonceBlindTag : ByteArray := "secp256k1-lean/blind/nonce".toUTF8

/-- Domain separation for the private key's blinding factor. -/
def keyBlindTag : ByteArray := "secp256k1-lean/blind/key".toUTF8

/-- Domain separation for the multiplicative blinding of `s`. -/
def scalarBlindTag : ByteArray := "secp256k1-lean/blind/s".toUTF8

/-- A secret non-zero scalar derived from `k` (and optional extra randomness
`aux`) with HMAC-SHA-256 (`0` is replaced by `1` in constant time). -/
def blindingScalar (k : Scalar) (aux : ByteArray := .empty) : Scalar :=
  let b := Scalar.ofBytesReduce (SHA256.hmac k.toBytes (scalarBlindTag ++ aux))
  ⟨U256.select (maskOf b.isZero) U256.one b.val⟩

/-- Output of `signCore`. -/
structure SignCore where
  r : Scalar
  s : Scalar
  /-- Bit 0: `R.y` is odd. Bit 1: `R.x ≥ n`. -/
  recId : UInt64
  /-- `1` if `k ≠ 0`, `r ≠ 0` and `s ≠ 0`; otherwise the nonce must be rejected. -/
  ok : UInt64
  deriving Inhabited

/-- ECDSA signing with private key `d`, nonce `k` and message representative
`e`, in constant time. (`k = 0` gives `R = 𝒪`, whose affine coordinates are
`0`, so `r = 0` and `ok = 0`.)

The blinding values are derived from `k` and `aux`. With fresh random `aux`
they differ between signatures even of the same message; the result does not
depend on `aux`. -/
def signCore (d k e : Scalar) (aux : ByteArray := .empty) : SignCore :=
  let (x, y, _) :=
    (PPoint.smulGBlind k (blindingFactor k (nonceBlindTag ++ aux))
      (blindingWord k (nonceWordTag ++ aux))).toAffine
  let xv := x.toU256
  let r := Scalar.reduce xv
  -- Multiplicative blinding: `s = (k·b)⁻¹ · (e·b + r·(d·b)) = k⁻¹ · (e + r·d)`.
  -- The private key is only multiplied by the secret `b`, never directly by
  -- the public, varying `r`.
  let b := blindingScalar k aux
  let s := (k * b).inv * (e * b + r * (d * b))
  let yOdd := y.toU256.l0 &&& 1
  let xHigh := U256.lt xv nMod.m ^^^ 1
  let ok := (k.isZero ||| r.isZero ||| s.isZero) ^^^ 1
  ⟨r, s, yOdd ||| (xHigh <<< 1), ok⟩

end Secp256k1.CT
