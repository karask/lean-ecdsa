import Secp256k1.CT.Point
import Secp256k1.SHA256

/-!
# Constant-time ECDSA signing core

The part of ECDSA signing that touches the private key `d` and the nonce
`k`, as a single function with no secret-dependent branches:

  `R = k • G`, `r = R.x mod n`, `s = k⁻¹ · (e + r·d) mod n`,

together with the recovery id and a success flag, all as constant-time values.
`k • G` uses randomised projective coordinates (`PPoint.smulGBlind`), with a
blinding factor derived from `k` by HMAC-SHA-256.
The caller then declassifies the outputs, which are published as the
signature anyway.
-/

namespace Secp256k1.CT

/-- A secret blinding factor for the projective coordinates, derived
deterministically from a secret scalar with HMAC-SHA-256 (so signatures stay
deterministic). Unknown to an observer who does not know the scalar. -/
def blindingFactor (s : Scalar) (tag : ByteArray) : Fe := Fe.ofBytes (SHA256.hmac s.toBytes tag)

/-- Domain separation for the nonce's blinding factor. -/
def nonceBlindTag : ByteArray := "secp256k1-lean/blind/nonce".toUTF8

/-- Domain separation for the private key's blinding factor. -/
def keyBlindTag : ByteArray := "secp256k1-lean/blind/key".toUTF8

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
`0`, so `r = 0` and `ok = 0`.) -/
def signCore (d k e : Scalar) : SignCore :=
  let (x, y, _) := (PPoint.smulGBlind k (blindingFactor k nonceBlindTag)).toAffine
  let xv := x.toU256
  let r := Scalar.reduce xv
  let s := k.inv * (e + r * d)
  let yOdd := y.toU256.l0 &&& 1
  let xHigh := U256.lt xv nMod.m ^^^ 1
  let ok := (k.isZero ||| r.isZero ||| s.isZero) ^^^ 1
  ⟨r, s, yOdd ||| (xHigh <<< 1), ok⟩

end Secp256k1.CT
