import Secp256k1.CT.Point

/-!
# Constant-time ECDSA signing core

The part of ECDSA signing that touches the private key `d` and the nonce
`k`, as a single function with no secret-dependent branches:

  `R = k • G`, `r = R.x mod n`, `s = k⁻¹ · (e + r·d) mod n`,

together with the recovery id and a success flag, all as constant-time values.
The caller then declassifies the outputs, which are published as the
signature anyway.
-/

namespace Secp256k1.CT

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
  let (x, y, _) := (PPoint.smulG k).toAffine
  let xv := x.toU256
  let r := Scalar.reduce xv
  let s := k.inv * (e + r * d)
  let yOdd := y.toU256.l0 &&& 1
  let xHigh := U256.lt xv nMod.m ^^^ 1
  let ok := (k.isZero ||| r.isZero ||| s.isZero) ^^^ 1
  ⟨r, s, yOdd ||| (xHigh <<< 1), ok⟩

end Secp256k1.CT
