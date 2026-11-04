import Secp256k1.Bytes
import Secp256k1.Field
import Secp256k1.SHA256
import Secp256k1.Curve
import Secp256k1.RFC6979

/-!
# ECDSA over secp256k1

ECDSA as specified in SEC 1 v2 §4.1, with deterministic nonces (RFC 6979,
HMAC-SHA-256), optional low-S normalisation (BIP 62/146), public key recovery,
and the compact (64-byte) and strict DER (BIP 66) signature encodings.

* `PrivateKey.sign` / `PublicKey.verify` hash the message with SHA-256.
* `PrivateKey.signHash` / `PublicKey.verifyHash` take an already computed
  digest (e.g. a double-SHA-256 Bitcoin sighash).

Signatures produced with the default options are byte-for-byte identical to
those of libsecp256k1's `secp256k1_ecdsa_sign`.
-/

namespace Secp256k1.ECDSA

/-! ## Keys -/

/-- A private key: a scalar `d ∈ [1, n-1]`. -/
structure PrivateKey where
  d : Nat
  isValid : 0 < d ∧ d < n

/-- Private keys are deliberately not printed. -/
instance : Repr PrivateKey := ⟨fun _ _ => "<PrivateKey>"⟩

namespace PrivateKey

/-- A private key from a scalar, if it lies in `[1, n-1]`. -/
def ofNat? (d : Nat) : Option PrivateKey :=
  if h : 0 < d ∧ d < n then some ⟨d, h⟩ else none

/-- A private key from its 32-byte big-endian encoding. -/
def ofBytes? (bs : ByteArray) : Option PrivateKey :=
  if bs.size = 32 then ofNat? (bytesToNat bs) else none

/-- The 32-byte big-endian encoding of the scalar. -/
def toBytes (sk : PrivateKey) : ByteArray := natToBytes sk.d 32

theorem toBytes_size (sk : PrivateKey) : sk.toBytes.size = 32 := by
  simp [toBytes, natToBytes_size]

/-- Generate a private key from `IO.getRandomBytes` by rejection sampling.

Lean only documents `IO.getRandomBytes` as reading a "system entropy
source" and does not guarantee it is cryptographically secure. For keys
protecting real value, obtain 32 bytes from a vetted CSPRNG and use
`ofBytes?`. -/
partial def generate : IO PrivateKey := do
  let bs ← IO.getRandomBytes 32
  match ofBytes? bs with
  | some sk => pure sk
  | none => generate

end PrivateKey

/-- A public key: a point on secp256k1 other than `𝒪`. The invariant is
enforced by the constructor, so verification never has to re-check it. -/
structure PublicKey where
  point : Point
  isValid : point.isValid = true
  deriving DecidableEq

instance : Repr PublicKey := ⟨fun pk _ => repr pk.point⟩

instance : Inhabited PublicKey := ⟨⟨G, G_isValid⟩⟩

namespace PublicKey

/-- A public key from a point, if it is on the curve and not `𝒪`. -/
def ofPoint? (P : Point) : Option PublicKey :=
  if h : P.isValid = true then some ⟨P, h⟩ else none

/-- Parse a SEC 1 encoded public key (33-byte compressed or 65-byte uncompressed). -/
def ofBytes? (bs : ByteArray) : Option PublicKey :=
  Point.ofBytes? bs >>= ofPoint?

/-- SEC 1 encoding (compressed by default). -/
def toBytes (pk : PublicKey) (compressed : Bool := true) : ByteArray :=
  pk.point.toBytes compressed

end PublicKey

/-- The public key `Q = d • G`. -/
def PrivateKey.publicKey (sk : PrivateKey) : PublicKey :=
  match PublicKey.ofPoint? (sk.d • G) with
  | some pk => pk
  | none => panic! "unreachable: d • G is a valid point for d ∈ [1, n-1]"

/-! ## Signatures -/

/-- An ECDSA signature `(r, s)`. Values are not range-checked on construction;
verification rejects anything outside `[1, n-1]`. -/
structure Signature where
  r : Nat
  s : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A signature together with the recovery id needed to recover the signer's
public key: bit 0 is the parity of `R.y`, bit 1 is set if `R.x ≥ n`. -/
structure RecoverableSignature where
  sig : Signature
  recId : Fin 4
  deriving DecidableEq, Repr, Inhabited

namespace Signature

/-- Whether `s ≤ n/2` (the canonical form required by Bitcoin, BIP 146). -/
def isLowS (sig : Signature) : Bool := sig.s ≤ n / 2

/-- Replace `s` by `n - s` if needed so that `s ≤ n/2`. Both forms verify
against the same key and message. -/
def normalize (sig : Signature) : Signature :=
  if sig.isLowS then sig else { sig with s := n - sig.s }

theorem normalize_isLowS (sig : Signature) : sig.normalize.isLowS = true := by
  unfold normalize isLowS
  split <;> simp_all <;> omega

theorem normalize_of_isLowS (sig : Signature) (h : sig.isLowS = true) : sig.normalize = sig := by
  simp [normalize, h]

/-- 64-byte compact encoding `r ‖ s` (each 32 bytes big-endian). -/
def toCompact (sig : Signature) : ByteArray :=
  natToBytes sig.r 32 ++ natToBytes sig.s 32

theorem toCompact_size (sig : Signature) : sig.toCompact.size = 64 := by
  simp [toCompact, natToBytes_size]

/-- Parse the 64-byte compact encoding. -/
def ofCompact? (bs : ByteArray) : Option Signature :=
  if bs.size = 64 then
    some ⟨bytesToNat (bs.extract 0 32), bytesToNat (bs.extract 32 64)⟩
  else none

/-- DER `INTEGER` with minimal two's-complement content. -/
private def derInteger (x : Nat) : ByteArray :=
  let body := natToMinimalBytes x
  let body := if body.size = 0 || body[0]! ≥ 0x80 then ByteArray.mk #[0] ++ body else body
  ByteArray.mk #[0x02, body.size.toUInt8] ++ body

/-- DER encoding `SEQUENCE { INTEGER r, INTEGER s }` (for `r, s < 2²⁵⁶`). -/
def toDER (sig : Signature) : ByteArray :=
  let body := derInteger sig.r ++ derInteger sig.s
  ByteArray.mk #[0x30, body.size.toUInt8] ++ body

/-- Check that `bs[off : off+len]` is a minimally encoded, non-negative DER integer body. -/
private def derIntegerOk (bs : ByteArray) (off len : Nat) : Bool :=
  len ≠ 0 &&
  bs[off]! &&& 0x80 == 0 &&
  !(len > 1 && bs[off]! == 0 && bs[off + 1]! &&& 0x80 == 0)

/-- Parse a strict DER signature, following the rules of BIP 66
(without the trailing sighash byte). -/
def ofDER? (bs : ByteArray) : Option Signature :=
  let size := bs.size
  if size < 8 || size > 72 then none
  else if bs[0]! != 0x30 || bs[1]!.toNat != size - 2 then none
  else
    let lenR := bs[3]!.toNat
    if 5 + lenR ≥ size then none
    else
      let lenS := bs[5 + lenR]!.toNat
      if lenR + lenS + 6 != size then none
      else if bs[2]! != 0x02 || !derIntegerOk bs 4 lenR then none
      else if bs[4 + lenR]! != 0x02 || !derIntegerOk bs (6 + lenR) lenS then none
      else some ⟨bytesToNat (bs.extract 4 (4 + lenR)), bytesToNat (bs.extract (6 + lenR) size)⟩

end Signature

/-- The message representative `e = bits2int(h) mod n` (SEC 1 §4.1.3 step 5). -/
def hashToScalar (h : ByteArray) : Nat := RFC6979.bits2int h % n

/-- Core of the signing algorithm with an explicit nonce `k`. Returns `none` if
`k ∉ [1, n-1]` or if `r = 0` or `s = 0` (in which case a new nonce is needed).

**Never reuse a nonce across different messages**: two signatures with the
same `k` reveal the private key. Prefer `PrivateKey.signHash`. -/
def signWithNonce (sk : PrivateKey) (e k : Nat) (lowS : Bool := true) :
    Option RecoverableSignature :=
  if ¬(0 < k ∧ k < n) then none
  else
    match k • G with
    | .infinity => none
    | .affine x y =>
      let r := x.val % n
      let s : Fn := Fn.inv (Fn.ofNat k) * (Fn.ofNat e + Fn.ofNat r * Fn.ofNat sk.d)
      let recId : Nat := (if y.isOdd then 1 else 0) + (if x.val ≥ n then 2 else 0)
      if r = 0 ∨ s.val = 0 then none
      else
        let (s, recId) :=
          if lowS && s.val > n / 2 then (n - s.val, recId ^^^ 1) else (s.val, recId)
        some ⟨⟨r, s⟩, Fin.ofNat 4 recId⟩

namespace PrivateKey

/-- Sign a message digest, returning the signature and its recovery id.

The nonce is derived deterministically with RFC 6979 (HMAC-SHA-256);
`extraEntropy` is mixed in as RFC 6979 §3.6 additional data. With
`lowS := true` (the default) the result is normalised so that `s ≤ n/2`.

Returns `none` only if 64 consecutive nonce candidates are rejected, which
happens with negligible probability. -/
def signHashRecoverable (sk : PrivateKey) (h : ByteArray) (lowS : Bool := true)
    (extraEntropy : ByteArray := .empty) : Option RecoverableSignature :=
  let e := hashToScalar h
  RFC6979.findNonce (signWithNonce sk e · lowS) 64 (RFC6979.init sk.d h extraEntropy)

/-- Sign a message digest. See `signHashRecoverable`. -/
def signHash (sk : PrivateKey) (h : ByteArray) (lowS : Bool := true)
    (extraEntropy : ByteArray := .empty) : Option Signature :=
  (sk.signHashRecoverable h lowS extraEntropy).map (·.sig)

/-- Sign `SHA-256(msg)`, returning the signature and its recovery id. -/
def signRecoverable (sk : PrivateKey) (msg : ByteArray) (lowS : Bool := true)
    (extraEntropy : ByteArray := .empty) : Option RecoverableSignature :=
  sk.signHashRecoverable (SHA256.hash msg) lowS extraEntropy

/-- Sign `SHA-256(msg)`. -/
def sign (sk : PrivateKey) (msg : ByteArray) (lowS : Bool := true)
    (extraEntropy : ByteArray := .empty) : Option Signature :=
  sk.signHash (SHA256.hash msg) lowS extraEntropy

end PrivateKey

namespace PublicKey

/-- Verify a signature over a message digest (SEC 1 §4.1.4).

Both low-S and high-S signatures are accepted unless `requireLowS := true`,
which matches libsecp256k1's `secp256k1_ecdsa_verify`. -/
def verifyHash (pk : PublicKey) (h : ByteArray) (sig : Signature)
    (requireLowS : Bool := false) : Bool :=
  let ⟨r, s⟩ := sig
  if ¬(0 < r ∧ r < n ∧ 0 < s ∧ s < n) then false
  else if requireLowS && !sig.isLowS then false
  else
    let w := Fn.inv (Fn.ofNat s)
    let u₁ := (Fn.ofNat (hashToScalar h) * w).val
    let u₂ := (Fn.ofNat r * w).val
    match Point.smulAdd u₁ G u₂ pk.point with
    | .infinity => false
    | .affine x _ => x.val % n == r

/-- Verify a signature over `SHA-256(msg)`. -/
def verify (pk : PublicKey) (msg : ByteArray) (sig : Signature)
    (requireLowS : Bool := false) : Bool :=
  pk.verifyHash (SHA256.hash msg) sig requireLowS

/-- Recover the public key that produced a recoverable signature over a
message digest (SEC 1 §4.1.6). -/
def recoverHash? (h : ByteArray) (rsig : RecoverableSignature) : Option PublicKey :=
  let ⟨⟨r, s⟩, recId⟩ := rsig
  if ¬(0 < r ∧ r < n ∧ 0 < s ∧ s < n) then none
  else
    let x := if recId.val ≥ 2 then r + n else r
    if hx : x < p then
      match Point.lift? ⟨x, hx⟩ (recId.val % 2 == 1) with
      | none => none
      | some R =>
        let rInv := Fn.inv (Fn.ofNat r)
        let u₁ := (Fn.ofNat (n - hashToScalar h) * rInv).val
        let u₂ := (Fn.ofNat s * rInv).val
        ofPoint? (Point.smulAdd u₁ G u₂ R)
    else none

/-- Recover the public key from a recoverable signature over `SHA-256(msg)`. -/
def recover? (msg : ByteArray) (rsig : RecoverableSignature) : Option PublicKey :=
  recoverHash? (SHA256.hash msg) rsig

end PublicKey

end Secp256k1.ECDSA
