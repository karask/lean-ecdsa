import Secp256k1.Bytes
import Secp256k1.Field
import Secp256k1.SHA256
import Secp256k1.Curve
import Secp256k1.RFC6979
import Secp256k1.CT.Point
import Secp256k1.CT.Sign
import Secp256k1.CT.ParseProofs

/-!
# ECDSA over secp256k1

ECDSA as specified in SEC 1 v2 §4.1, with deterministic nonces (RFC 6979,
HMAC-SHA-256), optional low-S normalisation (BIP 62/146), public key recovery,
and the compact (64-byte) and strict DER (BIP 66) signature encodings.

* `PrivateKey.sign` / `PublicKey.verify` hash the message with SHA-256.
* `PrivateKey.signHash` / `PublicKey.verifyHash` take an already computed
  digest (e.g. a double-SHA-256 Bitcoin sighash).
* `PrivateKey.signHashLowR` signs as Bitcoin Core's `CKey::Sign` (low R), and
  `RecoverableSignature.toBitcoinCompact` is the 65-byte format of
  `CKey::SignCompact`.

Signatures produced with the default options are byte-for-byte identical to
those of libsecp256k1's `secp256k1_ecdsa_sign`.

## Side channels

Operations on secrets (key derivation and signing) use the constant-time
arithmetic of `Secp256k1.CT`: the private key and the nonce are kept as
fixed-width limbs or bytes and never converted to `Nat`, and `k • G` uses
complete formulas with a fixed-window, fixed-length ladder. Values are
converted to `Nat` only once they are public (`R`, `r`, `s`).

Verification and recovery only involve public data and use the faster,
variable-time reference arithmetic of `Secp256k1.Curve`.
-/

namespace Secp256k1.ECDSA

/-! ## Keys -/

/-- A private key: a scalar `d ∈ [1, n-1]`, stored as constant-time limbs.
(`d < n` is the invariant of `CT.Scalar`; `d ≠ 0` is checked on construction.) -/
structure PrivateKey where
  scalar : CT.Scalar
  isNonzero : scalar.isZero = 0
  /-- `32`-bit limbs and value below `n` (a proof, erased at runtime). -/
  valid : scalar.Valid

/-- Private keys are deliberately not printed. -/
instance : Repr PrivateKey := ⟨fun _ _ => "<PrivateKey>"⟩

namespace PrivateKey

/-- A private key from its 32-byte big-endian encoding, if it lies in
`[1, n-1]`. The range check is constant time; only its outcome is revealed. -/
def ofBytes? (bs : ByteArray) : Option PrivateKey :=
  match h : CT.Scalar.ofBytes? bs with
  | none => none
  | some s =>
    if hz : CT.declassify s.isZero = 0 then some ⟨s, hz, CT.Scalar.ofBytes?_valid h⟩ else none

/-- A private key from a natural number, if it lies in `[1, n-1]`.

**Not constant time**: the key passes through `Nat`. Convenient for tests and
examples; prefer `ofBytes?` for real keys. -/
def ofNat? (d : Nat) : Option PrivateKey :=
  if d < n then ofBytes? (natToBytes d 32) else none

/-- The 32-byte big-endian encoding of the scalar. Constant time. -/
def toBytes (sk : PrivateKey) : ByteArray := sk.scalar.toBytes

/-- Generate a private key from `IO.getRandomBytes` by rejection sampling.

In Lean v4.35.0 (the pinned toolchain), `IO.getRandomBytes` reads
`/dev/urandom` on Unix-like systems and calls `BCryptGenRandom` on Windows,
both the operating system's cryptographically secure generator (see
`src/runtime/io.cpp` in the Lean repository). Lean documents this only as a
"system entropy source" and not as a guarantee, so re-check it when changing
toolchains. Unlike `getrandom(2)`, reading `/dev/urandom` does not wait for
the kernel generator to be seeded, which can matter very early in boot on
some systems. -/
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

/-- `P` as a public key, for a point known to be valid. Falls back to `G` (with
a panic message) otherwise, which cannot happen for `d • G` with `d ∈ [1, n-1]`. -/
def PublicKey.ofPointD (P : Point) : PublicKey :=
  match PublicKey.ofPoint? P with
  | some pk => pk
  | none => panic! "unreachable: d • G is a valid point for d ∈ [1, n-1]"

theorem PublicKey.ofPointD_point {P : Point} (h : P.isValid = true) : (ofPointD P).point = P := by
  simp only [ofPointD, ofPoint?, h, ↓reduceDIte]

/-- The public key `Q = d • G`, computed with constant-time scalar multiplication
with randomised projective coordinates and a randomised scalar. -/
def PrivateKey.publicKey (sk : PrivateKey) : PublicKey :=
  PublicKey.ofPointD
    (CT.PPoint.smulGBlind sk.scalar (CT.blindingFactor sk.scalar CT.keyBlindTag)
      (CT.blindingWord sk.scalar CT.keyWordTag)).toPoint

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

/-- The content of a DER `INTEGER`: the minimal big-endian bytes of `x`, with a
`0x00` prefix if they are empty or the top bit is set (two's complement). -/
def derBody (x : Nat) : ByteArray :=
  let body := natToMinimalBytes x
  if body.size = 0 || body[0]! ≥ 0x80 then ByteArray.mk #[0] ++ body else body

/-- DER `INTEGER` with minimal two's-complement content. -/
def derInteger (x : Nat) : ByteArray :=
  let body := derBody x
  ByteArray.mk #[0x02, body.size.toUInt8] ++ body

/-- DER encoding `SEQUENCE { INTEGER r, INTEGER s }` (for `r, s < 2²⁵⁶`). -/
def toDER (sig : Signature) : ByteArray :=
  let body := derInteger sig.r ++ derInteger sig.s
  ByteArray.mk #[0x30, body.size.toUInt8] ++ body

/-- Check that `bs[off : off+len]` is a minimally encoded, non-negative DER integer body. -/
def derIntegerOk (bs : ByteArray) (off len : Nat) : Bool :=
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

namespace RecoverableSignature

/-- The 65-byte encoding of Bitcoin Core's `CKey::SignCompact` (used for
message signing): a header byte `27 + recId`, plus 4 if the signer's public key
is serialised compressed, followed by the compact encoding `r ‖ s`. -/
def toBitcoinCompact (rsig : RecoverableSignature) (compressed : Bool := true) : ByteArray :=
  ByteArray.mk #[(27 + rsig.recId.val + if compressed then 4 else 0).toUInt8] ++
    rsig.sig.toCompact

/-- Parse the encoding of `toBitcoinCompact`: the signature and whether the
signer's key is compressed. Header bytes outside `27 … 34` are rejected. -/
def ofBitcoinCompact? (bs : ByteArray) : Option (RecoverableSignature × Bool) :=
  if bs.size = 65 then
    let hdr := bs[0]!.toNat
    if 27 ≤ hdr ∧ hdr ≤ 34 then
      (Signature.ofCompact? (bs.extract 1 65)).map fun sig =>
        (⟨sig, Fin.ofNat 4 (hdr - 27)⟩, 31 ≤ hdr)
    else none
  else none

end RecoverableSignature

/-- The message representative `e = bits2int(h) mod n` (SEC 1 §4.1.3 step 5). -/
def hashToScalar (h : ByteArray) : Nat := RFC6979.bits2int h % n

/-- Sign with an explicit nonce `k` (and public message representative `e`).
Returns `none` if `k = 0`, or if `r = 0` or `s = 0` (in which case a new nonce
is needed).

Everything involving `d` and `k` happens in `CT.signCore`, without
secret-dependent branches. Its outputs (`r`, `s`, the recovery id and the
success flag) are then declassified, since they are published as the
signature, and only then converted to `Nat`.

`aux` is mixed into the side-channel blinding values only; it does not change
the result.

**Never reuse a nonce across different messages**: two signatures with the
same `k` reveal the private key. Prefer `PrivateKey.signHash`. -/
def signWithNonce (sk : PrivateKey) (e : Nat) (k : CT.Scalar) (lowS : Bool := true)
    (aux : ByteArray := .empty) : Option RecoverableSignature :=
  let core := CT.declassify (CT.signCore sk.scalar k (CT.Scalar.ofNat e) aux)
  if core.ok == 0 then none
  else
    let r := core.r.toNat
    let s := core.s.toNat
    let recId := core.recId.toNat
    let (s, recId) := if lowS && s > n / 2 then (n - s, recId ^^^ 1) else (s, recId)
    some ⟨⟨r, s⟩, Fin.ofNat 4 recId⟩

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

namespace PrivateKey

/-- Sign a message digest, returning the signature and its recovery id.

The nonce is derived deterministically with RFC 6979 (HMAC-SHA-256);
`extraEntropy` is mixed in as RFC 6979 §3.6 additional data, and into the
side-channel blinding values. Fresh random `extraEntropy` ("hedged" signing,
see `signHedged`) makes repeated signatures of the same message use different
nonces and blinding, which helps against fault and power analysis; the
signature is still valid either way. With
`lowS := true` (the default) the result is normalised so that `s ≤ n/2`.

With `verifyAfterSign := true`, the signature is verified against the public
key before it is returned, and `none` is returned if that check fails. This is
a countermeasure against fault attacks: a glitch or bit flip during signing
that yields a wrong signature could otherwise reveal the private key. It
roughly doubles the cost of signing.

Otherwise, returns `none` only if 64 consecutive nonce candidates are
rejected, which happens with negligible probability. -/
def signHashRecoverable (sk : PrivateKey) (h : ByteArray) (lowS : Bool := true)
    (extraEntropy : ByteArray := .empty) (verifyAfterSign : Bool := false) :
    Option RecoverableSignature :=
  let e := hashToScalar h
  let rsig? := RFC6979.findNonce
    (fun T => (CT.Scalar.ofBytes? T).bind (signWithNonce sk e · lowS extraEntropy))
    64 (RFC6979.init sk.toBytes h extraEntropy)
  if verifyAfterSign then rsig?.filter (sk.publicKey.verifyHash h ·.sig) else rsig?

/-- Sign a message digest. See `signHashRecoverable`. -/
def signHash (sk : PrivateKey) (h : ByteArray) (lowS : Bool := true)
    (extraEntropy : ByteArray := .empty) (verifyAfterSign : Bool := false) :
    Option Signature :=
  (sk.signHashRecoverable h lowS extraEntropy verifyAfterSign).map (·.sig)

/-- Sign `SHA-256(msg)`, returning the signature and its recovery id. -/
def signRecoverable (sk : PrivateKey) (msg : ByteArray) (lowS : Bool := true)
    (extraEntropy : ByteArray := .empty) (verifyAfterSign : Bool := false) :
    Option RecoverableSignature :=
  sk.signHashRecoverable (SHA256.hash msg) lowS extraEntropy verifyAfterSign

/-- Sign `SHA-256(msg)`. See `signHashRecoverable`. -/
def sign (sk : PrivateKey) (msg : ByteArray) (lowS : Bool := true)
    (extraEntropy : ByteArray := .empty) (verifyAfterSign : Bool := false) :
    Option Signature :=
  sk.signHash (SHA256.hash msg) lowS extraEntropy verifyAfterSign

/-- Hedged signing of a message digest: 32 bytes from `IO.getRandomBytes` are
used as `extraEntropy`, so the nonce and all blinding values are fresh for every
call (and the result still verifies, by `Secp256k1Proofs.verify_sign`).
Verification after signing is on by default. -/
def signHashHedged (sk : PrivateKey) (h : ByteArray) (lowS : Bool := true)
    (verifyAfterSign : Bool := true) : IO (Option Signature) := do
  let aux ← IO.getRandomBytes 32
  return sk.signHash h lowS aux verifyAfterSign

/-- Hedged signing of `SHA-256(msg)`. See `signHashHedged`. -/
def signHedged (sk : PrivateKey) (msg : ByteArray) (lowS : Bool := true)
    (verifyAfterSign : Bool := true) : IO (Option Signature) :=
  sk.signHashHedged (SHA256.hash msg) lowS verifyAfterSign

/-- The additional data of attempt `counter` in Bitcoin Core's low-R grinding:
`counter` as a 32-bit little-endian integer, followed by 28 zero bytes. -/
def grindEntropy (counter : Nat) : ByteArray :=
  ByteArray.mk #[counter.toUInt8, (counter >>> 8).toUInt8, (counter >>> 16).toUInt8,
    (counter >>> 24).toUInt8] ++ ByteArray.replicate 28 0

/-- The grinding loop of `signHashLowR`, from attempt `counter` on, for at most
`fuel` attempts. Attempt `0` uses no additional data. -/
def grindLowR (sk : PrivateKey) (h : ByteArray) (counter : Nat) : Nat → Option Signature
  | 0 => none
  | fuel + 1 =>
    match sk.signHash h true (if counter = 0 then .empty else grindEntropy counter) with
    | none => none
    | some sig => if sig.r < 2 ^ 255 then some sig else sk.grindLowR h (counter + 1) fuel

/-- Sign a message digest as Bitcoin Core's `CKey::Sign` does: low-S, and
ground for a low `r` (`r < 2²⁵⁵`), which keeps the DER encoding at most 70 bytes
(`signHashLowR_toDER_size`). The first attempt is plain RFC 6979 (`signHash`); while
`r ≥ 2²⁵⁵`, attempt `i = 1, 2, …` uses `grindEntropy i` as `extraEntropy`.
Each attempt succeeds with probability about 1/2; after 256 failures the result
is `none`.

The number of attempts reveals only the top bit of `r` of discarded
signatures. With `verifyAfterSign := true` (the default, as in Bitcoin Core) the
result is verified before it is returned. -/
def signHashLowR (sk : PrivateKey) (h : ByteArray) (verifyAfterSign : Bool := true) :
    Option Signature :=
  let sig? := sk.grindLowR h 0 256
  if verifyAfterSign then sig?.filter (sk.publicKey.verifyHash h) else sig?

end PrivateKey


end Secp256k1.ECDSA
