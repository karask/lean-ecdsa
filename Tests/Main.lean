import Secp256k1
import Tests.Harness
import Tests.Vectors
import Tests.CT
import Tests.Wycheproof

/-!
# Test suite

Run with `lake test`. Vectors in `Tests/Vectors.lean` come from libsecp256k1
and python-ecdsa (see `scripts/gen_test_vectors.py`); the remaining checks
cover group laws, encodings, rejection of malformed inputs, and the
constant-time arithmetic against the reference implementation (`Tests/CT.lean`).
-/

open Secp256k1 Secp256k1.ECDSA

namespace Tests

/-! ## Hashing -/

def testHashing : TestM Unit := do
  section_ "SHA-256 / HMAC-SHA-256"
  for (msg, digest) in Vectors.sha256 do
    check s!"sha256 {msg.take 16}…" (Hex.encode (SHA256.hash (hex msg)) == digest)
  check "sha256 1M×'a'" <| Hex.encode (SHA256.hash (ByteArray.replicate 1000000 0x61)) ==
    "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
  for (key, msg, mac) in Vectors.hmacSha256 do
    check s!"hmac {key.take 16}…" (Hex.encode (SHA256.hmac (hex key) (hex msg)) == mac)

/-! ## Encodings -/

def testEncodings : TestM Unit := do
  section_ "Byte / hex encodings"
  check "hex roundtrip" (Hex.encode (hex "00ff10ABcd") == "00ff10abcd")
  check "hex odd length" (Hex.decode? "abc").isNone
  check "hex bad digit" (Hex.decode? "zz").isNone
  check "natToBytes pads" (Hex.encode (natToBytes 0x0102 4) == "00000102")
  check "natToBytes truncates" (Hex.encode (natToBytes 0x010203 2) == "0203")
  check "bytesToNat" (bytesToNat (hex "0102") == 0x0102)
  check "minimal bytes of 0" ((natToMinimalBytes 0).size == 0)
  check "minimal bytes of 256" (Hex.encode (natToMinimalBytes 256) == "0100")

/-! ## Curve arithmetic -/

def testCurve : TestM Unit := do
  section_ "Curve arithmetic"
  check "G on curve" G.isOnCurve
  check "0•G = 𝒪" ((0 : Nat) • G == .infinity)
  check "1•G = G" ((1 : Nat) • G == G)
  check "n•G = 𝒪" (n • G == .infinity)
  check "(n-1)•G = -G" ((n - 1) • G == -G)
  check "(n+1)•G = G" ((n + 1) • G == G)
  check "G + -G = 𝒪" (G + -G == .infinity)
  check "G + 𝒪 = G" (G + .infinity == G)
  check "G + G = 2•G" (G + G == (2 : Nat) • G)
  let P := (0xDEADBEEF : Nat) • G
  let Q := (12345678901234567890 : Nat) • G
  check "P + Q = Q + P" (P + Q == Q + P)
  check "(P + Q) + G = P + (Q + G)" ((P + Q) + G == P + (Q + G))
  check "a•G + b•G = (a+b)•G" (P + Q == (0xDEADBEEF + 12345678901234567890 : Nat) • G)
  check "a•(b•G) = (ab)•G" ((3 : Nat) • P == (3 * 0xDEADBEEF : Nat) • G)
  check "smulAdd" (Point.smulAdd 11 P 13 Q == (11 : Nat) • P + (13 : Nat) • Q)
  check "smulAdd with P = Q" (Point.smulAdd 5 P 7 P == (12 : Nat) • P)
  check "smulAdd cancelling" (Point.smulAdd 5 P (n - 5) P == .infinity)
  check "results on curve" ((P + Q).isOnCurve && (P - Q).isOnCurve)
  for (k, expected) in Vectors.scalarMul do
    let R := k • G
    check s!"k•G k={k}" (Hex.encode (R.toBytes (compressed := false)) == expected)
    check s!"k•G on curve k={k}" R.isOnCurve

def testPointEncoding : TestM Unit := do
  section_ "SEC 1 point encoding"
  let P := (0xC0FFEE : Nat) • G
  let Q := -P
  for R in [G, -G, P, Q] do
    check "compressed roundtrip" (Point.ofBytes? (R.toBytes) == some R)
    check "uncompressed roundtrip" (Point.ofBytes? (R.toBytes (compressed := false)) == some R)
  check "compressed size" (P.toBytes.size == 33)
  check "uncompressed size" ((P.toBytes (compressed := false)).size == 65)
  let gx := "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"
  check "reject bad prefix" (Point.ofBytes? (hex ("05" ++ gx))).isNone
  check "reject infinity" (Point.ofBytes? (hex "00")).isNone
  check "reject truncated" (Point.ofBytes? (hex ("02" ++ gx.drop 2))).isNone
  -- x = p is out of range.
  check "reject x ≥ p" (Point.ofBytes? (ByteArray.mk #[0x02] ++ natToBytes p 32)).isNone
  -- x = 5: 5³ + 7 = 132 is not a square mod p.
  check "reject x not on curve" (Point.ofBytes? (ByteArray.mk #[0x02] ++ natToBytes 5 32)).isNone
  check "reject point off curve" (Point.ofBytes? (match G with
    | .affine x y => ByteArray.mk #[0x04] ++ natToBytes x.val 32 ++ natToBytes (y.val + 1) 32
    | .infinity => .empty)).isNone

/-! ## ECDSA -/

def testKeys : TestM Unit := do
  section_ "Keys"
  check "priv 0 rejected" (PrivateKey.ofNat? 0).isNone
  check "priv n rejected" (PrivateKey.ofNat? n).isNone
  check "priv n-1 accepted" (PrivateKey.ofNat? (n - 1)).isSome
  check "priv wrong length" (PrivateKey.ofBytes? (natToBytes 1 31)).isNone
  check "priv bytes roundtrip" <|
    ((PrivateKey.ofBytes? (natToBytes 0xABCDEF 32)).map (Hex.encode ·.toBytes)) ==
      some (Hex.encode (natToBytes 0xABCDEF 32))
  check "pub of infinity rejected" (PublicKey.ofPoint? .infinity).isNone

/-- Checks against libsecp256k1 for one `(priv, msg)` vector. -/
def checkLibsecp (priv msgHex pubC pubU sigHex derHex : String) (recId : Nat) : TestM Unit := do
  let tag := s!"[{priv.take 8} / {msgHex.take 8}]"
  let some sk := PrivateKey.ofBytes? (hex priv) | check s!"{tag} private key" false
  let msg := hex msgHex
  let pk := sk.publicKey
  check s!"{tag} pub compressed" (Hex.encode pk.toBytes == pubC)
  check s!"{tag} pub uncompressed" (Hex.encode (pk.toBytes (compressed := false)) == pubU)
  check s!"{tag} pub parse" (PublicKey.ofBytes? (hex pubC) == some pk &&
    PublicKey.ofBytes? (hex pubU) == some pk)
  let some rsig := sk.signRecoverable msg | check s!"{tag} sign" false
  let sig := rsig.sig
  check s!"{tag} compact sig" (Hex.encode sig.toCompact == sigHex)
  check s!"{tag} recovery id" (rsig.recId.val == recId)
  check s!"{tag} DER sig" (Hex.encode sig.toDER == derHex)
  check s!"{tag} DER parse" (Signature.ofDER? (hex derHex) == some sig)
  check s!"{tag} compact parse" (Signature.ofCompact? (hex sigHex) == some sig)
  check s!"{tag} sign = signRecoverable" (sk.sign msg == some sig)
  check s!"{tag} low S" sig.isLowS
  check s!"{tag} verify" (pk.verify msg sig)
  check s!"{tag} verify strict" (pk.verify msg sig (requireLowS := true))
  check s!"{tag} recover" (PublicKey.recover? msg rsig == some pk)
  -- Negative checks.
  check s!"{tag} wrong message" (!pk.verify (msg.push 0) sig)
  check s!"{tag} wrong key" (!((sk.publicKey.point + G) |> PublicKey.ofPoint? |>.any (·.verify msg sig)))
  check s!"{tag} wrong r" (!pk.verify msg { sig with r := (sig.r + 1) % n })
  check s!"{tag} wrong recId" (PublicKey.recover? msg { rsig with recId := rsig.recId + 1 } != some pk)
  let high : Signature := { sig with s := n - sig.s }
  check s!"{tag} high S verifies" (pk.verify msg high)
  check s!"{tag} high S strict reject" (!pk.verify msg high (requireLowS := true))
  check s!"{tag} normalize" (high.normalize == sig)
  check s!"{tag} lowS := false" ((sk.sign msg (lowS := false)).map (·.normalize) == some sig)

def testLibsecp256k1 : TestM Unit := do
  section_ "ECDSA vs libsecp256k1"
  for (priv, msg, pubC, pubU, sig, der, recId) in Vectors.libsecp256k1 do
    checkLibsecp priv msg pubC pubU sig der recId
  section_ "ECDSA with additional data vs libsecp256k1"
  for (priv, msgHex, extra, sigHex, recId) in Vectors.libsecp256k1Extra do
    let some sk := PrivateKey.ofBytes? (hex priv) | check "private key" false
    let msg := hex msgHex
    let rsig := sk.signRecoverable msg (extraEntropy := hex extra)
    check s!"extra sig {priv.take 8}/{msgHex.take 8}" <|
      rsig.map (fun r => (Hex.encode r.sig.toCompact, r.recId.val)) == some (sigHex, recId)
    check s!"extra differs from plain {priv.take 8}/{msgHex.take 8}" <|
      (rsig.map (·.sig)) != sk.sign msg
    check s!"extra verify {priv.take 8}/{msgHex.take 8}" <|
      rsig.any (fun r => sk.publicKey.verify msg r.sig)

def testPythonEcdsa : TestM Unit := do
  section_ "ECDSA vs python-ecdsa (high S, truncated digests, additional data)"
  for (priv, digest, extra, r, s) in Vectors.pythonEcdsa do
    let tag := s!"[{priv.take 8} / {digest.take 8} / {extra.take 4}]"
    let some sk := PrivateKey.ofBytes? (hex priv) | check s!"{tag} private key" false
    let h := hex digest
    let expected : Signature := ⟨bytesToNat (hex r), bytesToNat (hex s)⟩
    let sig := sk.signHash h (lowS := false) (extraEntropy := hex extra)
    check s!"{tag} raw signature" (sig == some expected)
    check s!"{tag} low-S signature" (sk.signHash h (extraEntropy := hex extra) == some expected.normalize)
    check s!"{tag} verify" (sk.publicKey.verifyHash h expected)

def testRejection : TestM Unit := do
  section_ "Rejection of malformed signatures"
  let some sk := PrivateKey.ofNat? 0x1234567890 | check "private key" false
  let pk := sk.publicKey
  let msg := "hello".toUTF8
  let some sig := sk.sign msg | check "sign" false
  check "r = 0" (!pk.verify msg { sig with r := 0 })
  check "s = 0" (!pk.verify msg { sig with s := 0 })
  check "r = n" (!pk.verify msg { sig with r := n })
  check "s = n" (!pk.verify msg { sig with s := n })
  check "r + n" (!pk.verify msg { sig with r := sig.r + n })
  check "s + n" (!pk.verify msg { sig with s := sig.s + n })
  check "recover r = 0" (PublicKey.recover? msg ⟨{ sig with r := 0 }, 0⟩).isNone
  check "compact wrong length" (Signature.ofCompact? (natToBytes 1 63)).isNone
  check "signWithNonce k = 0" (signWithNonce sk 1 CT.Scalar.zero).isNone
  check "scalar k = n rejected" (CT.Scalar.ofBytes? (natToBytes n 32)).isNone
  -- Strict DER (BIP 66).
  let der := sig.toDER
  check "DER roundtrip" (Signature.ofDER? der == some sig)
  check "DER empty" (Signature.ofDER? .empty).isNone
  check "DER trailing byte" (Signature.ofDER? (der.push 0x01)).isNone
  check "DER truncated" (Signature.ofDER? (der.extract 0 (der.size - 1))).isNone
  check "DER wrong tag" (Signature.ofDER? (der.set! 0 0x31)).isNone
  check "DER wrong int tag" (Signature.ofDER? (der.set! 2 0x03)).isNone
  check "DER wrong length" (Signature.ofDER? (der.set! 1 (der[1]! + 1))).isNone
  -- r = 1, s = 1, then variants with negative / non-minimal integers.
  check "DER minimal" (Signature.ofDER? (hex "3006020101020101") == some ⟨1, 1⟩)
  check "DER negative r" (Signature.ofDER? (hex "3006020181020101")).isNone
  check "DER padded r" (Signature.ofDER? (hex "300702020001020101")).isNone
  check "DER padded s" (Signature.ofDER? (hex "300702010102020001")).isNone
  check "DER needed pad" (Signature.ofDER? (hex "300702020081020101") == some ⟨0x81, 1⟩)
  check "DER zero-length r" (Signature.ofDER? (hex "3006020002020101")).isNone
  check "DER S length overruns" (Signature.ofDER? (hex "3006020101020201")).isNone
  check "DER R length overruns" (Signature.ofDER? (hex "3006020501020101")).isNone
  check "DER encode 0x80" (Hex.encode (Signature.toDER ⟨0x80, 0x7f⟩) == "30070202008002017f")

def testRandomKeys : TestM Unit := do
  section_ "Random keys"
  for i in [0:5] do
    let sk ← PrivateKey.generate
    let pk := sk.publicKey
    let msg := s!"message {i}".toUTF8
    let some rsig := sk.signRecoverable msg | check "sign" false
    check s!"random sign/verify {i}" (pk.verify msg rsig.sig (requireLowS := true))
    check s!"random recover {i}" (PublicKey.recover? msg rsig == some pk)
    check s!"random roundtrip {i}" (PublicKey.ofBytes? pk.toBytes == some pk)

end Tests

open Tests in
def main : IO UInt32 := do
  let start ← IO.monoMsNow
  let ((), (passed, failed)) ← (do
      testHashing
      testEncodings
      testCurve
      testPointEncoding
      testKeys
      testLibsecp256k1
      testPythonEcdsa
      testRejection
      testRandomKeys
      testWycheproof
      testConstantTime : TestM Unit).run (0, #[])
  let elapsed := (← IO.monoMsNow) - start
  for name in failed do
    IO.eprintln s!"FAILED: {name}"
  IO.println s!"{passed} passed, {failed.size} failed ({elapsed} ms)"
  return if failed.isEmpty then 0 else 1
