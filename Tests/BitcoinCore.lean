import Secp256k1
import Tests.Harness
import Tests.BitcoinUtil
import Tests.Vectors

/-!
# Bitcoin Core's key tests

The ECDSA cases of Bitcoin Core's `src/test/key_tests.cpp` (`key_test1`,
`key_signature_tests`), with Bitcoin Core's constants: WIF keys, P2PKH
addresses, and the DER and 65-byte compact signatures of `CKey::Sign` and
`CKey::SignCompact`. `CKey::Sign` is `PrivateKey.signHashLowR`;
`CKey::SignCompact` is `signHashRecoverable` with `toBitcoinCompact`.
Message hashes are Bitcoin Core's `Hash`, i.e. double SHA-256.

Also: low-R signatures of libsecp256k1 driven by Bitcoin Core's grinding loop
(`Vectors.bitcoinCoreLowR`), including keys and messages where grinding takes
several attempts.
-/

open Secp256k1 Secp256k1.ECDSA Tests.Bitcoin

namespace Tests

/-- A Bitcoin Core `CKey`: a private key and whether its public key is
serialised compressed. -/
structure BtcKey where
  sk : PrivateKey
  compressed : Bool

def BtcKey.pub (k : BtcKey) : ByteArray := k.sk.publicKey.toBytes k.compressed

/-- `CPubKey::Verify`: Bitcoin Core verifies DER signatures after normalising
`s`, so high-S signatures are accepted. -/
def btcVerify (pub hash der : ByteArray) : Bool :=
  match PublicKey.ofBytes? pub, Signature.ofDER? der with
  | some pk, some sig => pk.verifyHash hash sig
  | _, _ => false

/-- `CKey::Sign` (low-R grinding, DER). -/
def btcSign (k : BtcKey) (hash : ByteArray) : Option ByteArray :=
  (k.sk.signHashLowR hash).map (·.toDER)

/-- `CKey::SignCompact`. -/
def btcSignCompact (k : BtcKey) (hash : ByteArray) : Option ByteArray :=
  (k.sk.signHashRecoverable hash).map (·.toBitcoinCompact k.compressed)

/-- `CPubKey::RecoverCompact`: the serialised public key. -/
def btcRecoverCompact (hash sig : ByteArray) : Option ByteArray := do
  let (rsig, compressed) ← RecoverableSignature.ofBitcoinCompact? sig
  let pk ← PublicKey.recoverHash? hash rsig
  return pk.toBytes compressed

def strSecret1 := "5HxWvvfubhXpYYpS3tJkw6fq9jE9j18THftkZjHHfmFiWtmAbrj"
def strSecret2 := "5KC4ejrDjv152FGwP386VD1i2NYc5KkfSMyv1nGy1VGDxGHqVY3"
def strSecret1C := "Kwr371tjA9u2rFSMZjTNun2PXXP3WPZu2afRHTcta6KxEUdm1vEw"
def strSecret2C := "L3Hq7a8FEQwJkW1M2GNKDW28546Vp5miewcCzSqUD9kCAXrJdS3g"
def addr1 := "1QFqqMUD55ZV3PJEJZtaKCsQmjLT6JkjvJ"
def addr2 := "1F5y5E5FMc5YzdJtB9hLaUe43GDxEKXENJ"
def addr1C := "1NoJrossxPBKfCHuJXT4HadJrXRE9Fxiqs"
def addr2C := "1CRj2HyM1CXWzHAXLQtiGLyggNT9WQqsDs"
def strAddressBad := "1HV9Lc3sNHZxwj4Zk6fB38tEmBryq2cBiF"

def decodeSecret (s : String) : Option BtcKey :=
  (decodeWIF? s).map fun (sk, c) => ⟨sk, c⟩

/-- The helpers against their own published vectors. -/
def testBitcoinHelpers : TestM Unit := do
  section_ "Test helpers: RIPEMD-160, Base58Check"
  -- RIPEMD-160 reference vectors (Dobbertin, Bosselaers, Preneel).
  for (msg, digest) in [
      ("", "9c1185a5c5e9fc54612808977ee8f548b2258d31"),
      ("a", "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"),
      ("abc", "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"),
      ("message digest", "5d0689ef49d2fae572b881b123a85ffa21595f36"),
      ("abcdefghijklmnopqrstuvwxyz", "f71c27109c692c1b56bbdceb5b9d2865b3708dbc"),
      ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
        "12a053384a9c0c88e405a06c27dcf49ada62eb2b"),
      ("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789",
        "b0e20b6e3116640286ed3a87a5713079b21f5189"),
      (String.join (List.replicate 8 "1234567890"), "9b752e45573d4b39f4dbd3323cab82bf63326bfb")] do
    check s!"ripemd160 {msg.take 16}…" (Hex.encode (RIPEMD160.hash msg.toUTF8) == digest)
  check "ripemd160 1M×'a'" <|
    Hex.encode (RIPEMD160.hash (ByteArray.replicate 1000000 0x61)) ==
      "52783243c1697bdbe16d37f97f68f08325dc1528"
  for s in [strSecret1, strSecret2, strSecret1C, strSecret2C, addr1, addr2C] do
    check s!"base58check roundtrip {s.take 8}…" <|
      (base58CheckDecode? s).map base58CheckEncode == some s
  check "base58check bad checksum" (base58CheckDecode? "1QFqqMUD55ZV3PJEJZtaKCsQmjLT6JkjvK").isNone

/-- `key_test1`. -/
def testKeyTest1 : TestM Unit := do
  section_ "Bitcoin Core key_tests.cpp: key_test1"
  let some key1 := decodeSecret strSecret1 | check "decode strSecret1" false
  let some key2 := decodeSecret strSecret2 | check "decode strSecret2" false
  let some key1C := decodeSecret strSecret1C | check "decode strSecret1C" false
  let some key2C := decodeSecret strSecret2C | check "decode strSecret2C" false
  check "key1 uncompressed" (!key1.compressed)
  check "key2 uncompressed" (!key2.compressed)
  check "key1C compressed" key1C.compressed
  check "key2C compressed" key2C.compressed
  check "bad key rejected" (decodeSecret strAddressBad).isNone
  let keys := [key1, key2, key1C, key2C]
  let pubs := keys.map (·.pub)
  -- VerifyPubKey: each key matches exactly its own serialised public key.
  for (k, i) in keys.zipIdx do
    for (pub, j) in pubs.zipIdx do
      check s!"VerifyPubKey {i} {j}" ((k.pub == pub) == (i == j))
  -- P2PKH addresses.
  for (k, addr) in keys.zip [addr1, addr2, addr1C, addr2C] do
    check s!"address {addr}" (p2pkh k.pub == addr)
  -- Signing and verification on 16 messages.
  let [pub1, pub2, pub1C, pub2C] := pubs | check "pubs" false
  for i in [0:16] do
    let hashMsg := hashString s!"Very secret message {i}: 11"
    let some sign1 := btcSign key1 hashMsg | check s!"sign1 {i}" false
    let some sign2 := btcSign key2 hashMsg | check s!"sign2 {i}" false
    let some sign1C := btcSign key1C hashMsg | check s!"sign1C {i}" false
    let some sign2C := btcSign key2C hashMsg | check s!"sign2C {i}" false
    for (pub, ok1, ok2) in [(pub1, true, false), (pub2, false, true),
        (pub1C, true, false), (pub2C, false, true)] do
      check s!"verify sign1 {i}" (btcVerify pub hashMsg sign1 == ok1)
      check s!"verify sign2 {i}" (btcVerify pub hashMsg sign2 == ok2)
      check s!"verify sign1C {i}" (btcVerify pub hashMsg sign1C == ok1)
      check s!"verify sign2C {i}" (btcVerify pub hashMsg sign2C == ok2)
    -- Compact signatures with key recovery.
    for (k, pub) in keys.zip pubs do
      let some csig := btcSignCompact k hashMsg | check s!"SignCompact {i}" false
      check s!"RecoverCompact {i}" (btcRecoverCompact hashMsg csig == some pub)
  -- Deterministic signing.
  let hashMsg := hashString "Very deterministic message"
  let det1 := "304402205dbbddda71772d95ce91cd2d14b592cfbc1dd0aabd6a394b6c2d377bbe59d31d022014ddda21494a4e221f0824f0b8b924c43fa43c0ad57dccdaa11f81a6bd4582f6"
  let det2 := "3044022052d8a32079c11e79db95af63bb9600c5b04f21a9ca33dc129c2bfa8ac9dc1cd5022061d8ae5e0f6c1a16bde3719c64c2fd70e404b6428ab9a69566962e8771b5944d"
  check "detsig key1" ((btcSign key1 hashMsg).map Hex.encode == some det1)
  check "detsig key1C" ((btcSign key1C hashMsg).map Hex.encode == some det1)
  check "detsig key2" ((btcSign key2 hashMsg).map Hex.encode == some det2)
  check "detsig key2C" ((btcSign key2C hashMsg).map Hex.encode == some det2)
  let cdet1 := "5dbbddda71772d95ce91cd2d14b592cfbc1dd0aabd6a394b6c2d377bbe59d31d14ddda21494a4e221f0824f0b8b924c43fa43c0ad57dccdaa11f81a6bd4582f6"
  let cdet2 := "52d8a32079c11e79db95af63bb9600c5b04f21a9ca33dc129c2bfa8ac9dc1cd561d8ae5e0f6c1a16bde3719c64c2fd70e404b6428ab9a69566962e8771b5944d"
  check "compact detsig key1" ((btcSignCompact key1 hashMsg).map Hex.encode == some ("1c" ++ cdet1))
  check "compact detsig key1C" ((btcSignCompact key1C hashMsg).map Hex.encode == some ("20" ++ cdet1))
  check "compact detsig key2" ((btcSignCompact key2 hashMsg).map Hex.encode == some ("1c" ++ cdet2))
  check "compact detsig key2C" ((btcSignCompact key2C hashMsg).map Hex.encode == some ("20" ++ cdet2))

/-- `key_signature_tests`. -/
def testKeySignatureTests : TestM Unit := do
  section_ "Bitcoin Core key_tests.cpp: key_signature_tests"
  let some key := decodeSecret strSecret1 | check "decode strSecret1" false
  -- `Sign(hash, sig, grind = false, test_case = i)`: RFC 6979 with
  -- `LE32(i) ‖ 0²⁸` as additional data and no grinding. A high R (DER length
  -- byte 0x21 followed by 0x00) appears within 20 tries.
  let msgHash := hashString "A message to be signed"
  let found := (List.range' 1 20).any fun i =>
    match key.sk.signHash msgHash (extraEntropy := PrivateKey.grindEntropy i) with
    | some sig => let der := sig.toDER; der[3]! == 0x21 && der[4]! == 0x00
    | none => false
  check "high R without grinding" found
  -- With grinding: every signature has a low R and at most 70 bytes; some are
  -- shorter than 70 bytes.
  let mut foundSmall := false
  for i in [0:256] do
    let h := hashString s!"A message to be signed{i}"
    match btcSign key h with
    | none => check s!"grind sign {i}" false
    | some der =>
      check s!"low R {i}" (der[3]! ≤ 32 && der.size ≤ 70)
      check s!"grind verify {i}" (btcVerify key.pub h der)
      foundSmall := foundSmall || der.size < 70
  check "some signature shorter than 70 bytes" foundSmall

/-- libsecp256k1 signatures selected by Bitcoin Core's grinding loop. -/
def testGrindVectors : TestM Unit := do
  section_ "Low-R grinding vs libsecp256k1 (Bitcoin Core's loop)"
  for (priv, hash, attempts, der) in Vectors.bitcoinCoreLowR do
    let tag := s!"[{priv.take 8} / {hash.take 8}]"
    let some sk := PrivateKey.ofBytes? (hex priv) | check s!"{tag} key" false
    check s!"{tag} signHashLowR ({attempts} attempts)" <|
      (sk.signHashLowR (hex hash)).map (Hex.encode ·.toDER) == some der
    check s!"{tag} without verifyAfterSign" <|
      (sk.signHashLowR (hex hash) (verifyAfterSign := false)).map (Hex.encode ·.toDER) == some der

def testBitcoinCore : TestM Unit := do
  testBitcoinHelpers
  testKeyTest1
  testKeySignatureTests
  testGrindVectors

end Tests
