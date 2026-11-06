import Secp256k1
import Tests.Harness

/-!
# libsecp256k1's own unit tests

Static vectors and edge cases from libsecp256k1's `src/tests.c` and
`src/modules/recovery/tests_impl.h`, the library Bitcoin Core uses for ECDSA:

* `run_sha256_known_output_tests`, `run_sha256_counter_tests`
* `run_rfc6979_hmac_sha256_tests`: the HMAC-DRBG of RFC 6979 (by
  `RFC6979.init_rel` and `RFC6979.findNonce_eq`, these outputs are also those of
  `RFC6979.Spec`)
* `run_ecdsa_edge_cases`: verification with `r`, `s` or the message at
  boundary values, signing where `s` would be zero, nonce corner cases
* `test_ecdsa_recovery_edge_cases`: recovery with all four recovery ids,
  DER parsing edge cases, every single-byte change of a DER signature

libsecp256k1's internal `secp256k1_ecdsa_sig_verify` takes the message as a
scalar; here it is passed as its 32-byte big-endian encoding.
-/

open Secp256k1 Secp256k1.ECDSA

namespace Tests

private def b32 (x : Nat) : ByteArray := natToBytes x 32

private def invN (x : Nat) : Nat := (Fn.inv (Fn.ofNat x)).val

/-- Verification as libsecp256k1's `secp256k1_ecdsa_sig_verify` (high S accepted). -/
private def sigVerify (pub : String) (r s msg : Nat) : Bool :=
  match PublicKey.ofBytes? (hex pub) with
  | some pk => pk.verifyHash (b32 msg) ⟨r, s⟩
  | none => false

def testLibsecpSha256 : TestM Unit := do
  section_ "libsecp256k1 tests.c: SHA-256 known outputs and counter tests"
  let known : List (String × Nat × String) := [
    ("", 1, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ("abc", 1, "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    ("message digest", 1, "f7846f55cf23e14eebeab5b4e1550cad5b509e3348fbc4efa3a1413d393cb650"),
    ("secure hash algorithm", 1, "f30ceb2bb2829e79e4ca9753d35a8ecc00262d164cc077080295381cbd643f0d"),
    ("SHA256 is considered to be safe", 1,
      "6819d915c73f4d1e77e4e1b52d1fa0f9cf9beaead3939f15874bd988e2a23630"),
    ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", 1,
      "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
    ("For this sample, this 63-byte string will be used as input data", 1,
      "f08a78cbbaee082b052ae0708f32fa1e50c5c421aa772ba5dbb406a2ea6be342"),
    ("This is exactly 64 bytes long, not counting the terminating byte", 1,
      "ab64eff7e88e2e46165e29f2bce41826bd4c7b3552f6b382a9e7d3af47c245f8"),
    ("aaaaa", 200000, "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0")]
  for (input, rep, out) in known do
    let msg := (List.replicate rep input.toUTF8).foldl (· ++ ·) .empty
    check s!"sha256 {input.take 16}…×{rep}" (Hex.encode (SHA256.hash msg) == out)
  -- Counter tests: the compression function from the midstate after
  -- `2^i - 64` bytes (i = 20 … 33), then the final 64-byte message block and the
  -- padding block with the 64-bit length.
  let input := "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno".toUTF8
  let midstates : List (List UInt32 × Nat) := [
    ([0xa2b5c8bb, 0x26c88bb3, 0x2abdc3d2, 0x9def99a3, 0xdfd21a6e, 0x41fe585b, 0x7ef2c440, 0x2b79adda], 0xfffc0),
    ([0xa0d29445, 0x9287de66, 0x76aabd71, 0x41acd765, 0x0c7528b4, 0x84e14906, 0x942faec6, 0xcc5a7b26], 0x1fffc0),
    ([0x50449526, 0xb9f1d657, 0xa0fc13e9, 0x50860f10, 0xa550c431, 0x3fbc97c1, 0x7bbb2d89, 0xdb67bac1], 0x3fffc0),
    ([0x54a6efdc, 0x46762e7b, 0x88bfe73f, 0xbbd149c7, 0x41620c43, 0x1168da7b, 0x2c5960f9, 0xeccffda6], 0x7fffc0),
    ([0x2515a8f5, 0x5faa2977, 0x3a850486, 0xac858cad, 0x7b7276ee, 0x235c0385, 0xc53a157c, 0x7cb3e69c], 0xffffc0),
    ([0x34f39828, 0x409fedb7, 0x4bbdd0fb, 0x3b643634, 0x7806bf2e, 0xe0d1b713, 0xca3f2e1e, 0xe38722c2], 0x1ffffc0),
    ([0x389ef5c5, 0x38c54167, 0x8f5d56ab, 0x582a75cc, 0x8217caef, 0xf10947dd, 0x6a1998a8, 0x048f0b8c], 0x3ffffc0),
    ([0xd6c3f394, 0x0bee43b9, 0x6783f497, 0x29fa9e21, 0x6ce491c1, 0xa81fe45e, 0x2fc3859a, 0x269012d0], 0x7ffffc0),
    ([0x6dd3c526, 0x44d88aa0, 0x806a1bae, 0xfbcc0d32, 0x9d6144f3, 0x9d2bd757, 0x9851a957, 0xb50430ad], 0xfffffc0),
    ([0x2add4021, 0xdfe8a9e6, 0xa56317c6, 0x7a15f5bb, 0x4a48aacd, 0x5d368414, 0x4f00e6f0, 0xd9355023], 0x1fffffc0),
    ([0xb66666b4, 0xdbeac32b, 0x0ea351ae, 0xcba9da46, 0x6278b874, 0x8c508e23, 0xe16ca776, 0x8465bac1], 0x3fffffc0),
    ([0xb6744789, 0x9cce87aa, 0xc4c478b7, 0xf38404d8, 0x2e38ba62, 0xa3f7019b, 0x50458fe7, 0x3047dbec], 0x7fffffc0),
    ([0x8b1297ba, 0xba261a80, 0x2ba1b0dd, 0xfbc67d6d, 0x61072c4e, 0x4b5a2a0f, 0x52872760, 0x2dfeb162], 0xffffffc0),
    ([0x24f33cf7, 0x41ad6583, 0x41c8ff5d, 0xca7ef35f, 0x50395756, 0x021b743e, 0xd7126cd7, 0xd037473a], 0x1ffffffc0)]
  let outputs := [
    "0e83e2c94fb2b82b890692780403485c4844676177a4c7909e92551005fe3915",
    "1d1ed7b8a3a78a79fda005089cebf0ec67079f8e3c0d8ef9755513c1e877f8bb",
    "66956cc9e03965b6b005d1afaff31db9a4da6f20cd3aae64c2dbeef5b88d570e",
    "3cbb1c125e17fd549045a77b616c1dfee6cc7feecfef3335506216702f87c3c9",
    "534da8e71e98738dd9a354a50e592c25436faaa2f521063ec982069498729da7",
    "ef7ee96bd3e5b7414cc8d307529a5a8b4e1e75a41778c836cdf82ed957e3d707",
    "8716fbf9a5f8c4562b48528e2d3085b64c56b5d1169ccf3295ad03e805580676",
    "75038028f2a763221a269c68e058fc73eb42f68616244bbc24f702c83d90e2b0",
    "df490f157b7dbfe0d4cf47c080934a61aa030766b3385dc8c90761fb97102fd8",
    "7719405641adbc59da1ec53714637bfb79e27ab15542994256fe269d0f7e80c6",
    "50e72a0e26442fe2552dc3938ac58658228c0cbfb1d2ca872ae435266fcd055e",
    "e4806fdb3d7dbade503fea003d465964fd581ca1b87d5fac94379ea0c09c938b",
    "2cf3a9f61525807076997df1c32fa331ff92352e8d041333d80ddb4af68c0334",
    "ec12249f35a4298b9e4a95f861af61c566553e3f2a98ea71166b1cd9e409d28e"]
  for ((mid, bytes), out) in midstates.zip outputs do
    let total := bytes + 64
    let padBlock := ByteArray.mk #[0x80] ++ ByteArray.replicate 55 0 ++ natToBytes (total * 8) 8
    let st := SHA256.compress (SHA256.compress mid.toArray input 0) padBlock 0
    let digest := st.foldl (init := ByteArray.empty) fun o w =>
      o.push (w >>> 24).toUInt8 |>.push (w >>> 16).toUInt8 |>.push (w >>> 8).toUInt8 |>.push w.toUInt8
    check s!"sha256 counter {total} bytes" (Hex.encode digest == out)
  -- The first two midstates also as complete messages of 2²⁰ and 2²¹ bytes.
  for (k, out) in [(16384, outputs[0]!), (32768, outputs[1]!)] do
    let msg := (List.replicate k input).foldl (· ++ ·) .empty
    check s!"sha256 of {64 * k} bytes" (Hex.encode (SHA256.hash msg) == out)

/-- The first `k` RFC 6979 candidates of the implementation. -/
private def implCandidates : Nat → RFC6979.State → List ByteArray
  | 0, _ => []
  | k + 1, st => let (T, st) := st.generate; T :: implCandidates k st.reseed

def testLibsecpRFC6979 : TestM Unit := do
  section_ "libsecp256k1 tests.c: RFC 6979 HMAC-DRBG"
  let key1 := "0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f00" ++
    "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a"
  let out1 := ["4fe29525b2086809159acdf0506efb86b0ec932c7ba44256ab321e421e67e9fb",
    "2bf0fff1d3c378a22dc5de1d856522325c65b504491a0cbd01cb8f3aa67ffd4a",
    "f528b410cb541f77000d7afb6c5b53c5c471eab43e466d9ac5190c39c82fd82e"]
  let key2 := "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  let out2 := ["9c236c165b82ae0cd590659e100b6bab3036e7ba8b06749baf6981e16f1a2b95",
    "df471061625bc0ea14b682feee2c9c02f235da04204c1d62a1536c6e17aed7a9",
    "7597887cbd76321f32e30440679a22cf7f8d9d2eac390e581fea091ce202ba94"]
  for (key, out) in [(key1, out1), (key2, out2)] do
    let seed := hex key
    -- The implementation, seeded with x = seed[0:32] and h₁ = seed[32:64]
    -- (here `bits2octets h₁ = h₁`, as h₁ < n).
    let st := RFC6979.init (seed.extract 0 32) (seed.extract 32 64)
    check s!"rfc6979 {key.take 8}…" ((implCandidates 3 st).map Hex.encode == out)
  -- A 65-byte seed (one more zero byte, as additional data) gives other outputs.
  let seed := hex key1
  let st := RFC6979.init (seed.extract 0 32) (seed.extract 32 64) (ByteArray.mk #[0])
  check "rfc6979 65-byte seed differs" <|
    ((implCandidates 3 st).zip out1).all fun (T, o) => Hex.encode T != o

def testLibsecpEdgeCases : TestM Unit := do
  section_ "libsecp256k1 tests.c: run_ecdsa_edge_cases"
  -- R = 𝒪: Q = G, r = 1, s = msg = -1.
  check "recomputed point is infinity" <|
    !(PublicKey.ofPoint? G).any (·.verifyHash (b32 (n - 1)) ⟨1, n - 1⟩)
  -- r = 0 with a key whose x is n.
  let pubModsZero := "02fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141"
  check "pubkey x = n parses" (PublicKey.ofBytes? (hex pubModsZero)).isSome
  check "r = 0 fails" (!sigVerify pubModsZero 0 1 0)
  let pubX1 := "020000000000000000000000000000000000000000000000000000000000000001"
  check "pubkey x = 1 parses" (PublicKey.ofBytes? (hex pubX1)).isSome
  check "s = 0 fails" (!sigVerify pubX1 1 0 0)
  -- Message 0.
  let pubX2 := "020000000000000000000000000000000000000000000000000000000000000002"
  let pubXn2 := "02fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364143"
  for pub in [pubX2, pubXn2] do
    check s!"msg 0 {pub.drop 62}" (sigVerify pub 2 2 0)
    check s!"msg 0 -s {pub.drop 62}" (sigVerify pub 2 (n - 2) 0)
    check s!"msg 0 wrong s {pub.drop 62}" (!sigVerify pub 2 1 0)
  -- Message 1.
  let r1 := 0x000000000000000000000000000000014551231950b75fc4402da1722fc9baeb
  for pub in ["02144e5a58ef5b226fd2e2076a77cf05b41de74a3098278c93e6e63c0bc4737625",
      "028ad537ed73d9401da033d2dcf0afae34cf5f964c73280f92c0f69dd9b2091062"] do
    check s!"msg 1 {pub.drop 62}" (sigVerify pub r1 1 1)
    check s!"msg 1 -s {pub.drop 62}" (sigVerify pub r1 (n - 1) 1)
    check s!"msg 1 wrong s {pub.drop 62}" (!sigVerify pub r1 (invN 2) 1)
  -- Message -1.
  let rm1 := 0x000000000000000000000000000000014551231950b75fc4402da1722fc9baee
  let pubM1 := "03af97ff7d3af6a00294bd9f4b2ed75228db492a65cb1e27579cba7420d51d20f1"
  check "msg -1" (sigVerify pubM1 rm1 1 (n - 1))
  check "msg -1 -s" (sigVerify pubM1 rm1 (n - 1) (n - 1))
  check "msg -1 wrong s" (!sigVerify pubM1 rm1 (invN 3) (n - 1))
  -- r + n overflows p: r = p - n + 1, x(R) = 1.
  check "r + n overflows p" <|
    !sigVerify "0257ad61c8683fcf069919118c0f99b9389f65059ba071babea63205341445dae8"
      0x000000000000000000000000000000014551231950b75fc4402da1722fc9baef 1 0
  -- Signing where s would be zero.
  let some sk1 := PrivateKey.ofNat? 1 | check "key 1" false
  let some k1 := CT.Scalar.ofBytes? (b32 1) | check "nonce 1" false
  let some kn1 := CT.Scalar.ofBytes? (b32 (n - 1)) | check "nonce n-1" false
  let msg := hex "8641998106234453aa5f9d6a3178f4f7b812e00b817a776265dfdd31b93e29a9"
  check "s = 0 with nonce 1" (signWithNonce sk1 (hashToScalar msg) k1).isNone
  check "s = 0 with nonce n-1" (signWithNonce sk1 (hashToScalar msg) kn1).isNone
  let msg' := hex "8641998106234453aa5f9d6a3178f4f7b812e00b817a776265dfdd31b93e29aa"
  check "nonce 1 after changing the message" (signWithNonce sk1 (hashToScalar msg') k1).isSome
  match signWithNonce sk1 (hashToScalar msg') kn1 with
  | some rsig => check "nonce n-1 verifies" (sk1.publicKey.verifyHash msg' rsig.sig)
  | none => check "nonce n-1 after changing the message" false
  -- Nonce function corner cases, without and with 32 zero bytes of extra data.
  check "high key rejected" (PrivateKey.ofBytes? (ByteArray.replicate 32 0xff)).isNone
  check "zero key rejected" (PrivateKey.ofBytes? (ByteArray.replicate 32 0)).isNone
  for extra in [ByteArray.empty, ByteArray.replicate 32 0] do
    let tag := if extra.isEmpty then "no extra" else "zero extra"
    let msg := b32 1
    -- The retry loop reaches the first good value: the candidates 0, 2²⁵⁶ - 1,
    -- 2²⁵⁶ - 2, n and n + 1 are rejected before the first RFC 6979 candidate.
    let accept := fun T => (CT.Scalar.ofBytes? T).bind (signWithNonce sk1 (hashToScalar msg) · true extra)
    let rfc := (implCandidates 1 (RFC6979.init sk1.toBytes msg extra))[0]!
    let retry := [b32 0, b32 (2 ^ 256 - 1), b32 (2 ^ 256 - 2), b32 n, b32 (n + 1), rfc]
    let sig := sk1.signHashRecoverable msg true extra
    check s!"retry reaches first good value ({tag})" (sig.isSome && retry.findSome? accept == sig)
    check s!"deterministic ({tag})" (sk1.signHashRecoverable msg true extra == sig)
    -- Different messages and different keys give different r.
    let mut rs : Array Nat := #[]
    for i in [0:256] do
      let msg := natToBytes (i * 2 ^ 248 + 1) 32
      if let some s := sk1.signHash msg true extra then rs := rs.push s.r
    for i in [0:256] do
      let some sk := PrivateKey.ofNat? (i * 2 ^ 248 + 1) | continue
      if let some s := sk.signHash (b32 2) true extra then rs := rs.push s.r
    let sorted := rs.qsort (· < ·)
    check s!"512 signatures ({tag})" (rs.size == 512)
    check s!"distinct r ({tag})" <|
      (List.range (sorted.size - 1)).all fun i => sorted[i]! != sorted[i + 1]!
  -- Additional data changes the nonce.
  let zeros := ByteArray.replicate 32 0
  check "extra data changes the nonce" <|
    implCandidates 1 (RFC6979.init zeros zeros) != implCandidates 1 (RFC6979.init zeros zeros zeros)

def testLibsecpRecovery : TestM Unit := do
  section_ "libsecp256k1 recovery tests: test_ecdsa_recovery_edge_cases"
  let msg32 := "This is a very secret message...".toUTF8
  let sig64 : Signature :=
    ⟨0x67cb285f9cd194e840d629397af5569662fde44649995963179a7dd17bd23532,
     0x4b1b7df34ce1f68e694ff6f11ac751dd7dd73e387ee4fc866e1be8ecc7dd9557⟩
  let expected : List (Fin 4 × Bool) := [(0, false), (1, true), (2, false), (3, false)]
  for (recId, ok) in expected do
    check s!"sig64 recId {recId}" ((PublicKey.recoverHash? msg32 ⟨sig64, recId⟩).isSome == ok)
  -- (r, s) = (4, 4) recovers with all four recovery ids.
  let sigbder := hex "3006020104020104"
  let sigbderlong := hex ("3026022100fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364145" ++
    "020104")
  let verifyDER (pk : PublicKey) (der : ByteArray) : Bool :=
    match Signature.ofDER? der with
    | some sig => pk.verifyHash msg32 sig (requireLowS := true)
    | none => false
  for recId in [(0 : Fin 4), 1, 2, 3] do
    let some pkb := PublicKey.recoverHash? msg32 ⟨⟨4, 4⟩, recId⟩
      | check s!"(4,4) recId {recId}" false
    check s!"(4,4) DER verifies, recId {recId}" (verifyDER pkb sigbder)
    check s!"(n + 4, 4) fails, recId {recId}" (!verifyDER pkb sigbderlong)
    -- DER parsing: zero-length integers, leading zeros.
    for bad in ["30050200020101", "30050201010200",
        "302502200000000000000000000000000000000000000000000000000000000000000004020104",
        "302502010402200000000000000000000000000000000000000000000000000000000000000004",
        "30260221000000000000000000000000000000000000000000000000000000000000000004020104",
        "30260201040221000000000000000000000000000000000000000000000000000000000000000004"] do
      check s!"DER rejected {bad.take 12}…" (Signature.ofDER? (hex bad)).isNone
    -- 33-byte integers with a non-zero first byte (≥ 2²⁵⁶) never verify.
    -- (`sigbderalt3` and `sigbderalt4` with the first byte of the integer set to 1.)
    for big in ["30260221010000000000000000000000000000000000000000000000000000000000000004020104",
        "30260201040221010000000000000000000000000000000000000000000000000000000000000004"] do
      check s!"DER ≥ 2²⁵⁶ fails {big.take 12}…" (!verifyDER pkb (hex big))
    check s!"damaged s fails, recId {recId}" (!verifyDER pkb (hex "3006020104020105"))
    check "truncated DER (6)" (Signature.ofDER? (sigbder.extract 0 6)).isNone
    check "truncated DER (7)" (Signature.ofDER? (sigbder.extract 0 7)).isNone
    -- Every single-byte change either fails to parse or fails to verify.
    let ok := (List.range 8).all fun i => (List.range 256).all fun c =>
      c == sigbder[i]!.toNat ||
        !verifyDER pkb (sigbder.set! i c.toUInt8)
    check s!"all single-byte changes rejected, recId {recId}" ok
  -- r or s equal to zero.
  let some pkc := PublicKey.recoverHash? msg32 ⟨⟨1, 1⟩, 0⟩ | check "(1,1) recovers" false
  check "(1,1) DER verifies" (verifyDER pkc (hex "3006020101020101"))
  check "r = 0 does not recover" (PublicKey.recoverHash? msg32 ⟨⟨0, 1⟩, 0⟩).isNone
  check "r = 0 does not verify" (!verifyDER pkc (hex "3006020100020101"))
  check "s = 0 does not recover" (PublicKey.recoverHash? msg32 ⟨⟨1, 0⟩, 0⟩).isNone
  check "s = 0 does not verify" (!verifyDER pkc (hex "3006020101020100"))

def testLibsecpUnit : TestM Unit := do
  testLibsecpSha256
  testLibsecpRFC6979
  testLibsecpEdgeCases
  testLibsecpRecovery

end Tests
