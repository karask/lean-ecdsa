import Lean.Data.Json
import Secp256k1
import Tests.Harness

/-!
# Project Wycheproof vectors

Runs the secp256k1 ECDSA verification vectors in `Tests/wycheproof/`
(adversarial edge cases: malformed and BER encodings, out-of-range and
modified integers, special-case hashes and public keys, arithmetic edge cases
of the double scalar multiplication). Every test's verdict must match the
expected `"valid"` / `"invalid"` result.
-/

open Lean (Json)
open Secp256k1 Secp256k1.ECDSA

namespace Tests

inductive SigFormat where
  | der
  | p1363

structure WycheproofFile where
  name : String
  format : SigFormat
  requireLowS : Bool

def wycheproofFiles : List WycheproofFile := [
  ⟨"ecdsa_secp256k1_sha256_test.json", .der, false⟩,
  ⟨"ecdsa_secp256k1_sha256_bitcoin_test.json", .der, true⟩,
  ⟨"ecdsa_secp256k1_sha256_p1363_test.json", .p1363, false⟩]

/-- Run one Wycheproof file. Returns `(tests run, tests listed in the header)`. -/
def runWycheproofFile (f : WycheproofFile) : TestM (Nat × Nat) := do
  let path := s!"Tests/wycheproof/{f.name}"
  let contents ← try IO.FS.readFile path catch _ => pure ""
  let .ok json := Json.parse contents | check s!"{f.name}: read and parse {path}" false; pure (0, 1)
  let expected := (json.getObjValAs? Nat "numberOfTests").toOption.getD 0
  let .ok groups := (json.getObjValD "testGroups").getArr? | check s!"{f.name}: groups" false; pure (0, 1)
  let mut count := 0
  for g in groups do
    let pkHex := ((g.getObjValD "publicKey").getObjValAs? String "uncompressed").toOption.getD ""
    let pk? := PublicKey.ofBytes? (hex pkHex)
    check s!"{f.name}: public key {pkHex.take 16}… parses" pk?.isSome
    let tests := ((g.getObjValD "tests").getArr?).toOption.getD #[]
    for t in tests do
      let field (k : String) : String := (t.getObjValAs? String k).toOption.getD ""
      let tcId := (t.getObjValAs? Nat "tcId").toOption.getD 0
      let result := field "result"
      let sigBytes := hex (field "sig")
      let sig? := match f.format with
        | .der => Signature.ofDER? sigBytes
        | .p1363 => Signature.ofCompact? sigBytes
      let accepted := match pk?, sig? with
        | some pk, some sig => pk.verify (hex (field "msg")) sig (requireLowS := f.requireLowS)
        | _, _ => false
      check s!"{f.name} #{tcId} ({result}: {field "comment"})" (accepted == (result == "valid"))
      count := count + 1
  check s!"{f.name}: all {expected} tests run" (count == expected && expected > 0)
  return (count, expected)

def testWycheproof : TestM Unit := do
  section_ "Project Wycheproof (DER, Bitcoin low-S, P1363)"
  for f in wycheproofFiles do
    let (count, _) ← runWycheproofFile f
    IO.println s!"    {f.name}: {count} vectors"

end Tests
