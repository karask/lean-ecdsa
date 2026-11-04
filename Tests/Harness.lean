import Secp256k1

/-! Minimal test harness: counts passed checks and records failed ones. -/

namespace Tests

/-- Number of passed checks and names of failed ones. -/
abbrev TestM := StateT (Nat × Array String) IO

def check (name : String) (ok : Bool) : TestM Unit :=
  modify fun (passed, failed) => if ok then (passed + 1, failed) else (passed, failed.push name)

def hex (s : String) : ByteArray := Secp256k1.Hex.decode! s

def section_ (title : String) : TestM Unit := IO.println s!"• {title}"

end Tests
