import Secp256k1

/-!
# Differential fuzzing driver

Reads one command per line on standard input and prints one result line per
command. Driven by `scripts/fuzz_vs_libsecp256k1.py`, which compares every
answer with libsecp256k1. Arguments are hex; `-` stands for an empty string.

| Command | Output |
| --- | --- |
| `pub <d>` | compressed public key of private key `d`, or `ERR` |
| `sign <d> <h> <extra>` | `<compact sig> <recid>` (RFC 6979, low-S), or `ERR` |
| `verify <pub> <h> <der>` | `1` / `0` (strict DER, low-S required, like libsecp256k1) |
| `recover <h> <compact sig> <recid>` | compressed public key, or `ERR` |
| `parsepub <bytes>` | compressed public key, or `ERR` |
-/

open Secp256k1 Secp256k1.ECDSA

namespace Fuzz

def arg (s : String) : ByteArray := if s == "-" then .empty else Hex.decode! s

def orErr : Option String → String
  | some s => s
  | none => "ERR"

def handle (line : String) : String :=
  match line.splitOn " " with
  | ["pub", d] => orErr <| (PrivateKey.ofBytes? (arg d)).map (Hex.encode ·.publicKey.toBytes)
  | ["sign", d, h, extra] => orErr do
      let sk ← PrivateKey.ofBytes? (arg d)
      let rsig ← sk.signHashRecoverable (arg h) (extraEntropy := arg extra)
      return s!"{Hex.encode rsig.sig.toCompact} {rsig.recId.val}"
  | ["verify", pk, h, der] =>
      match PublicKey.ofBytes? (arg pk), Signature.ofDER? (arg der) with
      | some pk, some sig => if pk.verifyHash (arg h) sig (requireLowS := true) then "1" else "0"
      | _, _ => "0"
  | ["recover", h, sig, recId] => orErr do
      let sig ← Signature.ofCompact? (arg sig)
      let recId ← recId.toNat?
      if hr : recId < 4 then
        let pk ← PublicKey.recoverHash? (arg h) ⟨sig, ⟨recId, hr⟩⟩
        return Hex.encode pk.toBytes
      else none
  | ["parsepub", bs] => orErr <| (PublicKey.ofBytes? (arg bs)).map (Hex.encode ·.toBytes)
  | _ => "BADCMD"

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn (handle (line.replace "\n" ""))
  loop stdin stdout

end Fuzz

def main : IO Unit := do
  Fuzz.loop (← IO.getStdin) (← IO.getStdout)
