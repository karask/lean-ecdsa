import Lean
import Secp256k1

/-!
Checks that every theorem in the `Secp256k1` namespace depends only on Lean's
standard axioms (`propext`, `Classical.choice`, `Quot.sound`): no `sorryAx`,
and no `Lean.ofReduceBool` from `native_decide` or `bv_decide`.

Run with `lake env lean scripts/CheckAxioms.lean`; it fails if any theorem
uses another axiom.
-/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let std := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Array Name) := #[]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if (`Secp256k1).isPrefixOf n && ci matches .thmInfo _ then
      count := count + 1
      let axs ← liftCoreM (Lean.collectAxioms n)
      let extra := axs.filter (fun a => !std.contains a)
      if !extra.isEmpty then bad := bad.push (n, extra)
  if bad.isEmpty then
    logInfo m!"{count} theorems use only propext, Classical.choice and Quot.sound"
  else
    throwError m!"theorems with non-standard axioms: {bad.toList}"
