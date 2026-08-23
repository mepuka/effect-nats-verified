import EffectNatsSubstrate
import Lean

/-!
Exhaustive axiom census (gate step 3, proof-map §6): every theorem in the `EffectNatsSubstrate`
namespace must rest on at most `propext`, `Classical.choice`, `Quot.sound`. Unlike `Axioms.lean`
(the frozen surface, named one by one), this enumerates the environment, so a new theorem cannot
escape the gate by being left off a list. Run from the package directory:
`lake env lean scripts/AxiomsAll.lean`; fails (non-zero exit) on any offender.
-/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (n, c) in env.constants.toList do
    if (`EffectNatsSubstrate).isPrefixOf n then
      match c with
      | .thmInfo _ =>
        count := count + 1
        let axs ← liftCoreM (collectAxioms n)
        if axs.any (fun a => !allowed.contains a) then bad := bad.push (n, axs)
      | _ => pure ()
  logInfo m!"EffectNatsSubstrate theorems: {count}; non-standard axioms: {bad.size}"
  unless bad.isEmpty do
    throwError m!"theorems with non-standard axioms: {bad}"
