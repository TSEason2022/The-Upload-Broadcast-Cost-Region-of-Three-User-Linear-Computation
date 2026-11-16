import UploadBroadcast.NonzeroDefectRelays
import UploadBroadcast.NonzeroDefectProfile
import Lean

/-! Traverse the union of all project theorem dependencies with Lean's own
axiom collector, sharing its visited set across roots. This is equivalent to
whitelisting each separate dependency set, without repeatedly traversing the
same mathlib/PFR proofs thousands of times. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) =>
    if ((`UploadBroadcast.NonzeroDefectRelays).isPrefixOf name ||
        (`UploadBroadcast.NonzeroDefectProfile).isPrefixOf name) && info.isTheorem then some name else none
  if names.isEmpty then
    throwError "No UploadBroadcast theorems found; refusing an empty audit"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom {ax} reachable from project theorems"
  logInfo m!"Axiom audit passed for {names.length} project theorems."
  logInfo m!"Complete reachable axiom set: {state.axioms}"
