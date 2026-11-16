import UploadBroadcast.CycleSourceEndpoint
import Lean

#print UploadBroadcast.CycleSourceEndpoint.Repair

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List Name := [`UploadBroadcast.CycleUploadOptimality.canonical_active,
    `UploadBroadcast.CycleUploadOptimality.canonical_reverse_active,
    `UploadBroadcast.CycleUploadOptimality.canonical_positive_optimal,
    `UploadBroadcast.CycleUploadOptimality.canonical_reverse_optimal,
    `UploadBroadcast.CycleSourceEndpoint.positive_canonical,
    `UploadBroadcast.CycleSourceEndpoint.negative_canonical,
    `UploadBroadcast.CycleSourceEndpoint.positive_directSum,
    `UploadBroadcast.CycleSourceEndpoint.negative_directSum]
  for n in names do
    match env.find? n with
    | none => throwError "Missing cycle source endpoint: {n}"
    | some ci =>
      unless ci.isTheorem do throwError "Not a theorem: {n}"
      logInfo m!"{n} : {ci.type}"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom: {ax}"
  logInfo m!"Independent cycle source audit passed for {names.length} roots; axioms {state.axioms}"
