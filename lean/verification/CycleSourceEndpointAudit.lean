import UploadBroadcast.CycleSourceEndpoint
import Lean

#print axioms UploadBroadcast.CycleUploadOptimality.task_active
#print axioms UploadBroadcast.CycleUploadOptimality.canonical_active
#print axioms UploadBroadcast.CycleUploadOptimality.canonical_reverse_active
#print axioms UploadBroadcast.CycleUploadOptimality.canonical_positive_optimal
#print axioms UploadBroadcast.CycleUploadOptimality.canonical_reverse_optimal
#print axioms UploadBroadcast.CycleSourceEndpoint.positive_directSum
#print axioms UploadBroadcast.CycleSourceEndpoint.negative_directSum

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) =>
    if (`UploadBroadcast).isPrefixOf name && info.isTheorem then some name else none
  if names.isEmpty then throwError "Empty project audit"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom {ax}"
  logInfo m!"Demand-cycle source audit passed for {names.length} imported project theorems."
  logInfo m!"Complete reachable axiom set: {state.axioms}"
