import UploadBroadcast.ConditionedResidualBridges
import Lean
#print axioms UploadBroadcast.ConditionedResidualBridges.canonicalReduction_all_tripod_bridges
#print axioms UploadBroadcast.ConditionedResidualBridges.canonicalReduction_conditioned_retained_bounds
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) =>
    if ((`UploadBroadcast.ConditionedResidualBridges).isPrefixOf name ||
        (`UploadBroadcast.GlobalUploadConverse).isPrefixOf name ||
        (`UploadBroadcast.GlobalUploadGeometry).isPrefixOf name) && info.isTheorem then some name else none
  if names.isEmpty then throwError "No conditioned-bridge theorems found"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom {ax} reachable from conditioned-bridge theorems"
  logInfo m!"Conditioned-bridge axiom audit passed for {names.length} theorems."
  logInfo m!"Complete reachable axiom set: {state.axioms}"
