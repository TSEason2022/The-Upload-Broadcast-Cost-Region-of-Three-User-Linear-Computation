import UploadBroadcast.IntrinsicUploadInvariance
import Lean

#check UploadBroadcast.Task.intrinsic_upload_parameters
#check UploadBroadcast.Task.minimum_upload_all_choices
#check UploadBroadcast.Task.pairRank_all_choices
#check UploadBroadcast.Task.ActivePairSelection.postResidualQuotient_mapTask
#check UploadBroadcast.Task.ActivePairSelection.all_rank_choices_independent
#check UploadBroadcast.Task.PrivateTripodChart.dimensions_eq_intrinsic
#check UploadBroadcast.Task.PrivateTripodChart.dimensions_equiv
#check UploadBroadcast.Task.PrivateTripodChart.mixedDimension_eq_any_lifts
#check UploadBroadcast.IntrinsicUploadRanks.quotient_relationRows_eq
#print axioms UploadBroadcast.Task.intrinsic_upload_parameters
#print axioms UploadBroadcast.Task.minimum_upload_all_choices
#print axioms UploadBroadcast.Task.ActivePairSelection.postResidualQuotient_mapTask
#print axioms UploadBroadcast.Task.PrivateTripodChart.dimensions_eq_intrinsic
#print axioms UploadBroadcast.IntrinsicUploadRanks.quotient_relationRows_eq

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) =>
    if (`UploadBroadcast).isPrefixOf name && info.isTheorem then some name else none
  if names.isEmpty then throwError "Empty project theorem audit"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom {ax}"
  logInfo m!"Axiom audit passed for {names.length} imported project theorems."
  logInfo m!"Complete reachable axiom set: {state.axioms}"
