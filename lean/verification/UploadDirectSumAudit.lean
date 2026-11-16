import UploadBroadcast.UploadParameterDirectSum
import Lean

#check UploadBroadcast.ActualBlockGraph.combinedTask
#check UploadBroadcast.ActualBlockGraph.combinedData
#check UploadBroadcast.ActualBlockGraph.incidence_conjugacy
#check UploadBroadcast.ActualBlockGraph.graph_conjugacy
#check UploadBroadcast.ActualBlockGraph.G0_direct_sum
#check UploadBroadcast.ActualBlockGraph.mixed_rank_additive
#check UploadBroadcast.ActualBlockGraph.common_rank_additive
#check UploadBroadcast.ActualBlockGraph.pure_rank_additive
#check UploadBroadcast.ActualBlockGraph.tripod_rank_additive
#check UploadBroadcast.UploadParameterDirectSum.private_dimension_additive
#check UploadBroadcast.UploadParameterDirectSum.arbitrary_chart_ranks
#check UploadBroadcast.IntrinsicUploadDirectSums.activePairRank_additive
#print axioms UploadBroadcast.ActualBlockGraph.G0_direct_sum
#print axioms UploadBroadcast.ActualBlockGraph.mixed_rank_additive
#print axioms UploadBroadcast.ActualBlockGraph.tripod_rank_additive
#print axioms UploadBroadcast.UploadParameterDirectSum.private_dimension_additive
#print axioms UploadBroadcast.IntrinsicUploadDirectSums.activePairRank_additive

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
