import UploadBroadcast.UploadParameterDirectSum
import UploadBroadcast.OppositeDemandExample
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List Name := [`UploadBroadcast.ActualBlockGraph.incidence_conjugacy,
    `UploadBroadcast.ActualBlockGraph.graph_conjugacy,
    `UploadBroadcast.ActualBlockGraph.G0_direct_sum,
    `UploadBroadcast.ActualBlockGraph.mixed_rank_additive,
    `UploadBroadcast.ActualBlockGraph.common_rank_additive,
    `UploadBroadcast.ActualBlockGraph.pure_rank_additive,
    `UploadBroadcast.ActualBlockGraph.tripod_rank_additive,
    `UploadBroadcast.UploadParameterDirectSum.retained_private_spaces,
    `UploadBroadcast.UploadParameterDirectSum.private_dimension_additive,
    `UploadBroadcast.UploadParameterDirectSum.arbitrary_chart_ranks,
    `UploadBroadcast.IntrinsicUploadDirectSums.activePairRank_additive,
    `UploadBroadcast.OppositeDemandExample.strict_subadditivity_example]
  for n in names do
    match env.find? n with
    | none => throwError "Missing standalone source endpoint: {n}"
    | some ci =>
      unless ci.isTheorem do throwError "Not a theorem: {n}"
      logInfo m!"{n} : {ci.type}"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom: {ax}"
  logInfo m!"Independent standalone source audit passed for {names.length} roots; axioms {state.axioms}"
