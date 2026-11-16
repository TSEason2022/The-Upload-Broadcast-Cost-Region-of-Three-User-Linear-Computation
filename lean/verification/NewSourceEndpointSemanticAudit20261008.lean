import UploadBroadcast.OriginalUploadTheorem
import UploadBroadcast.ResidualRowPaperEndpoint
import Lean


#check UploadBroadcast.Task.minimum_upload
#print axioms UploadBroadcast.Task.minimum_upload

#check UploadBroadcast.Task.minimum_upload_source_formula
#print axioms UploadBroadcast.Task.minimum_upload_source_formula

#check UploadBroadcast.Task.minimum_upload_attainment
#print axioms UploadBroadcast.Task.minimum_upload_attainment

#check UploadBroadcast.Task.minimum_upload_scalar_of_integral
#print axioms UploadBroadcast.Task.minimum_upload_scalar_of_integral

#check UploadBroadcast.Task.minimum_upload_two_instance
#print axioms UploadBroadcast.Task.minimum_upload_two_instance

#check UploadBroadcast.Task.minimum_upload_closed_lower
#print axioms UploadBroadcast.Task.minimum_upload_closed_lower

#check UploadBroadcast.Task.uploadOmniscienceValue_eq
#print axioms UploadBroadcast.Task.uploadOmniscienceValue_eq

#check UploadBroadcast.Task.preResidual_pairKnown_finrank
#print axioms UploadBroadcast.Task.preResidual_pairKnown_finrank

#check UploadBroadcast.ResidualTaskAssembly.tripodDimension_eq_pure_mixed
#print axioms UploadBroadcast.ResidualTaskAssembly.tripodDimension_eq_pure_mixed

#check UploadBroadcast.ResidualTaskAssembly.tripodDimension_eq_stacked_rank
#print axioms UploadBroadcast.ResidualTaskAssembly.tripodDimension_eq_stacked_rank

#check UploadBroadcast.ResidualTaskAssembly.finalRows_finrank
#print axioms UploadBroadcast.ResidualTaskAssembly.finalRows_finrank

#check UploadBroadcast.Task.pairCanonicalRetraction
#print axioms UploadBroadcast.Task.pairCanonicalRetraction

#check UploadBroadcast.OriginalUpload.reduction
#print axioms UploadBroadcast.OriginalUpload.reduction

#check UploadBroadcast.ConditionedResidualBridges.canonicalResidualGeometry
#print axioms UploadBroadcast.ConditionedResidualBridges.canonicalResidualGeometry

#check UploadBroadcast.ConditionedResidualBridges.canonicalReduction_all_tripod_bridges
#print axioms UploadBroadcast.ConditionedResidualBridges.canonicalReduction_all_tripod_bridges

#check UploadBroadcast.ConditionedResidualBridges.canonicalReduction_conditioned_retained_bounds
#print axioms UploadBroadcast.ConditionedResidualBridges.canonicalReduction_conditioned_retained_bounds

#check UploadBroadcast.GlobalUploadConverse.code_conditioned_retained_rank_bounds
#print axioms UploadBroadcast.GlobalUploadConverse.code_conditioned_retained_rank_bounds

#check UploadBroadcast.ResidualRowShape.exists_exact_row_completion
#print axioms UploadBroadcast.ResidualRowShape.exists_exact_row_completion

#check UploadBroadcast.ResidualRowShape.row_completion_paper
#print axioms UploadBroadcast.ResidualRowShape.row_completion_paper

#check UploadBroadcast.ResidualRowShape.canonicalReduction_scalar_upload_exact
#print axioms UploadBroadcast.ResidualRowShape.canonicalReduction_scalar_upload_exact

#check UploadBroadcast.ResidualTaskAssembly.finalResidual_zero_common
#print axioms UploadBroadcast.ResidualTaskAssembly.finalResidual_zero_common

#check UploadBroadcast.ResidualTaskAssembly.finalResidual_fully_used
#print axioms UploadBroadcast.ResidualTaskAssembly.finalResidual_fully_used

#check UploadBroadcast.ResidualTaskAssembly.canonicalRetraction
#print axioms UploadBroadcast.ResidualTaskAssembly.canonicalRetraction

#check UploadBroadcast.PassiveRetraction.restoreLinear
#print axioms UploadBroadcast.PassiveRetraction.restoreLinear

#check UploadBroadcast.PassiveRetraction.restoreLinear_costs
#print axioms UploadBroadcast.PassiveRetraction.restoreLinear_costs

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List Name := [
    `UploadBroadcast.Task.minimum_upload,
    `UploadBroadcast.Task.minimum_upload_source_formula,
    `UploadBroadcast.Task.minimum_upload_attainment,
    `UploadBroadcast.Task.minimum_upload_scalar_of_integral,
    `UploadBroadcast.Task.minimum_upload_two_instance,
    `UploadBroadcast.Task.minimum_upload_closed_lower,
    `UploadBroadcast.Task.uploadOmniscienceValue_eq,
    `UploadBroadcast.Task.preResidual_pairKnown_finrank,
    `UploadBroadcast.ResidualTaskAssembly.tripodDimension_eq_pure_mixed,
    `UploadBroadcast.ResidualTaskAssembly.tripodDimension_eq_stacked_rank,
    `UploadBroadcast.ResidualTaskAssembly.finalRows_finrank,
    `UploadBroadcast.Task.pairCanonicalRetraction,
    `UploadBroadcast.OriginalUpload.reduction,
    `UploadBroadcast.ConditionedResidualBridges.canonicalResidualGeometry,
    `UploadBroadcast.ConditionedResidualBridges.canonicalReduction_all_tripod_bridges,
    `UploadBroadcast.ConditionedResidualBridges.canonicalReduction_conditioned_retained_bounds,
    `UploadBroadcast.GlobalUploadConverse.code_conditioned_retained_rank_bounds,
    `UploadBroadcast.ResidualRowShape.exists_exact_row_completion,
    `UploadBroadcast.ResidualRowShape.row_completion_paper,
    `UploadBroadcast.ResidualRowShape.canonicalReduction_scalar_upload_exact,
    `UploadBroadcast.ResidualTaskAssembly.finalResidual_zero_common,
    `UploadBroadcast.ResidualTaskAssembly.finalResidual_fully_used,
    `UploadBroadcast.ResidualTaskAssembly.canonicalRetraction,
    `UploadBroadcast.PassiveRetraction.restoreLinear,
    `UploadBroadcast.PassiveRetraction.restoreLinear_costs
  ]
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom {ax} reachable from new source endpoints"
  logInfo m!"Independent new-source-endpoint audit passed for {names.length} roots."
  logInfo m!"Complete reachable axiom set: {state.axioms}"
