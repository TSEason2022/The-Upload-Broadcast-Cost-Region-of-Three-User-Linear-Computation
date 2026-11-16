import UploadBroadcast
import UploadBroadcast.IntrinsicUploadInvariance
import UploadBroadcast.OriginalJointReduction
import UploadBroadcast.RegularRelayOptimality
import UploadBroadcast.ActualPairCapacities
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List Name := [`UploadBroadcast.Task.Code.exists_upload_only_decoder,
    `UploadBroadcast.LinearObservation.model_entropy_rank,
    `UploadBroadcast.LinearObservation.model_condEntropy_rank,
    `UploadBroadcast.LinearObservation.model_mutualInfo_rank,
    `UploadBroadcast.general_broadcastOptimum_eq_rankBound,
    `UploadBroadcast.general_block_profile_attained,
    `UploadBroadcast.Task.intrinsic_upload_parameters,
    `UploadBroadcast.Task.minimum_upload_all_choices,
    `UploadBroadcast.Task.PrivateTripodChart.mixedDimension_eq_any_lifts,
    `UploadBroadcast.PassiveRetraction.broadcastOptimum_eq,
    `UploadBroadcast.PassiveRetraction.inducedRelay_map,
    `UploadBroadcast.PassiveRetraction.scalarRelaySelection_of_reduced,
    `UploadBroadcast.Task.scalarRelaySelection_of_canonical,
    `UploadBroadcast.Profile.entry_directSum,
    `UploadBroadcast.Profile.rankBound_directSum_le,
    `UploadBroadcast.FiniteRelayAssembly.entry_task,
    `UploadBroadcast.FiniteRelayAssembly.inducedRelay_entry,
    `UploadBroadcast.ActualPairCapacities.margin_nonneg,
    `UploadBroadcast.ActualPairCapacities.omniscience_margin,
    `UploadBroadcast.OmniscienceProfile.first_entry,
    `UploadBroadcast.OmniscienceProfile.second_entry,
    `UploadBroadcast.OmniscienceProfile.relay_deficits,
    `UploadBroadcast.OmniscienceRelayProfile.entry_preserved,
    `UploadBroadcast.Structural.tits_squares,
    `UploadBroadcast.RootClassification.classification_iff,
    `UploadBroadcast.RootClassification.table_legal_thresholds,
    `UploadBroadcast.BoundaryComponentMenus.T2_permuted_preserving,
    `UploadBroadcast.RegularRelayOptimality.from_actual_chart,
    `UploadBroadcast.ScalarIncidence.projection_lift,
    `UploadBroadcast.ScalarIncidence.projection_mem,
    `UploadBroadcast.Examples.two_instance_achievability,
    `UploadBroadcast.Examples.fixed_relay_broadcast_cost_lower,
    `UploadBroadcast.Examples.fixed_broadcast_cost,
    `UploadBroadcast.BinaryOperationalTightness.broadcastOptimum_eq,
    `UploadBroadcast.BinaryOperationalTightness.scalar_broadcast_cost_strict,
    `UploadBroadcast.Task.uploadOptimum_halfInteger,
    `UploadBroadcast.Task.broadcastOptimum_halfInteger,
    `UploadBroadcast.Task.uploadOptimum_double,
    `UploadBroadcast.Task.broadcastOptimum_double,
    `UploadBroadcast.Task.doubled_optima_integral,
    `UploadBroadcast.Task.costRegion_subset_optimal_rectangle,
    `UploadBroadcast.Task.scalar_joint_requires_integral]
  for n in names do
    match env.find? n with
    | none => throwError "Missing supplemental semantic-review endpoint: {n}"
    | some ci =>
      unless ci.isTheorem do throwError "Not a theorem: {n}"
      logInfo m!"{n} : {ci.type}"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom: {ax}"
  logInfo m!"Supplemental audit passed for {names.length} roots; axioms {state.axioms}"
