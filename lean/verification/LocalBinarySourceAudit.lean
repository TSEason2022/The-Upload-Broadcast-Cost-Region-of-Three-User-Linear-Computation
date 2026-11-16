import UploadBroadcast.BinaryAdditionalMenuPermutations
import UploadBroadcast.ResidualProfiles
import Lean

#print axioms UploadBroadcast.BinaryMenuPermutations.original_exact_optimal_permuted
#print axioms UploadBroadcast.BinaryMenuOptimality.charge_le_actual_margin
#print axioms UploadBroadcast.BinaryMenuOptimality.r2_charge_le_actual_margin
#print axioms UploadBroadcast.BinaryAdditionalMenuPermutations.additional_optimal_permuted
#print axioms UploadBroadcast.BinaryAdditionalMenuPermutations.additional_fits_permuted
#print axioms UploadBroadcast.BinaryAdditionalMenuPermutations.r2_optimal_permuted
#print axioms UploadBroadcast.BinaryAdditionalMenuPermutations.r2_fits_permuted
#print axioms UploadBroadcast.BinaryAdditionalMenuPermutations.exceptions_permuted
#print axioms UploadBroadcast.BoundaryComponentMenus.T1_all_permuted_choices
#print axioms UploadBroadcast.RegularExactMenus.from_actual_regular
#print axioms UploadBroadcast.ResidualProfiles.profiles

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
  logInfo m!"Local binary source audit passed for {names.length} imported project theorems."
  logInfo m!"Complete reachable axiom set: {state.axioms}"
