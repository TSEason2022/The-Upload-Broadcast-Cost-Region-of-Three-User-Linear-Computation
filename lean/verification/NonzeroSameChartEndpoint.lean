import UploadBroadcast.NonzeroSameChartPermutations
import Lean

#check UploadBroadcast.NonzeroSameChartOptimality.family_code_lower
#check UploadBroadcast.NonzeroSameChartOptimality.same_chart_full_and_optimal_relay
#check UploadBroadcast.NonzeroSameChartMenus.same_chart_all_menu_choices
#check UploadBroadcast.NonzeroSameChartPermutations.same_chart_all_permuted_choices
#check UploadBroadcast.NonzeroSameChartPermutations.other_families_profile_preserving
#print axioms UploadBroadcast.GeometricUploadConverse.code_lower
#print axioms UploadBroadcast.NonzeroSameChartOptimality.same_chart_full_and_optimal_relay
#print axioms UploadBroadcast.NonzeroSameChartMenus.same_chart_all_menu_choices
#print axioms UploadBroadcast.NonzeroSameChartPermutations.same_chart_all_permuted_choices
#print axioms UploadBroadcast.NonzeroSameChartPermutations.indexed_menu_table
#print axioms UploadBroadcast.NonzeroSameChartPermutations.other_families_profile_preserving
#print axioms UploadBroadcast.NonzeroSameChartPermutations.pathPerm_exhaustive
#print axioms UploadBroadcast.NonzeroSameChartPermutations.indexed_arms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := [`UploadBroadcast.GeometricUploadConverse,
    `UploadBroadcast.NonzeroSameChartOptimality, `UploadBroadcast.NonzeroSameChartMenus,
    `UploadBroadcast.NonzeroSameChartPermutations]
  let names := env.constants.toList.filterMap fun (name, info) =>
    if roots.any (·.isPrefixOf name) && info.isTheorem then some name else none
  if names.isEmpty then throwError "Empty same-chart audit"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom {ax}"
  logInfo m!"All {names.length} same-chart endpoint theorems pass the axiom whitelist: {state.axioms}"
