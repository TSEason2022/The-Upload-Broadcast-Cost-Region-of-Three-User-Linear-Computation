import UploadBroadcast.CitedEntropyCounterexample
#print axioms UploadBroadcast.FiniteSubspaceCertificate.Space.submodule_join
#print axioms UploadBroadcast.FiniteSubspaceCertificate.Space.submodule_meet
#print axioms UploadBroadcast.FiniteSubspaceCertificate.Space.finrank_eq
#print axioms UploadBroadcast.CitedEntropyCounterexample.side_spanning
#print axioms UploadBroadcast.CitedEntropyCounterexample.side_card
#print axioms UploadBroadcast.CitedEntropyCounterexample.signal_card
#print axioms UploadBroadcast.CitedEntropyCounterexample.all_subset_kernel_cards
#print axioms UploadBroadcast.CitedEntropyCounterexample.all_subset_ranks
#print axioms UploadBroadcast.CitedEntropyCounterexample.all_subset_entropies
#print axioms UploadBroadcast.CitedEntropyCounterexample.all_block_subset_entropies
#print axioms UploadBroadcast.CitedEntropyCounterexample.scalarSource_injective
#print axioms UploadBroadcast.CitedEntropyCounterexample.scalarSource_surjective
#print axioms UploadBroadcast.CitedEntropyCounterexample.scalarSource_uniform
#print axioms UploadBroadcast.CitedEntropyCounterexample.joint_original_coefficients
#print axioms UploadBroadcast.CitedEntropyCounterexample.original_side
#print axioms UploadBroadcast.CitedEntropyCounterexample.original_demand
#print axioms UploadBroadcast.CitedEntropyCounterexample.broadcastOptima
#print axioms UploadBroadcast.CitedEntropyCounterexample.corrected_entropy_counterexample
#print axioms UploadBroadcast.CitedEntropyCounterexample.equal_subset_entropies_distinct_operational_optima

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) =>
    if (`UploadBroadcast).isPrefixOf name && info.isTheorem then some name else none
  if names.isEmpty then throwError "Empty cited-counterexample audit"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom {ax} reachable from cited counterexample"
  logInfo m!"Strict cited-entropy audit passed for {names.length} project theorems."
  logInfo m!"Complete reachable axiom set: {state.axioms}"
