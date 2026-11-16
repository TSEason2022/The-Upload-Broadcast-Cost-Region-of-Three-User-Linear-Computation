import UploadBroadcast.CitedEntropyCounterexample
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List Name := [`UploadBroadcast.CitedEntropyCounterexample.joint_original_coefficients,
    `UploadBroadcast.CitedEntropyCounterexample.task_signal_eq,
    `UploadBroadcast.CitedEntropyCounterexample.original_side,
    `UploadBroadcast.CitedEntropyCounterexample.original_demand,
    `UploadBroadcast.CitedEntropyCounterexample.scalarSource_injective,
    `UploadBroadcast.CitedEntropyCounterexample.scalarSource_surjective,
    `UploadBroadcast.CitedEntropyCounterexample.scalarSource_uniform,
    `UploadBroadcast.CitedEntropyCounterexample.all_subset_ranks,
    `UploadBroadcast.CitedEntropyCounterexample.all_subset_entropies,
    `UploadBroadcast.CitedEntropyCounterexample.all_block_subset_entropies,
    `UploadBroadcast.CitedEntropyCounterexample.broadcastOptima,
    `UploadBroadcast.CitedEntropyCounterexample.corrected_entropy_counterexample,
    `UploadBroadcast.CitedEntropyCounterexample.equal_subset_entropies_distinct_operational_optima]
  for n in names do
    match env.find? n with
    | none => throwError "Missing entropy witness endpoint: {n}"
    | some ci =>
      unless ci.isTheorem do throwError "Not a theorem: {n}"
      logInfo m!"{n} : {ci.type}"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom: {ax}"
  logInfo m!"Independent entropy witness audit passed for {names.length} roots; axioms {state.axioms}"
