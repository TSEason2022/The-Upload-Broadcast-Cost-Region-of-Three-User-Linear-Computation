import UploadBroadcast.CitedBinaryFieldNecessity
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List Name := [`UploadBroadcast.CitedBinaryFieldNecessity.signal_from_demands,
    `UploadBroadcast.CitedBinaryFieldNecessity.broadcastOptimum_eq_one,
    `UploadBroadcast.CitedBinaryFieldNecessity.broadcast_source_injective,
    `UploadBroadcast.CitedBinaryFieldNecessity.scalar_broadcast_card,
    `UploadBroadcast.CitedBinaryFieldNecessity.scalar_cost_ge_two,
    `UploadBroadcast.CitedBinaryFieldNecessity.scalar_cost_gt_ceiling]
  for n in names do
    match env.find? n with
    | none => throwError "Missing binary witness endpoint: {n}"
    | some ci => logInfo m!"{n} : {ci.type}"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom: {ax}"
  logInfo m!"Independent binary necessity audit passed for {names.length} roots; axioms {state.axioms}"
