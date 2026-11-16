import UploadBroadcast.SourceMainTheorem
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List Name := [`UploadBroadcast.canonical_scalar_selection,
    `UploadBroadcast.ResidualBackgroundSelectionTheorem.exists_optimal_relay,
    `UploadBroadcast.ResidualBackgroundSelectionTheorem.residual_background_selection,
    `UploadBroadcast.Task.scalar_relay_selection,
    `UploadBroadcast.Task.stable_relay_source,
    `UploadBroadcast.Task.binary_integer_relay,
    `UploadBroadcast.Task.scalar_budget,
    `UploadBroadcast.Task.joint_two,
    `UploadBroadcast.Task.main_region,
    `UploadBroadcast.Task.minimum_linear_blocklength,
    `UploadBroadcast.Task.scalar_joint_iff_integral,
    `UploadBroadcast.nonlinear_uniform_bound_tight]
  for n in names do
    match env.find? n with
    | none => throwError "Missing global source endpoint: {n}"
    | some ci =>
      unless ci.isTheorem do throwError "Not a theorem: {n}"
      logInfo m!"{n} : {ci.type}"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom: {ax}"
  logInfo m!"Independent global source audit passed for {names.length} roots; axioms {state.axioms}"
