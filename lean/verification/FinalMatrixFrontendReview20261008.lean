import UploadBroadcast.MatrixTaskEndpoints
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List Name := [`UploadBroadcast.MatrixFrontend.Data.Code.toTask_upload_range,
    `UploadBroadcast.MatrixFrontend.Data.Code.toTask_broadcast_range,
    `UploadBroadcast.MatrixFrontend.Data.Code.ofTask_uploadCost,
    `UploadBroadcast.MatrixFrontend.Data.Code.ofTask_broadcastCost,
    `UploadBroadcast.MatrixFrontend.Data.achievableAt_eq,
    `UploadBroadcast.MatrixFrontend.Data.code_costs_of_task_eq,
    `UploadBroadcast.MatrixFrontend.Data.linearCode_costs_of_task_eq,
    `UploadBroadcast.MatrixFrontend.Data.normalized_dimensions,
    `UploadBroadcast.MatrixFrontend.Data.normalized_joint_rank,
    `UploadBroadcast.MatrixFrontend.Data.normalized_achievableAt_eq,
    `UploadBroadcast.MatrixFrontend.Data.normalize_code,
    `UploadBroadcast.MatrixFrontend.Data.denormalize_code,
    `UploadBroadcast.MatrixFrontend.Data.normalize_linearCode,
    `UploadBroadcast.MatrixFrontend.Data.denormalize_linearCode,
    `UploadBroadcast.MatrixFrontend.Data.exists_retained_normalization,
    `UploadBroadcast.MatrixFrontend.Data.ambient_achievableAt_eq,
    `UploadBroadcast.MatrixFrontend.Data.ambient_linearCode_nonempty_iff]
  for n in names do
    match env.find? n with
    | none => throwError "Missing matrix semantic endpoint: {n}"
    | some ci =>
      unless ci.isTheorem do throwError "Not a theorem: {n}"
      logInfo m!"{n} : {ci.type}"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom: {ax}"
  logInfo m!"Independent matrix audit passed for {names.length} roots; axioms {state.axioms}"
