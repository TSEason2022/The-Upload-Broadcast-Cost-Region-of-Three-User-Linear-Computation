import UploadBroadcast.RegularSubobjectDefect
import Lean

open Lean Elab Command in
run_cmd do
  let targets := #[
    `UploadBroadcast.TaskDecomposition.Task.componentDefect_split,
    `UploadBroadcast.TaskDecomposition.Task.componentDefect_bot,
    `UploadBroadcast.TaskDecomposition.Task.exists_positive_defect_component,
    `UploadBroadcast.TaskDecomposition.Task.componentDefect_top,
    `UploadBroadcast.TaskDecomposition.Task.preserves_onComponent,
    `UploadBroadcast.TaskDecomposition.Task.defect_nonpos_of_injective_preserves]
  let env ← getEnv
  for name in targets do
    unless (env.find? name).isSome do
      throwError "Missing declaration {name}"
    let axioms ← Lean.collectAxioms name
    logInfo m!"{name}: {axioms}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved axiom {ax} in {name}"
  logInfo m!"Axiom audit passed for {targets.size} subobject-defect theorems."
