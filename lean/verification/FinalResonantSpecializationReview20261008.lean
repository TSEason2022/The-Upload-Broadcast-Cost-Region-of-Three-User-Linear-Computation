import UploadBroadcast.ResonantUploadSpecializations
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List Name := [`UploadBroadcast.ResonantUploadSpecializations.jordan_active,
    `UploadBroadcast.ResonantUploadSpecializations.jordan_uploadOptimum,
    `UploadBroadcast.ResonantUploadSpecializations.source_uploadOptimum,
    `UploadBroadcast.ResonantUploadSpecializations.map_scalarCoordinates,
    `UploadBroadcast.ResonantUploadSpecializations.binary_active,
    `UploadBroadcast.ResonantUploadSpecializations.binary_uploadOptimum,
    `UploadBroadcast.ResonantUploadSpecializations.binary_joint_two]
  for n in names do
    match env.find? n with
    | none => throwError "Missing resonant source endpoint: {n}"
    | some ci =>
      unless ci.isTheorem do throwError "Not a theorem: {n}"
      logInfo m!"{n} : {ci.type}"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom: {ax}"
  logInfo m!"Independent resonant specialization audit passed for {names.length} roots; axioms {state.axioms}"
