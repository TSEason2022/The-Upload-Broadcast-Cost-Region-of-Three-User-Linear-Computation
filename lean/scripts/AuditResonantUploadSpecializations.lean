import UploadBroadcast.ResonantUploadSpecializations
import Lean

#check UploadBroadcast.ResonantUploadSpecializations.jordan_active
#check UploadBroadcast.ResonantUploadSpecializations.jordan_uploadOptimum
#check UploadBroadcast.ResonantUploadSpecializations.source_uploadOptimum
#check UploadBroadcast.ResonantUploadSpecializations.map_scalarCoordinates
#check UploadBroadcast.ResonantUploadSpecializations.binary_active
#check UploadBroadcast.ResonantUploadSpecializations.binary_uploadOptimum
#check UploadBroadcast.ResonantUploadSpecializations.binary_joint_two
#print axioms UploadBroadcast.ResonantUploadSpecializations.jordan_active
#print axioms UploadBroadcast.ResonantUploadSpecializations.jordan_uploadOptimum
#print axioms UploadBroadcast.ResonantUploadSpecializations.source_uploadOptimum
#print axioms UploadBroadcast.ResonantUploadSpecializations.map_scalarCoordinates
#print axioms UploadBroadcast.ResonantUploadSpecializations.binary_active
#print axioms UploadBroadcast.ResonantUploadSpecializations.binary_uploadOptimum
#print axioms UploadBroadcast.ResonantUploadSpecializations.binary_joint_two

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  if Lean.debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel checking is disabled in the audit environment"
  let declarations := env.constants.toList.filter fun (name, info) =>
    !info.isUnsafe && match env.getModuleIdxFor? name with
    | some idx => env.allImportedModuleNames[idx]! == `UploadBroadcast.ResonantUploadSpecializations
    | none => false
  if declarations.isEmpty then
    throwError "No specialization declarations found"
  for (name, _) in declarations do
    if (env.checked.get.find? name).isNone then
      throwError "Declaration absent from checked environment: {name}"
  let work : Lean.CollectAxioms.M Unit := (declarations.map Prod.fst).forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved reachable axiom {ax}"
  logInfo m!"Module-origin audit passed for {declarations.length} safe declarations. Axioms: {state.axioms}"
