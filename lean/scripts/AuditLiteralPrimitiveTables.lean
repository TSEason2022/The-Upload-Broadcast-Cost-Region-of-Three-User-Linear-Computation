import UploadBroadcast.LiteralPrimitiveTables
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  if Lean.debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel checking is disabled in the audit environment"
  let literalModule (name : Name) :=
    name.toString.startsWith "UploadBroadcast.LiteralPrimitive" ||
    name == `UploadBroadcast.LiteralMatrixCertificates
  let declarations := env.constants.toList.filter fun (name, info) =>
    !info.isUnsafe && match env.getModuleIdxFor? name with
    | some idx => literalModule env.allImportedModuleNames[idx]!
    | none => false
  if declarations.isEmpty then
    throwError "No literal-certificate declarations found"
  for (name, _) in declarations do
    if (env.checked.get.find? name).isNone then
      throwError "Declaration absent from checked environment: {name}"
  let work : Lean.CollectAxioms.M Unit := (declarations.map Prod.fst).forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved reachable axiom {ax}"
  logInfo m!"Literal-matrix module-origin audit passed for {declarations.length} safe declarations. Axioms: {state.axioms}"
