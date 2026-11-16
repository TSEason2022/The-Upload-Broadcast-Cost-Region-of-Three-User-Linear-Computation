import UploadBroadcast
import Lean

/-! Inventory all declarations originating in imported project
modules with Lean's own axiom collector, sharing its visited set across roots.
Module provenance includes private and out-of-namespace names. All safe
declaration kinds are roots, so proof-bearing definitions and unused logical
declarations are also checked. Lean generates unsafe implementation-only
specializations, including unsafe axiom stubs: these cannot be referenced by
safe kernel proofs and are counted separately, not treated as logical roots.
Source-level unsafe declarations remain disallowed by the lexical gate.
This audit examines imported terms; it does not authenticate cached
objects or independently re-run their kernel checks. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  if Lean.debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel checking is disabled in the audit environment"
  let projectModules := env.allImportedModuleNames.filter (`UploadBroadcast).isPrefixOf
  if projectModules.isEmpty then
    throwError "No UploadBroadcast modules imported; refusing an empty audit"
  let declarations := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => (`UploadBroadcast).isPrefixOf env.allImportedModuleNames[idx]!
    | none => false
  let logicalDeclarations := declarations.filter fun (_, info) => !info.isUnsafe
  let names := logicalDeclarations.map Prod.fst
  if names.isEmpty then
    throwError "No project declarations found; refusing an empty audit"
  for (name, _) in logicalDeclarations do
    if (env.checked.get.find? name).isNone then
      throwError "Project declaration absent from checked environment: {name}"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom {ax} reachable from safe project declarations"
  let theoremCount := (logicalDeclarations.filter fun (_, info) => info.isTheorem).length
  let outsideNamespace := (logicalDeclarations.filter fun (name, _) =>
    !(`UploadBroadcast).isPrefixOf name).length
  logInfo m!"Axiom audit passed for {names.length} safe declarations ({theoremCount} theorems) from {projectModules.size} project modules."
  logInfo m!"Included {outsideNamespace} private or out-of-namespace declarations."
  logInfo m!"Inventoried {declarations.length - names.length} unsafe compiler implementation declarations separately."
  logInfo m!"Imported-object trust level: {env.header.trustLevel}; this audit is not an independent object recheck."
  logInfo m!"Complete reachable axiom set: {state.axioms}"
