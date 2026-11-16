import UploadBroadcast.LiteralThetaBlocks
import Lean

/-! Audit every safe declaration originating in the literal θ-block module,
including definitions carrying proofs and compiler-generated declarations.
All reachable axioms, including those reached through imported dependencies,
are restricted to the three standard logical axioms below. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  if Lean.debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel checking is disabled in the audit environment"
  let declarations := env.constants.toList.filter fun (name, info) =>
    !info.isUnsafe && match env.getModuleIdxFor? name with
    | some idx => env.allImportedModuleNames[idx]! == `UploadBroadcast.LiteralThetaBlocks
    | none => false
  if declarations.isEmpty then
    throwError "No literal theta-block declarations found"
  for (name, _) in declarations do
    if (env.checked.get.find? name).isNone then
      throwError "Declaration absent from checked environment: {name}"
  let work : Lean.CollectAxioms.M Unit := (declarations.map Prod.fst).forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved reachable axiom {ax}"
  logInfo m!"Literal-theta module-origin audit passed for {declarations.length} safe declarations. Axioms: {state.axioms}"
