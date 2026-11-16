import UploadBroadcast.ResidualRowPaperEndpoint
import Lean
#print axioms UploadBroadcast.ResidualRowShape.exists_exact_row_completion
#print axioms UploadBroadcast.ResidualRowShape.row_completion_paper
#print axioms UploadBroadcast.ResidualRowShape.canonicalReduction_scalar_upload_exact
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) =>
    if (`UploadBroadcast.ResidualRowShape).isPrefixOf name && info.isTheorem then some name else none
  if names.isEmpty then throwError "No row-shape theorems found"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom {ax} reachable from row-shape theorems"
  logInfo m!"Row-shape axiom audit passed for {names.length} theorems."
  logInfo m!"Complete reachable axiom set: {state.axioms}"
