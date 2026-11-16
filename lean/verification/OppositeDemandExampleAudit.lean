import UploadBroadcast.OppositeDemandExample
import Lean

#check UploadBroadcast.OppositeDemandExample.first
#check UploadBroadcast.OppositeDemandExample.second
#check UploadBroadcast.OppositeDemandExample.combined
#check UploadBroadcast.OppositeDemandExample.singleton_encoders
#check UploadBroadcast.OppositeDemandExample.sum_encoder
#check UploadBroadcast.OppositeDemandExample.optima
#check UploadBroadcast.OppositeDemandExample.all_block_lower
#check UploadBroadcast.OppositeDemandExample.strict_subadditivity_example
#print axioms UploadBroadcast.OppositeDemandExample.singleton_encoders
#print axioms UploadBroadcast.OppositeDemandExample.sum_encoder
#print axioms UploadBroadcast.OppositeDemandExample.optima
#print axioms UploadBroadcast.OppositeDemandExample.all_block_lower
#print axioms UploadBroadcast.OppositeDemandExample.strict_subadditivity_example

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) =>
    if (`UploadBroadcast).isPrefixOf name && info.isTheorem then some name else none
  if names.isEmpty then throwError "Empty project audit"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom {ax}"
  logInfo m!"Opposite-demand source audit passed for {names.length} imported project theorems."
  logInfo m!"Complete reachable axiom set: {state.axioms}"
