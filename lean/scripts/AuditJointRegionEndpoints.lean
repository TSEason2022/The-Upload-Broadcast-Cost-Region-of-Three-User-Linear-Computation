import UploadBroadcast.JointRegionEndpoints
import UploadBroadcast.BroadcastFiniteEndpoints
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) =>
    if (`UploadBroadcast).isPrefixOf name && info.isTheorem then some name else none
  if names.isEmpty then
    throwError "No UploadBroadcast theorems found; refusing an empty audit"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom {ax} reachable from endpoint theorem imports"
  logInfo m!"Endpoint dependency axiom audit passed for {names.length} project theorems."
  logInfo m!"Complete reachable axiom set: {state.axioms}"

#print axioms UploadBroadcast.Task.uploadOptimum_double
#print axioms UploadBroadcast.Task.uploadOptimum_halfInteger
#print axioms UploadBroadcast.Task.minimum_upload_scalar_of_optimum_integral
#print axioms UploadBroadcast.Task.ScalarRelayWitness.scalar_code
#print axioms UploadBroadcast.Task.scalar_ceiling_of_actual_relay
#print axioms UploadBroadcast.Task.joint_two_of_actual_doubled_relay
#print axioms UploadBroadcast.Task.least_linear_joint_blocklength_of_selection
#print axioms UploadBroadcast.Task.region_eq_rectangle_of_doubled_selection
#print axioms UploadBroadcast.fullyInformed_one_two_or_four
