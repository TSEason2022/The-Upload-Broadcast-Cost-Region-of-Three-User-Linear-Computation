import UploadBroadcast.BlockOptimalRelaySeparation
import Lean
#print axioms UploadBroadcast.TripodCompression.exists_compressed_double
#print axioms UploadBroadcast.TripodCompression.exists_compressed_double_finrank
#print axioms UploadBroadcast.OptimalRelaySeparation.exists_cheaper_code
#print axioms UploadBroadcast.OptimalRelaySeparation.induced_separation_of_two_code_lower
#print axioms UploadBroadcast.OptimalRelaySeparation.minimum_induced_independent
#print axioms UploadBroadcast.OptimalRelaySeparation.optimal_residual_sides
#print axioms UploadBroadcast.OptimalRelaySeparation.optimal_residual_sides_ambient
#print axioms UploadBroadcast.OptimalRelaySeparation.omniscience_minimum_separation
#print axioms UploadBroadcast.OptimalRelaySeparation.binary_relay_separation

#print axioms UploadBroadcast.OptimalRelaySeparation.optimal_block_residual_sides
#print axioms UploadBroadcast.OptimalRelaySeparation.optimal_block_residual_sides_ambient

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, info) in env.constants.toList do
    if (`UploadBroadcast.TripodCompression).isPrefixOf name ||
        (`UploadBroadcast.OptimalRelaySeparation).isPrefixOf name ||
        name.toString.startsWith "UploadBroadcast.Task.Code.toBlockDouble" then
      if info.isTheorem then
        count := count + 1
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unapproved axiom {ax} in {name}"
  if count == 0 then
    throwError "Empty relay separation audit"
  logInfo m!"Standard-axiom audit passed for all {count} relay-separation theorems."
