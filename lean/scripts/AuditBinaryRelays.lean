import UploadBroadcast.BinaryRelayMenus
import UploadBroadcast.BinaryMenuAllocation
import UploadBroadcast.BinaryRelayProfiles
import UploadBroadcast.BinaryCodimTwoProfiles
import UploadBroadcast.BinaryExceptionalRelays
import UploadBroadcast.NonzeroR2Wedge
import UploadBroadcast.TaskUserPermutation
import UploadBroadcast.R2PermutedMenus
import UploadBroadcast.NonzeroExceptionalRelays
import UploadBroadcast.BinaryAugmentedAllocation
import UploadBroadcast.R2ExactProfile
import UploadBroadcast.NonzeroBinaryMenus
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefixes : List Name := [`UploadBroadcast.BinaryRelayMenus, `UploadBroadcast.BinaryMenuAllocation, `UploadBroadcast.BinaryRelayProfiles, `UploadBroadcast.BinaryCodimTwoProfiles, `UploadBroadcast.BinaryExceptionalRelays, `UploadBroadcast.NonzeroR2Wedge, `UploadBroadcast.TaskUserPermutation, `UploadBroadcast.R2PermutedMenus, `UploadBroadcast.NonzeroExceptionalRelays, `UploadBroadcast.BinaryAugmentedAllocation, `UploadBroadcast.R2ExactProfile, `UploadBroadcast.NonzeroBinaryMenus]
  let names := env.constants.toList.filterMap fun (name, info) =>
    if prefixes.any (·.isPrefixOf name) && info.isTheorem then some name else none
  if names.isEmpty then
    throwError "No project theorems found; refusing an empty audit"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom {ax} reachable from project theorems"
  logInfo m!"Binary relay axiom audit passed for {names.length} project theorems."
  logInfo m!"Complete reachable axiom set: {state.axioms}"
