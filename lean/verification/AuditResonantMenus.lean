import UploadBroadcast.ResonantProfile
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, info) in env.constants.toList do
    if (`UploadBroadcast.ResonantRelay).isPrefixOf name && info.isTheorem then
      count := count + 1
      let axioms ← Lean.collectAxioms name
      logInfo m!"{name}: {axioms}"
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unapproved axiom {ax} in {name}"
  if count == 0 then
    throwError "No resonant relay/profile theorems found"
  logInfo m!"Resonant relay/profile axiom audit passed for {count} theorems."
