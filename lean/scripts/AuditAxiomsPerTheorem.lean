import UploadBroadcast
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, info) in env.constants.toList do
    if (`UploadBroadcast).isPrefixOf name then
      if info.isTheorem then
        count := count + 1
        let axioms ← Lean.collectAxioms name
        logInfo m!"{name}: {axioms}"
        for ax in axioms do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unapproved axiom {ax} in {name}"
  if count == 0 then
    throwError "No UploadBroadcast theorems found; refusing an empty audit"
  logInfo m!"Axiom audit passed for {count} project theorems."
