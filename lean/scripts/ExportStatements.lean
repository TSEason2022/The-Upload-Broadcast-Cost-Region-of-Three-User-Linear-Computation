import UploadBroadcast
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, info) in env.constants.toList do
    if (`UploadBroadcast).isPrefixOf name && info.isTheorem then
      count := count + 1
      logInfo m!"{name} : {info.type}"
  logInfo m!"Exported {count} theorem types. Supporting declarations are not named-paper coverage counts."
