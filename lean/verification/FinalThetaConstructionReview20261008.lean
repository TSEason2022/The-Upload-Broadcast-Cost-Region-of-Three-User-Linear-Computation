import UploadBroadcast.LiteralThetaBlocks
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List Name := [`UploadBroadcast.LiteralThetaBlocks.R0.rank_conditions,
    `UploadBroadcast.LiteralThetaBlocks.R0.full_profile,
    `UploadBroadcast.LiteralThetaBlocks.R0.relation_certificate,
    `UploadBroadcast.LiteralThetaBlocks.R0.relay,
    `UploadBroadcast.LiteralThetaBlocks.R0.P_eq_kernel,
    `UploadBroadcast.LiteralThetaBlocks.R0.pair01,
    `UploadBroadcast.LiteralThetaBlocks.R0.pair02,
    `UploadBroadcast.LiteralThetaBlocks.R0.pair12,
    `UploadBroadcast.LiteralThetaBlocks.R0.pair_dimension,
    `UploadBroadcast.LiteralThetaBlocks.R0.triple_zero,
    `UploadBroadcast.LiteralThetaBlocks.R0.pair_conditional_rank,
    `UploadBroadcast.LiteralThetaBlocks.R0.pairs_span,
    `UploadBroadcast.LiteralThetaBlocks.R0.relay_side_dimension,
    `UploadBroadcast.LiteralThetaBlocks.R0.relay_signal_dimension,
    `UploadBroadcast.LiteralThetaBlocks.R0.relay_local_upload_dimension,
    `UploadBroadcast.LiteralThetaBlocks.R0.relay_pair_dimension,
    `UploadBroadcast.LiteralThetaBlocks.R0.relay_pair_conditional_rank,
    `UploadBroadcast.LiteralThetaBlocks.R0.relay_triple_zero,
    `UploadBroadcast.LiteralThetaBlocks.R0.relay_pair01,
    `UploadBroadcast.LiteralThetaBlocks.R0.relay_pair02,
    `UploadBroadcast.LiteralThetaBlocks.R0.relay_pair12,
    `UploadBroadcast.LiteralThetaBlocks.D.rank_conditions,
    `UploadBroadcast.LiteralThetaBlocks.D.profile,
    `UploadBroadcast.LiteralThetaBlocks.D.pair01,
    `UploadBroadcast.LiteralThetaBlocks.D.pair02,
    `UploadBroadcast.LiteralThetaBlocks.D.pair12,
    `UploadBroadcast.LiteralThetaBlocks.D.triple_zero,
    `UploadBroadcast.LiteralThetaBlocks.D.pair_conditional_rank,
    `UploadBroadcast.LiteralThetaBlocks.D.pairs_span,
    `UploadBroadcast.LiteralThetaBlocks.D.relay,
    `UploadBroadcast.LiteralThetaBlocks.D.append_profile,
    `UploadBroadcast.LiteralThetaBlocks.D.append_dimensions,
    `UploadBroadcast.LiteralThetaBlocks.D.append_conditional_ranks,
    `UploadBroadcast.LiteralThetaBlocks.embed_injective,
    `UploadBroadcast.LiteralThetaBlocks.induced_eq_image_D,
    `UploadBroadcast.LiteralThetaBlocks.R0_same_chart_profile]
  for n in names do
    match env.find? n with
    | none => throwError "Missing literal source endpoint: {n}"
    | some ci =>
      unless ci.isTheorem do throwError "Not a theorem: {n}"
      logInfo m!"{n} : {ci.type}"
  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom: {ax}"
  logInfo m!"Independent literal-construction audit passed for {names.length} roots; axioms {state.axioms}"
