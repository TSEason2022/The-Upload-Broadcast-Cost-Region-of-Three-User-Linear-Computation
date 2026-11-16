import UploadBroadcast.BaseFieldComponents
import Lean

/-! Source-shape check, including arbitrary extension fields and no activity,
transversality, root-family, scalar-endomorphism, or splitting-oracle premise. -/
open UploadBroadcast TaskDecomposition in
example {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : TaskDecomposition.Task K V)
    (hi : QuiverRepresentation.Indecomposable T.toRep)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hchi : 0 < Structural.excess T.dimensionVector.f
      T.dimensionVector.a₁ T.dimensionVector.a₂ T.dimensionVector.a₃)
    (L : Type*) [Field L] [Algebra K L] :
    QuiverRepresentation.Indecomposable (T.tensorRep L) ∧
      E6RealRoots.IsRealRoot (QuiverRepresentation.dimension T.toRep) ∧
      ReflectionReduction.tits T.dimensionVector = 1 :=
  T.source_base_field_components hi hspan hchi L

#print axioms UploadBroadcast.E6RealRoots.nonnegative_realRoot_iff_norm_one
#print axioms UploadBroadcast.TaskDecomposition.Task.tensorRepIso
#print axioms UploadBroadcast.TaskDecomposition.Task.source_base_field_components
#print axioms UploadBroadcast.TaskDecomposition.Task.component_base_field_components

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := #[
    ``UploadBroadcast.E6RealRoots.nonnegative_realRoot_iff_norm_one,
    ``UploadBroadcast.TaskDecomposition.Task.tensorRep_indec_iff,
    ``UploadBroadcast.TaskDecomposition.Task.source_base_field_components,
    ``UploadBroadcast.TaskDecomposition.Task.component_base_field_components]
  let work : Lean.CollectAxioms.M Unit := roots.forM Lean.CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom {ax} in original-field source endpoint"
  logInfo m!"Original-field source endpoint strict axiom audit passed: {state.axioms}"
