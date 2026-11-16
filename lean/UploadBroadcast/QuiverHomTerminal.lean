import UploadBroadcast.QuiverHomLinear
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! Terminal Hom spaces at an actual source-supported target. -/
namespace UploadBroadcast.QuiverRepresentation
universe u
variable {K V E : Type u} [Field K] [DecidableEq V]
  {Q : Orientation V E}

/-- At a source, every map into a representation supported there extends
uniquely to a representation morphism. -/
def supportedSourceTargetHom (R S : Rep K Q) {s : V}
    (hs : Q.IsSource s) (hp : SupportedAt S s)
    (f : R.space s →ₗ[K] S.space s) : Hom R S where
  map v := if h : v = s then by subst v; exact f else 0
  comm e := by
    apply LinearMap.ext
    intro x
    have ht := hs e
    simp only [dif_neg ht, LinearMap.zero_comp, LinearMap.zero_apply,
      LinearMap.comp_apply]
    exact (hp (Q.target e) ht _).symm

/-- The terminal identification is linear, so it computes the actual Hom
space dimension, not merely its cardinality. -/
def supportedSourceTargetHomLinearEquiv (R S : Rep K Q) {s : V}
    (hs : Q.IsSource s) (hp : SupportedAt S s) :
    Hom R S ≃ₗ[K] (R.space s →ₗ[K] S.space s) where
  toFun f := f.map s
  invFun f := supportedSourceTargetHom R S hs hp f
  left_inv f := by
    apply Hom.ext
    intro v
    by_cases hv : v = s
    · subst v; simp [supportedSourceTargetHom]
    · apply LinearMap.ext
      intro x
      simp only [supportedSourceTargetHom, dif_neg hv, LinearMap.zero_apply]
      exact (hp v hv _).symm
  right_inv f := by simp [supportedSourceTargetHom]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A one-dimensional source-simple target reads the dimension at that vertex. -/
theorem hom_finrank_sourceSimpleTarget (R S : Rep K Q) {s : V}
    [FiniteDimensional K (R.space s)] [FiniteDimensional K (S.space s)]
    (hs : Q.IsSource s) (hp : VertexSimple S s) :
    Module.finrank K (Hom R S) = Module.finrank K (R.space s) := by
  rw [(supportedSourceTargetHomLinearEquiv R S hs hp.1).finrank_eq,
    Module.finrank_linearMap, hp.2, mul_one]

end UploadBroadcast.QuiverRepresentation
