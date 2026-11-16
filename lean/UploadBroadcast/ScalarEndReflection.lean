import UploadBroadcast.TaskQuiverBridge
import UploadBroadcast.SourceHomVanishing

/-! Scalar endomorphisms descend through actual reflection equivalences. -/
namespace UploadBroadcast.QuiverRepresentation
open ReflectionEquivalence

universe u
variable {K V E : Type u} [Field K]

def scalarHom {Q : Orientation V E} (R : Rep K Q) (c : K) : Hom R R where
  map _ := c • LinearMap.id
  comm e := by ext x; simp

def ScalarEnd {Q : Orientation V E} (R : Rep K Q) : Prop :=
  ∀ f : Hom R R, ∃ c : K, f = scalarHom R c

@[simp] theorem pullbackHom_scalar {V' E' : Type u} {Q : Orientation V E} {Q' : Orientation V' E'}
    (a : GraphIso Q Q') (R : Rep K Q') (c : K) :
    pullbackHom a (scalarHom R c) = scalarHom (pullback a R) c := rfl

@[simp] theorem Iso.homCongr_scalar {Q : Orientation V E} {R S : Rep K Q}
    (a : Iso R S) (c : K) : a.homCongr a (scalarHom R c) = scalarHom S c := by
  apply Hom.ext
  intro v
  apply LinearMap.ext
  intro x
  simp [Iso.homCongr, Hom.comp, Iso.toHom, Iso.symm, scalarHom]

section Attached
variable {I : Type u} [Fintype I] [DecidableEq I] {Q : Orientation V E}
  (R : Rep K Q) (neighbour : I → V)
  {X : Type u} [AddCommGroup X] [Module K X]

@[simp] theorem reflectAttachedSinkHom_scalar (f : Boundary R neighbour →ₗ[K] X) (c : K) :
    reflectAttachedSinkHom (scalarHom (attachSink R neighbour f) c) =
      scalarHom (attachSource R neighbour (sink f)) c := by
  apply Hom.ext
  intro v
  cases v <;> rfl

omit [Fintype I] in
@[simp] theorem reflectAttachedSourceHom_scalar (g : X →ₗ[K] Boundary R neighbour) (c : K) :
    reflectAttachedSourceHom (scalarHom (attachSource R neighbour g) c) =
      scalarHom (attachSink R neighbour (source g)) c := by
  apply Hom.ext
  intro v
  cases v with
  | some v => rfl
  | none =>
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H w => rfl

end Attached

section Reflection
variable [DecidableEq V] [DecidableEq E] [Fintype E] {Q : Orientation V E} {s : V}

@[simp] theorem sinkReflectHomEquiv_scalar (R : Rep K Q) (hs : Q.IsSink s)
    (hf : Function.Surjective (sinkIncoming R hs)) (c : K) :
    sinkReflectHomEquiv R R hs hf hf (scalarHom R c) = scalarHom (sinkReflect R hs) c := by
  change pullbackHom _ (reflectAttachedSinkHom
    ((sinkChartIso R hs).homCongr (sinkChartIso R hs)
      (pullbackHom (sinkChartGraph Q s hs) (scalarHom R c)))) = _
  rw [pullbackHom_scalar, Iso.homCongr_scalar, reflectAttachedSinkHom_scalar, pullbackHom_scalar]
  rfl

@[simp] theorem sourceReflectHomEquiv_scalar (R : Rep K Q) (hs : Q.IsSource s)
    (hf : Function.Injective (sourceOutgoing R hs)) (c : K) :
    sourceReflectHomEquiv R R hs hf hf (scalarHom R c) = scalarHom (sourceReflect R hs) c := by
  change pullbackHom _ (reflectAttachedSourceHom
    ((sourceChartIso R hs).homCongr (sourceChartIso R hs)
      (pullbackHom (sourceChartGraph Q s hs) (scalarHom R c)))) = _
  rw [pullbackHom_scalar, Iso.homCongr_scalar, reflectAttachedSourceHom_scalar, pullbackHom_scalar]
  rfl

theorem scalarEnd_of_sinkReflect (R : Rep K Q) (hs : Q.IsSink s)
    (hf : Function.Surjective (sinkIncoming R hs)) (h : ScalarEnd (sinkReflect R hs)) : ScalarEnd R := by
  intro f
  obtain ⟨c, hc⟩ := h (sinkReflectHomEquiv R R hs hf hf f)
  refine ⟨c, (sinkReflectHomEquiv R R hs hf hf).injective ?_⟩
  rw [sinkReflectHomEquiv_scalar]
  exact hc

theorem scalarEnd_of_sourceReflect (R : Rep K Q) (hs : Q.IsSource s)
    (hf : Function.Injective (sourceOutgoing R hs)) (h : ScalarEnd (sourceReflect R hs)) : ScalarEnd R := by
  intro f
  obtain ⟨c, hc⟩ := h (sourceReflectHomEquiv R R hs hf hf f)
  refine ⟨c, (sourceReflectHomEquiv R R hs hf hf).injective ?_⟩
  rw [sourceReflectHomEquiv_scalar]
  exact hc

theorem ReflectionReach.scalarEnd {Q Q' : Orientation V E} {R : Rep K Q} {S : Rep K Q'}
    (h : ReflectionReach R S) : ScalarEnd S → ScalarEnd R := by
  induction h with
  | refl => exact id
  | sink R hs hf => exact scalarEnd_of_sinkReflect R hs hf
  | source R hs hg => exact scalarEnd_of_sourceReflect R hs hg
  | trans h1 h2 ih1 ih2 => exact fun hs => ih1 (ih2 hs)

end Reflection

theorem VertexSimple.scalarEnd {Q : Orientation V E} {R : Rep K Q} {s : V}
    (h : VertexSimple R s) : ScalarEnd R := by
  have hn : Nontrivial (R.space s) := by
    rcases subsingleton_or_nontrivial (R.space s) with hz | hn
    · letI := hz
      have hh := h.2
      rw [Module.finrank_zero_of_subsingleton] at hh
      contradiction
    · exact hn
  letI := hn
  obtain ⟨x, hx⟩ := exists_ne (0 : R.space s)
  intro f
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one h.2 hx (f.map s x)
  refine ⟨c, ?_⟩
  apply Hom.ext
  intro v
  apply LinearMap.ext
  intro y
  change f.map v y = c • y
  by_cases hv : v = s
  · subst v
    obtain ⟨a, rfl⟩ := exists_smul_eq_of_finrank_eq_one h.2 hx y
    rw [map_smul, ← hc, smul_comm]
  · rw [h.1 v hv y, map_zero, smul_zero]

theorem ReachesSimple.scalarEnd [DecidableEq V] [DecidableEq E] [Fintype E]
    {Q : Orientation V E} {R : Rep K Q} (h : ReachesSimple R) : ScalarEnd R := by
  obtain ⟨Q', S, s, hr, hs⟩ := h
  exact hr.scalarEnd hs.scalarEnd

end UploadBroadcast.QuiverRepresentation

namespace UploadBroadcast.E6Reflection
open QuiverRepresentation

theorem nonzero_defect_scalarEnd {K : Type} [Field K] (R : Rep K inwardE6)
    [∀ v, FiniteDimensional K (R.space v)] (hR : Indecomposable R)
    (hd : ReflectionReduction.defect (vector (dimension R)) ≠ 0) : ScalarEnd R :=
  (nonzero_defect_reaches_simple R hR hd).scalarEnd

end UploadBroadcast.E6Reflection

namespace UploadBroadcast.TaskDecomposition
open QuiverRepresentation

/-- Every preserving ambient endomorphism of a nonzero-defect indecomposable
six-subspace task is scalar, proved over the original field. -/
theorem Task.nonzero_defect_end_scalar {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Task K V) (hT : Indecomposable T.spaces ⊤)
    (hd : ReflectionReduction.defect T.dimensionVector ≠ 0)
    (f : V →ₗ[K] V) (hf : Stable T.spaces f) : ∃ c : K, f = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := E6Reflection.nonzero_defect_scalarEnd T.toRep
    (T.rep_indec_of_indec hT) hd (T.homOfPreserves T f hf)
  exact ⟨c, congrArg (fun h => h.map .center) hc⟩

end UploadBroadcast.TaskDecomposition
