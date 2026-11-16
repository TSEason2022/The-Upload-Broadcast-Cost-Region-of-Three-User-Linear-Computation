import UploadBroadcast.RegularResonantClassification
import UploadBroadcast.ResonantBaseChange
import UploadBroadcast.TaskComponentBridge
import UploadBroadcast.E6RealRoots
import UploadBroadcast.TensorTaskExtension

/-!
# Positive-excess components over the original finite field

Source: `lem:base-field-components`. For arbitrary finite-dimensional nested
three-arm flags over a finite field, genuine indecomposability, side spanning,
and positive side excess imply the real-root equation and indecomposability
after every field extension. The conclusion concerns the actual tensor-extended
subspaces. Neither a root bound nor an extension-splitting theorem is assumed.
The passive tripod is included, since the source lemma does not assume activity.
-/
noncomputable section
open scoped TensorProduct
namespace UploadBroadcast.TaskDecomposition

variable {K L V W I : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Every label-preserving configuration isomorphism extends to an actual
isomorphism of tensor-extended configurations. -/
theorem ConfigurationIso.baseChange {S : I → Submodule K V} {T : I → Submodule K W}
    (h : ConfigurationIso S T) :
    ConfigurationIso (extendConfiguration (L := L) S) (extendConfiguration T) := by
  obtain ⟨e,he,he'⟩ := h
  refine ⟨LinearEquiv.baseChange K L V W e, ?_, ?_⟩
  · exact he.baseChange
  · exact he'.baseChange

@[simp] theorem Task.extend_spaces (T : Task K V) :
    (T.extend (L := L)).spaces = extendConfiguration (L := L) T.spaces := by
  funext i
  rcases i with ⟨i,b⟩
  cases b <;> rfl

/-- Absolute indecomposability is transported on the six actual extended
subspaces, not inferred from dimension-vector equality. -/
theorem ConfigurationIso.extend_indec {S : I → Submodule K V} {T : I → Submodule K W}
    (h : ConfigurationIso S T)
    (hi : Indecomposable (extendConfiguration (L := L) T) ⊤) :
    Indecomposable (extendConfiguration (L := L) S) ⊤ :=
  ResonantBaseChange.indecomposable_of_iso h.baseChange hi

end UploadBroadcast.TaskDecomposition

namespace UploadBroadcast.BaseFieldComponents
open TaskDecomposition GeneralTransverseClassification ResonantEndomorphisms
variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The six-list and labeled-three-arm presentations name exactly the same
extended spaces; all six labels, including demand enlargements, are checked. -/
theorem graph_extend_indec_of_six {X : Type*} [AddCommGroup X] [Module K X]
    (J : Module.End K X) (h : X →ₗ[K] K)
    (hi : Indecomposable (extendConfiguration (L := L) (spaces K X J h)) ⊤) :
    Indecomposable ((graphTask K X J h).extend (L := L)).spaces ⊤ := by
  apply indecomposable_of_projection_eq_zero_or_id hi.1
  intro f hf hid
  apply hi.projection_eq_zero_or_id f _ hid
  intro i p hp
  fin_cases i
  · exact hf (0,false) p hp
  · exact hf (1,false) p hp
  · exact hf (2,false) p hp
  · exact hf (0,true) p hp
  · exact hf (1,true) p hp
  · exact hf (2,true) p hp

/-- Scalar endomorphisms of the passive endpoint follow directly from its
three distinct lines. There is no activity hypothesis. -/
theorem passive_end_scalar
    (f : Ambient K (Fin 0 → K) →ₗ[K] Ambient K (Fin 0 → K))
    (hf : Stable (graphTask K (Fin 0 → K) 0 0).spaces f) :
    ∃ a : K, f = a • LinearMap.id := by
  obtain ⟨a,hv,hr⟩ := scalar_action f
    ⟨hf (0,false), hf (1,false), hf (2,false)⟩
  refine ⟨a,?_⟩
  apply LinearMap.ext
  intro p
  have hp : p = scalarV K (Fin 0 → K) p.2.2.2.1 +
      scalarR K (Fin 0 → K) p.2.2.2.2 := by
    rcases p with ⟨x,y,z,v,r⟩
    have hx : x = 0 := Subsingleton.elim _ _
    have hy : y = 0 := Subsingleton.elim _ _
    have hz : z = 0 := Subsingleton.elim _ _
    simp [scalarV,scalarR,hx,hy,hz]
  calc
    f p = f (scalarV K (Fin 0 → K) p.2.2.2.1 +
      scalarR K (Fin 0 → K) p.2.2.2.2) := congrArg f hp
    _ = scalarV K (Fin 0 → K) (a*p.2.2.2.1) +
      scalarR K (Fin 0 → K) (a*p.2.2.2.2) := by rw [map_add,hv,hr]
    _ = (a • LinearMap.id) p := by
      conv_rhs => rw [hp]
      simp [scalarV,scalarR,smul_add]
      rfl

/-- The passive tripod remains indecomposable under every field extension. -/
theorem passive_extend_indec :
    Indecomposable ((graphTask K (Fin 0 → K) 0 0).extend (L := L)).spaces ⊤ := by
  rw [Task.extend_spaces]
  exact scalarEnd_baseChange_indec _ (passive_end_scalar K)

/-- The canonical resonant block is absolutely indecomposable in the actual
three-arm task presentation, by explicit tensor-coordinate naturality. -/
theorem resonant_extend_indec (n : ℕ) :
    Indecomposable ((graphTask K (JordanResonance.V K n)
      (JordanResonance.shift K n) (JordanResonance.head K n)).extend (L := L)).spaces ⊤ :=
  graph_extend_indec_of_six K L _ _ (ResonantBaseChange.jordan_absolutely_indecomposable K L n)

end UploadBroadcast.BaseFieldComponents

namespace UploadBroadcast.TaskDecomposition
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The source lemma's real-root equation for arbitrary original-field flags.
Defect zero, nonzero defect, and the passive endpoint are all included. -/
theorem Task.positive_excess_tits_one (T : Task K V)
    (hi : Indecomposable T.spaces ⊤)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hpos : Module.finrank K V < Module.finrank K (T.A 0) +
      Module.finrank K (T.A 1) + Module.finrank K (T.A 2)) :
    ReflectionReduction.tits T.dimensionVector = 1 := by
  by_cases hd : ReflectionReduction.defect T.dimensionVector = 0
  · exact (RegularResonantClassification.tits_and_excess T hi hd hspan hpos).1
  · exact T.nonzero_defect_tits_one hi hd

/-- Source `lem:base-field-components`, actual absolute indecomposability:
for every extension field, the scalar-extended six flags have no nontrivial
simultaneous direct-sum decomposition. No activity assumption is imposed. -/
theorem Task.positive_excess_extend_indec (T : Task K V)
    (hi : Indecomposable T.spaces ⊤)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hpos : Module.finrank K V < Module.finrank K (T.A 0) +
      Module.finrank K (T.A 1) + Module.finrank K (T.A 2))
    (L : Type*) [Field L] [Algebra K L] :
    Indecomposable (T.extend (L := L)).spaces ⊤ := by
  by_cases hd : ReflectionReduction.defect T.dimensionVector = 0
  · rcases RegularResonantClassification.classification T hi hd hspan hpos with
      ⟨_,hiso⟩ | ⟨n,hiso⟩
    · rw [Task.extend_spaces]
      apply hiso.extend_indec
      simpa only [Task.extend_spaces] using BaseFieldComponents.passive_extend_indec K L
    · rw [Task.extend_spaces]
      apply hiso.extend_indec
      simpa only [Task.extend_spaces] using BaseFieldComponents.resonant_extend_indec K L n
  · exact T.nonzero_defect_extend_indec hi hd L

/-- Combined original-field source endpoint. `L` is an arbitrary extension,
not merely a field with a selected finite degree or a splitting certificate. -/
theorem Task.positive_excess_base_field_components (T : Task K V)
    (hi : Indecomposable T.spaces ⊤)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hpos : Module.finrank K V < Module.finrank K (T.A 0) +
      Module.finrank K (T.A 1) + Module.finrank K (T.A 2))
    (L : Type*) [Field L] [Algebra K L] :
    Indecomposable (T.extend (L := L)).spaces ⊤ ∧
      ReflectionReduction.tits T.dimensionVector = 1 :=
  ⟨T.positive_excess_extend_indec hi hspan hpos L,
    T.positive_excess_tits_one hi hspan hpos⟩

/-- The same absolute conclusion stated as indecomposability of the actual
inward-E6 representation, whose arrows are the six nested inclusions. -/
theorem Task.positive_excess_extend_rep_indec (T : Task K V)
    (hi : QuiverRepresentation.Indecomposable T.toRep)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hpos : Module.finrank K V < Module.finrank K (T.A 0) +
      Module.finrank K (T.A 1) + Module.finrank K (T.A 2))
    (L : Type*) [Field L] [Algebra K L] :
    QuiverRepresentation.Indecomposable (T.extend (L := L)).toRep :=
  (T.extend (L := L)).rep_indec_of_indec
    (T.positive_excess_extend_indec (T.indec_of_rep_indec hi) hspan hpos L)

/-- Source-form wrapper with the integer excess `sum_i dim A_i - dim F`.
The original representation is indecomposable, and its actual extension is
indecomposable for an arbitrary extension field. -/
theorem Task.base_field_components (T : Task K V)
    (hi : QuiverRepresentation.Indecomposable T.toRep)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hchi : 0 < Structural.excess T.dimensionVector.f
      T.dimensionVector.a₁ T.dimensionVector.a₂ T.dimensionVector.a₃)
    (L : Type*) [Field L] [Algebra K L] :
    QuiverRepresentation.Indecomposable (T.extend (L := L)).toRep ∧
      ReflectionReduction.tits T.dimensionVector = 1 := by
  have hpos : Module.finrank K V < Module.finrank K (T.A 0) +
      Module.finrank K (T.A 1) + Module.finrank K (T.A 2) := by
    simp only [Structural.excess,Task.dimensionVector] at hchi
    omega
  exact ⟨T.positive_excess_extend_rep_indec hi hspan hpos L,
    T.positive_excess_tits_one (T.indec_of_rep_indec hi) hspan hpos⟩

/-- The original-field conclusion applied to an actual indecomposable component
inside a larger ambient space. The side-span and excess belong to that component. -/
theorem Task.component_base_field_components (T : Task K V) (P : Submodule K V)
    (hi : Indecomposable T.spaces P)
    (hspan : ((T.onComponent P).A 0 ⊔ (T.onComponent P).A 1) ⊔
      (T.onComponent P).A 2 = ⊤)
    (hchi : 0 < T.componentExcess P)
    (L : Type*) [Field L] [Algebra K L] :
    Indecomposable ((T.onComponent P).extend (L := L)).spaces ⊤ ∧
      ReflectionReduction.tits (T.componentDimension P) = 1 := by
  have hpos : Module.finrank K P < Module.finrank K ((T.onComponent P).A 0) +
      Module.finrank K ((T.onComponent P).A 1) +
      Module.finrank K ((T.onComponent P).A 2) := by
    norm_num [Task.componentExcess,Fin.sum_univ_succ] at hchi
    change (Module.finrank K P : ℤ) < (Module.finrank K ↥(T.A 0 ⊓ P) : ℤ) +
      (Module.finrank K ↥(T.A 1 ⊓ P) + Module.finrank K ↥(T.A 2 ⊓ P)) at hchi
    simp only [Task.onComponent,finrank_comap_subtype]
    omega
  simpa only [Task.onComponent_dimensionVector] using
    (T.onComponent P).positive_excess_base_field_components
      (T.onComponent_indec P hi) hspan hpos L

/-- The actual dimension vector is in the Weyl orbit of a simple affine E6
root. This uses the proved norm-one/orbit equivalence, not a definition of
real-root membership by the desired Tits equation. -/
theorem Task.positive_excess_real_root (T : Task K V)
    (hi : Indecomposable T.spaces ⊤)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hpos : Module.finrank K V < Module.finrank K (T.A 0) +
      Module.finrank K (T.A 1) + Module.finrank K (T.A 2)) :
    E6RealRoots.IsRealRoot (QuiverRepresentation.dimension T.toRep) := by
  apply E6RealRoots.realRoot_of_nonneg_norm_one
  · intro v
    exact Int.natCast_nonneg _
  · exact T.positive_excess_tits_one hi hspan hpos

/-- Complete source `lem:base-field-components`: an arbitrary indecomposable
nested three-arm task over its original finite field, with spanning sides and
positive excess, remains indecomposable over every extension field, and its
actual dimension vector is a real root in the simple-reflection-orbit sense.
The explicit Tits value is also recorded. -/
theorem Task.source_base_field_components (T : Task K V)
    (hi : QuiverRepresentation.Indecomposable T.toRep)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hchi : 0 < Structural.excess T.dimensionVector.f
      T.dimensionVector.a₁ T.dimensionVector.a₂ T.dimensionVector.a₃)
    (L : Type*) [Field L] [Algebra K L] :
    QuiverRepresentation.Indecomposable (T.tensorRep L) ∧
      E6RealRoots.IsRealRoot (QuiverRepresentation.dimension T.toRep) ∧
      ReflectionReduction.tits T.dimensionVector = 1 := by
  obtain ⟨ha,hq⟩ := T.base_field_components hi hspan hchi L
  refine ⟨(T.tensorRep_indec_iff L).mpr ha,?_,hq⟩
  apply E6RealRoots.realRoot_of_nonneg_norm_one
  · intro v
    exact Int.natCast_nonneg _
  · exact hq

end UploadBroadcast.TaskDecomposition
