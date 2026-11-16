import UploadBroadcast.RegularTripodPair
import UploadBroadcast.RegularExtensionGeneration
import UploadBroadcast.ExtensionBlockSeparation
import UploadBroadcast.CrossIntersectionClosure

/-!
# Cross-transversality of positive-excess regular indecomposables

Every actual semistable task has a proved finite regular-simple filtration.
The two concrete regular simples T0 and T1 are Hom- and extension-orthogonal
to every other regular-simple class, by the explicit Hom–Euler identities.
The constructive block-separation theorem and positive T0-Hom detection force
all factors of a positive-excess regular indecomposable into that pair.
Cross-path injectivity, and hence every distinct Ui∩Aj=0, follows by extension
closure. No root shape, equality of private dimensions, or tube classification
is assumed.
-/
namespace UploadBroadcast.RegularPositiveCross
open TaskDecomposition QuiverRepresentation RegularTripodPair
variable {K : Type} [Field K]

/-- The two concrete classes, up to actual representation isomorphism. -/
def pairClass (R : Rep K inwardE6) : Prop :=
  Nonempty (Iso (T₀ K).toRep R) ∨ Nonempty (Iso (T₁ K).toRep R)

/-- The explicit orthogonality conditions satisfied by every other
regular-simple actual task. Only the conditions used in separation are stored. -/
def outsideClass (R : Rep K inwardE6) : Prop :=
  HomZero (T₀ K).toRep R ∧ HomZero (T₁ K).toRep R ∧
  Function.Surjective (coboundary (T₀ K).toRep R) ∧
  Function.Surjective (coboundary (T₁ K).toRep R) ∧
  Function.Surjective (coboundary R (T₀ K).toRep) ∧
  Function.Surjective (coboundary R (T₁ K).toRep)

private theorem homZero_of_finrank_zero (R S : Rep K inwardE6)
    [∀ v, FiniteDimensional K (R.space v)] [∀ v, FiniteDimensional K (S.space v)]
    (h : Module.finrank K (Hom R S)=0) : HomZero R S := by
  intro f
  change f=0
  exact (Module.finrank_zero_iff.mp h).elim f 0

/-- Every actual regular-simple task lies in the concrete pair or satisfies
the full cross-class linear-obstruction vanishing conditions. -/
theorem regularSimple_atom_dichotomy {F : Type} [AddCommGroup F] [Module K F]
    [FiniteDimensional K F] (T : TaskDecomposition.Task K F) (hT : T.IsRegularSimple) :
    pairClass T.toRep ∨ outsideClass T.toRep := by
  classical
  by_cases h₀ : ConfigurationIso T.spaces (T₀ K).spaces
  · obtain ⟨e⟩ := (T.configurationIso_iff_repIso (T₀ K)).mp h₀
    exact Or.inl (Or.inl ⟨e.symm⟩)
  by_cases h₁ : ConfigurationIso T.spaces (T₁ K).spaces
  · obtain ⟨e⟩ := (T.configurationIso_iff_repIso (T₁ K)).mp h₁
    exact Or.inl (Or.inr ⟨e.symm⟩)
  obtain ⟨⟨h0l,h0r,e0l,e0r⟩,⟨h1l,h1r,e1l,e1r⟩⟩ :=
    regular_simple_outside_pair_orthogonal T hT h₀ h₁
  right
  refine ⟨homZero_of_finrank_zero _ _ h0l,homZero_of_finrank_zero _ _ h1l,?_,?_,?_,?_⟩
  · apply coboundary_surjective_of_hom_eq_euler
    rw [h0l,e0l]
    rfl
  · apply coboundary_surjective_of_hom_eq_euler
    rw [h1l,e1l]
    rfl
  · apply coboundary_surjective_of_hom_eq_euler
    rw [h0r,e0r]
    rfl
  · apply coboundary_surjective_of_hom_eq_euler
    rw [h1r,e1r]
    rfl

theorem pair_outside_coboundary (R S : Rep K inwardE6)
    (hR : pairClass R) (hS : outsideClass S) :
    Function.Surjective (coboundary R S) := by
  rcases hR with hR | hR
  · obtain ⟨e⟩ := hR
    exact coboundary_surjective_iso_source e hS.2.2.1
  · obtain ⟨e⟩ := hR
    exact coboundary_surjective_iso_source e hS.2.2.2.1

theorem outside_pair_coboundary (R S : Rep K inwardE6)
    (hR : outsideClass R) (hS : pairClass S) :
    Function.Surjective (coboundary R S) := by
  rcases hS with hS | hS
  · obtain ⟨e⟩ := hS
    exact coboundary_surjective_iso_target e hR.2.2.2.2.1
  · obtain ⟨e⟩ := hS
    exact coboundary_surjective_iso_target e hR.2.2.2.2.2

theorem pair_outside_homZero (R S : Rep K inwardE6)
    (hR : pairClass R) (hS : outsideClass S) : HomZero R S := by
  rcases hR with hR | hR
  · obtain ⟨e⟩ := hR
    exact homZero_iso_source e hS.1
  · obtain ⟨e⟩ := hR
    exact homZero_iso_source e hS.2.1

/-- Both explicit atoms have all six distinct cross-path maps injective. -/
theorem pairClass_crossTransverse (R : Rep K inwardE6) (hR : pairClass R) :
    CrossTransverse R := by
  have h₀ : CrossTransverse (T₀ K).toRep := by
    intro i j hij
    apply ((T₀ K).crossMap_injective_iff i j).mpr
    exact (T₀_cross_disjoint j i (Ne.symm hij)).symm
  have h₁ : CrossTransverse (T₁ K).toRep := by
    intro i j _
    apply ((T₁ K).crossMap_injective_iff i j).mpr
    exact (T₁_cross_disjoint j i).symm
  rcases hR with hR | hR
  · obtain ⟨e⟩ := hR
    exact h₀.iso e
  · obtain ⟨e⟩ := hR
    exact h₁.iso e

/-- Positive side excess places an actual zero-defect indecomposable entirely
in the extension closure of T0 and T1, with no root-shape assumption. -/
theorem positive_regular_generated_by_pair {F : Type} [AddCommGroup F] [Module K F]
    [FiniteDimensional K F] (T : TaskDecomposition.Task K F)
    (hi : TaskDecomposition.Indecomposable T.spaces ⊤)
    (hzero : ReflectionReduction.defect T.dimensionVector=0)
    (hpos : Module.finrank K F <
      Module.finrank K (T.A 0)+Module.finrank K (T.A 1)+Module.finrank K (T.A 2)) :
    ExtensionGenerated pairClass T.toRep := by
  have hsem := T.isSemistable_of_indec hi hzero
  have hgen : ExtensionGenerated (fun R => pairClass R ∨ outsideClass R) T.toRep :=
    hsem.regularFiltration.extensionGenerated _ (fun _ _ _ _ S hS => regularSimple_atom_dichotomy S hS)
  have hrank := positive_excess_T₀_hom_pos T hpos
  haveI : Nontrivial (Hom (T₀ K).toRep T.toRep) := Module.nontrivial_of_finrank_pos hrank
  obtain ⟨f,hf⟩ := exists_ne (0 : Hom (T₀ K).toRep T.toRep)
  exact hgen.one_class_of_detected_atom pair_outside_coboundary outside_pair_coboundary
    pair_outside_homZero (T.rep_indec_of_indec hi) (T₀ K).toRep (Or.inl ⟨Iso.refl _⟩) f hf

/-- The missing general cross-transversality theorem for the actual source
task. This conclusion covers every distinct pair, over every field. -/
theorem cross_disjoint {F : Type} [AddCommGroup F] [Module K F]
    [FiniteDimensional K F] (T : TaskDecomposition.Task K F)
    (hi : TaskDecomposition.Indecomposable T.spaces ⊤)
    (hzero : ReflectionReduction.defect T.dimensionVector=0)
    (hpos : Module.finrank K F <
      Module.finrank K (T.A 0)+Module.finrank K (T.A 1)+Module.finrank K (T.A 2)) :
    ∀ i j : Fin 3, i≠j → Disjoint (T.U i) (T.A j) := by
  have hg := positive_regular_generated_by_pair T hi hzero hpos
  intro i j hij
  apply (T.crossMap_injective_iff i j).mp
  exact hg.crossTransverse pairClass_crossTransverse i j hij

end UploadBroadcast.RegularPositiveCross
