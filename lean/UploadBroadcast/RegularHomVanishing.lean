import UploadBroadcast.ResonantTripodTransversality

/-! Actual Hom separation of positive-defect and regular representations,
without root classification or an assumed tube decomposition. -/
namespace UploadBroadcast.QuiverRepresentation
universe u
variable {K V E : Type u} [Field K] [DecidableEq V] [DecidableEq E] [Fintype E]

/-- A negative source-word endpoint forces a supported source along the way;
a target with injective outgoing maps along the word admits no morphism from it. -/
theorem SourceWord.hom_zero_of_negative {Q Q' : Orientation V E} (w : SourceWord Q Q')
    (R S : Rep K Q) [∀ v, FiniteDimensional K (R.space v)]
    (hR : Indecomposable R) (hS : w.InjectiveAlong S)
    (v : V) (hneg : w.action (dimension R) v < 0) (f : Hom R S) : f = Hom.zero R S := by
  induction w with
  | nil => exact False.elim (not_lt_of_ge (Int.natCast_nonneg _) hneg)
  | @cons Q Q' s hs tail ih =>
    obtain hsimple | ⟨hnew,hout⟩ := source_step R hs hR
    · exact supportedSource_hom_zero R S hs hsimple.1 hS.1 f
    · have hn : tail.action (dimension (sourceReflect R hs)) v < 0 := by
        rw [dimension_sourceReflect R hs hout]
        exact hneg
      have he := ih (sourceReflect R hs) (sourceReflect S hs) hnew hS.2 hn
        (sourceReflectHomEquiv R S hs hout hS.1 f)
      apply (sourceReflectHomEquiv R S hs hout hS.1).injective
      rw [sourceReflectHomEquiv_zero]
      exact he
end UploadBroadcast.QuiverRepresentation

namespace UploadBroadcast.RegularHomVanishing
open QuiverRepresentation E6Reflection ResonantTripodTransversality

theorem source_blocks_zero_defect_nonsimple (n : ℕ) (x : ReflectionReduction.Dimension)
    (hd : ReflectionReduction.defect x=0) (hne : encode x ≠ fun _ => 0) :
    (sourceBlockWord.power n).NonSimpleDims (encode x) := by
  induction n with
  | zero => exact True.intro
  | succ n ih =>
    rw [SourceWord.nonSimpleDims_power_succ]
    refine ⟨ih,?_⟩
    rw [sourceBlocks_action,vector_encode,ReflectionReduction.sourceBlocks_eq,hd]
    have he : ReflectionReduction.translate x (-↑n*0)=x := by
      cases x
      simp [ReflectionReduction.translate]
    rw [he]
    exact source_power_zero_defect_nonsimple 6 x hd hne

/-- No nonzero morphisms from a positive-defect indecomposable to a
zero-defect indecomposable over any field. -/
theorem positive_to_zero_hom_zero {K : Type} [Field K]
    (R S : Rep K inwardE6)
    [∀ v, FiniteDimensional K (R.space v)] [∀ v, FiniteDimensional K (S.space v)]
    (hR : Indecomposable R) (hS : Indecomposable S)
    (hpos : 0 < ReflectionReduction.defect (vector (dimension R)))
    (hzero : ReflectionReduction.defect (vector (dimension S))=0)
    (f : Hom R S) : f=Hom.zero R S := by
  obtain ⟨n,hn⟩ := ReflectionReduction.positive_defect_terminates (vector (dimension R)) hpos
  have hx : encode (vector (dimension S)) ≠ fun _ => 0 := by
    rw [encode_vector]
    exact indecomposable_dimension_nonzero S hS
  have hc : (sourceBlockWord.power n).NonSimpleDims (dimension S) := by
    simpa only [encode_vector] using source_blocks_zero_defect_nonsimple n (vector (dimension S)) hzero hx
  have hs := (sourceBlockWord.power n).valid_of_dims S hS hc
  apply (sourceBlockWord.power n).hom_zero_of_negative R S hR hs.1 E6Vertex.center _ f
  rw [sourceBlocks_action]
  exact hn

end UploadBroadcast.RegularHomVanishing
