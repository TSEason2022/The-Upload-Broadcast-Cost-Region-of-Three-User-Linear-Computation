import UploadBroadcast.BinaryMenuOptimality
import UploadBroadcast.NonzeroSameChartPermutations

/-! Exact original binary menus in every actual user labeling. -/
namespace UploadBroadcast.BinaryMenuPermutations
open Module Profile NonzeroDefectRelays NonzeroDefectProfile NonzeroFamilyRanks
open NonzeroBinaryMenus R2PermutedMenus
variable {K F : Type} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

theorem original_exact_optimal_permuted (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (p : Equiv.Perm Three) (g : Kind) (hg : g=.T1 ∨ g=.O)
    (n : ℕ) (hn : 1 ≤ n) (h : Dimensions (reindexTask p T) (family g) n) (k : Fin 6) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (finrank K P : ℝ)=T.uploadOptimum ∧
      (∀ r : Fin 6, entry (reindexTask p (inducedTask T P hl)) (.inl r)=
        entry (reindexTask p T) (.inl r)+(menu g k r : ℝ)) ∧
      (∀ r : Three × Three, entry (reindexTask p (inducedTask T P hl)) (.inr r)=
        entry (reindexTask p T) (.inr r)) := by
  obtain ⟨P,hl,hf,hd,he,hq⟩ := BinaryExactFamilyMenus.full_original_binary_exact_menu
    (reindexTask p T) (TaskUserPermutation.reindex_indecomposable T p hT) g hg n hn h k
  have hl' : T.LocallyGenerated P := (reindex_locallyGenerated T p P).mp hl
  have hf' : T.RelayFeasible P := (reindex_relayFeasible T p P).mp hf
  refine ⟨P,hl',hf',?_,he,hq⟩
  apply NonzeroSameChartPermutations.relay_rank_eq_uploadOptimum_permuted T hT p (family g) n hn h P hl' hf'
  simpa [codimension,show family g≠.R2 by cases g <;> decide] using hd

end UploadBroadcast.BinaryMenuPermutations
