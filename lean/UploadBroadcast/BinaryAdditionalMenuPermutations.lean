import UploadBroadcast.BinaryMenuPermutations

/-! Additional binary choices, charges, and exceptions for every original
user labeling. Capacity and charge coordinates are relabeled together. -/
namespace UploadBroadcast.BinaryAdditionalMenuPermutations
open Module Profile NonzeroDefectRelays NonzeroDefectProfile NonzeroFamilyRanks
open NonzeroBinaryMenus R2PermutedMenus
variable {K F : Type} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

theorem additional_optimal_permuted (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (p : Equiv.Perm Three) (g : Kind) (n : ℕ) (hn : 1≤n)
    (h : Dimensions (reindexTask p T) (family g) n) (k : Fin 6) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (finrank K P : ℝ)=T.uploadOptimum ∧
      (∀ r : Fin 6, entry (reindexTask p (inducedTask T P hl)) (.inl r) ≤
        entry (reindexTask p T) (.inl r)+(menu g k r : ℝ)) ∧
      (∀ r : Three × Three, entry (reindexTask p (inducedTask T P hl)) (.inr r)=
        entry (reindexTask p T) (.inr r)) := by
  obtain ⟨P,hl,hf,hd,he,hq⟩ := full_binary_menu (reindexTask p T)
    (TaskUserPermutation.reindex_indecomposable T p hT) g n hn h k
  have hl' := (reindex_locallyGenerated T p P).mp hl
  have hf' := (reindex_relayFeasible T p P).mp hf
  refine ⟨P,hl',hf',?_,he,hq⟩
  apply NonzeroSameChartPermutations.relay_rank_eq_uploadOptimum_permuted
    T hT p (family g) n hn h P hl' hf'
  simpa [codimension,show family g≠.R2 by cases g <;> decide] using hd

theorem additional_fits_permuted (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (p : Equiv.Perm Three) (g : Kind) (hg1 : g≠.T1) (hgO : g≠.O)
    (n : ℕ) (hn : 1≤n) (h : Dimensions (reindexTask p T) (family g) n)
    (c : Fin 6 → ℕ)
    (hcap : ∀ a : Three, BinaryMenuAllocation.charge (extraFamily g) a ≤
      c (BinaryMenuAllocation.pairLeft a)+c (BinaryMenuAllocation.pairRight a)) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (finrank K P : ℝ)=T.uploadOptimum ∧
      (∀ r : Fin 6, entry (reindexTask p (inducedTask T P hl)) (.inl r) ≤
        entry (reindexTask p T) (.inl r)+(c r : ℝ)) ∧
      (∀ r : Three × Three, entry (reindexTask p (inducedTask T P hl)) (.inr r)=
        entry (reindexTask p T) (.inr r)) := by
  obtain ⟨k,hk⟩ := BinaryMenuAllocation.menu_fits (extraFamily g) c hcap
  obtain ⟨P,hl,hf,hu,he,hq⟩ := additional_optimal_permuted T hT p g n hn h k
  refine ⟨P,hl,hf,hu,?_,hq⟩
  intro r
  apply (he r).trans
  apply add_le_add_left
  have hm : menu g k r = BinaryMenuAllocation.menu (extraFamily g) k r := by
    cases g <;> simp_all [menu,extraFamily]
  rw [hm]
  exact_mod_cast hk r

theorem r2_optimal_permuted (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (p : Equiv.Perm Three) (n : ℕ) (hn : 1≤n)
    (h : Dimensions (reindexTask p T) .R2 n) (k : Fin 6) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (finrank K P : ℝ)=T.uploadOptimum ∧
      (∀ r : Fin 6, entry (reindexTask p (inducedTask T P hl)) (.inl r) ≤
        entry (reindexTask p T) (.inl r)+(BinaryMenuAllocation.menu .R2 k r : ℝ)) ∧
      (∀ r : Three × Three, entry (reindexTask p (inducedTask T P hl)) (.inr r)=
        entry (reindexTask p T) (.inr r)) := by
  obtain ⟨P,hl,hf,hd,he,hq⟩ := full_binary_R2_menu (reindexTask p T)
    (TaskUserPermutation.reindex_indecomposable T p hT) n hn h k
  have hl' := (reindex_locallyGenerated T p P).mp hl
  have hf' := (reindex_relayFeasible T p P).mp hf
  refine ⟨P,hl',hf',?_,he,hq⟩
  apply NonzeroSameChartPermutations.relay_rank_eq_uploadOptimum_permuted
    T hT p .R2 n hn h P hl' hf'
  norm_num [fullAmbient,codimension]
  omega

theorem r2_fits_permuted (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (p : Equiv.Perm Three) (n : ℕ) (hn : 2≤n)
    (h : Dimensions (reindexTask p T) .R2 n) (c : Fin 6 → ℕ)
    (hcap : ∀ a : Three, 1≤c (BinaryMenuAllocation.pairLeft a)+c (BinaryMenuAllocation.pairRight a)) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (finrank K P : ℝ)=T.uploadOptimum ∧
      (∀ r : Fin 6, entry (reindexTask p (inducedTask T P hl)) (.inl r) ≤
        entry (reindexTask p T) (.inl r)+(c r : ℝ)) ∧
      (∀ r : Three × Three, entry (reindexTask p (inducedTask T P hl)) (.inr r)=
        entry (reindexTask p T) (.inr r)) := by
  obtain ⟨k,hk⟩ := BinaryMenuAllocation.menu_fits .R2 c (by
    intro a
    have hh := hcap a
    fin_cases a <;> simpa [BinaryMenuAllocation.charge] using hh)
  obtain ⟨P,hl,hf,hu,he,hq⟩ := r2_optimal_permuted T hT p n (by omega) h k
  exact ⟨P,hl,hf,hu,fun r => (he r).trans (add_le_add_left (by exact_mod_cast hk r) _),hq⟩

theorem exceptions_permuted (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (p : Equiv.Perm Three) (g : Family) (hg : g=.T3 ∨ g=.H ∨ g=.R2)
    (h : Dimensions (reindexTask p T) g 1) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (finrank K P : ℝ)=T.uploadOptimum ∧
      ∀ r : Index, entry (reindexTask p (inducedTask T P hl)) r ≤ entry (reindexTask p T) r := by
  have hi := TaskUserPermutation.reindex_indecomposable T p hT
  have hex : ∃ P : Submodule K F, ∃ hl : (reindexTask p T).LocallyGenerated P,
      (reindexTask p T).RelayFeasible P ∧ finrank K P=fullAmbient g 1-codimension g ∧
      ∀ r : Index, entry (inducedTask (reindexTask p T) P hl) r ≤ entry (reindexTask p T) r := by
    rcases hg with rfl | hg
    · obtain ⟨P,hl,hf,hd,he⟩ := NonzeroExceptionalRelays.full_tripod_exception_profile _ hi h
      exact ⟨P,hl,hf,by simpa [fullAmbient,codimension] using hd,he⟩
    · obtain ⟨P,hl,hf,hd,he⟩ := NonzeroExceptionalRelays.full_small_exception_profile _ hi g hg h
      refine ⟨P,hl,hf,?_,he⟩
      rcases hg with rfl | rfl <;> simpa [fullAmbient,codimension] using hd
  obtain ⟨P,hl,hf,hd,he⟩ := hex
  have hl' := (reindex_locallyGenerated T p P).mp hl
  have hf' := (reindex_relayFeasible T p P).mp hf
  refine ⟨P,hl',hf',NonzeroSameChartPermutations.relay_rank_eq_uploadOptimum_permuted
    T hT p g 1 (by decide) h P hl' hf' hd,?_⟩
  exact he

end UploadBroadcast.BinaryAdditionalMenuPermutations
