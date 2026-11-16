import UploadBroadcast.ResidualProfileCompleteness
import UploadBroadcast.RegularExactMenus

/-! Source `thm:profiles`: exhaustive profile preservation outside the listed
families, and every listed exact optimal relay menu on the original task. -/
namespace UploadBroadcast.ResidualProfiles
open Module Profile NonzeroDefectProfile NonzeroFamilyRanks NonzeroDefectRelays
open ResidualComponentAdditivity ResidualProfileCompleteness
variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Every choice is a genuine original-space relay, upload-optimal for the
nonlinear operational problem, with the entire exact fifteen-entry increment. -/
def OptimalExactMenu [Finite K] (T : Task K F) (inc : Three → Profile.Index → ℝ) : Prop :=
  ∀ choice : Three, ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
    T.RelayFeasible P ∧ (finrank K P : ℝ) = T.uploadOptimum ∧
    ∀ r : Profile.Index, entry (inducedTask T P hl) r = entry T r + inc choice r

/-- First-entry changes are in the original arm order; all nine Q increments
are zero. Repeated T₁ choices simply pad its two-element menu. -/
def permutedIncrement (g : Family) (k : Fin 6) (choice : Three) : Profile.Index → ℝ
  | .inl r => NonzeroSameChartMenus.menuIncrement g choice (R2PermutedMenus.inverseFirst k r)
  | .inr _ => 0

/-- Exact menus for every actual positive-index nonzero-defect family. -/
theorem positive_index_menu [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : Task K F)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (k : Fin 6) (n : ℕ) (hn : 1 ≤ n)
    (hd : Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) g n) :
    OptimalExactMenu T (permutedIncrement g k) := by
  intro choice
  obtain ⟨hfull,hQ,P,hl,hf,_,hu,_,hfirst,hsecond⟩ :=
    NonzeroSameChartPermutations.same_chart_all_permuted_choices hq T hi k g n hn hd choice
  refine ⟨P,hl,hf,hu,?_⟩
  rintro (r | ⟨i,l⟩)
  · rw [hfirst,hfull]
    rfl
  · have h₁ := hsecond i l
    have h₂ := hQ i l
    change _ = _ + 0
    linarith only [h₁,h₂]

/-- The same original-order interface covers all three Z boundary rows. -/
theorem boundary_menu [Finite K] (T : Task K F)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (k : Fin 6) (hd : Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) .T1 0) :
    OptimalExactMenu T (permutedIncrement .T1 k) := by
  intro choice
  obtain ⟨P,hl,hf,_,hu,hfirst,hsecond⟩ :=
    BoundaryComponentMenus.T1_all_permuted_choices T hi k hd choice
  refine ⟨P,hl,hf,hu,?_⟩
  rintro (r | ⟨i,l⟩)
  · exact hfirst r
  · simpa only [permutedIncrement,add_zero] using hsecond i l

/-- Exact original-task R_n menus; its index n denotes source R_(n+1). -/
theorem regular_menu [Finite K] (T : Task K F) (ha : ActiveResidual T) (n : ℕ)
    (e : F ≃ₗ[K] ResonantEndomorphisms.Ambient K (JordanResonance.V K n))
    (he : mapTask e T = ResonantRelay.jordanTask K n) :
    OptimalExactMenu T ResonantFiniteAssembly.increment := by
  intro choice
  obtain ⟨P,hl,hf,_,hu,hfirst,hsecond⟩ := RegularExactMenus.from_actual_chart T ha n e he choice
  refine ⟨P,hl,hf,hu,?_⟩
  rintro (r | ⟨i,l⟩)
  · exact hfirst r
  · simpa only [ResonantFiniteAssembly.increment,add_zero] using hsecond i l

/-- Source `thm:profiles`, in one source-facing statement. The first clause
uses the actual exhaustive component classification, including zero excess.
The remaining clauses realize every listed T₁/O/Z/R menu, and by definition
preserve every one of the nine Q entries. -/
theorem profiles [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : Task K F) (ha : ActiveResidual T)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤) :
    (¬ ListedExceptional T →
      ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
        T.RelayFeasible P ∧ (finrank K P : ℝ) = T.uploadOptimum ∧
        ∀ r : Profile.Index, entry (inducedTask T P hl) r = entry T r) ∧
    (∀ (k : Fin 6) (n : ℕ),
      Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) .T1 n →
        OptimalExactMenu T (permutedIncrement .T1 k)) ∧
    (∀ (k : Fin 6) (n : ℕ), 1 ≤ n →
      Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) .O n →
        OptimalExactMenu T (permutedIncrement .O k)) ∧
    (∀ (n : ℕ) (e : F ≃ₗ[K] ResonantEndomorphisms.Ambient K (JordanResonance.V K n)),
      mapTask e T = ResonantRelay.jordanTask K n →
        OptimalExactMenu T ResonantFiniteAssembly.increment) := by
  refine ⟨outside_table_profile_preserving hq T ha hi,?_,?_,regular_menu T ha⟩
  · intro k n hd
    by_cases hn : n = 0
    · subst n
      exact boundary_menu T hi k hd
    · exact positive_index_menu hq T hi .T1 k n (by omega) hd
  · intro k n hn hd
    exact positive_index_menu hq T hi .O k n hn hd

end UploadBroadcast.ResidualProfiles
