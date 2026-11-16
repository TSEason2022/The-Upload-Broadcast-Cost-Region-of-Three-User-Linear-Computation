import UploadBroadcast.ResidualComponentClassification
import UploadBroadcast.BoundaryComponentMenus
import UploadBroadcast.NonzeroSameChartPermutations

/-! The profile-preserving half of source `thm:profiles`, for every actual
active residual indecomposable outside the listed exceptional menus. -/
namespace UploadBroadcast.ResidualProfileCompleteness
open Module Profile NonzeroDefectProfile NonzeroFamilyRanks NonzeroDefectRelays
open ResidualComponentAdditivity ResidualComponentClassification
variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Membership in the source table, retaining actual arm labels and the
actual regular-family chart. T₁ at zero is exactly the three Z boundary rows. -/
def ListedExceptional (T : Task K F) : Prop :=
  (∃ (k : Fin 6) (n : ℕ), Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) .T1 n) ∨
  (∃ (k : Fin 6) (n : ℕ), 1 ≤ n ∧ Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) .O n) ∨
  (∃ (n : ℕ) (e : F ≃ₗ[K] ResonantEndomorphisms.Ambient K (JordanResonance.V K n)),
    mapTask e T = ResonantRelay.jordanTask K n)

/-- Every nonlisted actual residual indecomposable has an upload-optimal
relay preserving all fifteen entries. The zero-excess case and the surviving
T₂ zero-index boundary are included. -/
theorem outside_table_profile_preserving [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : Task K F) (h : ActiveResidual T)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (hout : ¬ ListedExceptional T) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (finrank K P : ℝ) = T.uploadOptimum ∧
      ∀ r : Profile.Index, entry (inducedTask T P hl) r = entry T r := by
  obtain hz | hp := residual_exhaustion T h hi
  · obtain ⟨hu,hl,hf,hprofile⟩ := zero_excess_full_relay T h hz
    refine ⟨⊤,hl,hf,?_,?_⟩
    · simpa only [finrank_top] using hu.symm
    · intro r
      simpa only [Task.inducedRelay_entry] using hprofile r
  · rcases hp with ⟨k,⟨g,n,hn,hd⟩ | hd | hd⟩ | hregular
    · have hgT : g ≠ .T1 := by
        rintro rfl
        exact hout (Or.inl ⟨k,n,hd⟩)
      have hgO : g ≠ .O := by
        rintro rfl
        exact hout (Or.inr (Or.inl ⟨k,n,hn,hd⟩))
      obtain ⟨P,hl,hf,_,hu,hprofile⟩ :=
        NonzeroSameChartPermutations.other_families_profile_preserving hq T hi k g hgT hgO n hn hd
      exact ⟨P,hl,hf,hu,hprofile⟩
    · exact False.elim (hout (Or.inl ⟨k,0,hd⟩))
    · obtain ⟨P,hl,hf,_,hu,hprofile⟩ := BoundaryComponentMenus.T2_permuted_preserving T hi k hd
      exact ⟨P,hl,hf,hu,hprofile⟩
    · exact False.elim (hout (Or.inr (Or.inr hregular)))

end UploadBroadcast.ResidualProfileCompleteness
