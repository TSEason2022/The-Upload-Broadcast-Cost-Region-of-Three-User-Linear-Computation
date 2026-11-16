import UploadBroadcast.NonzeroHyperplaneUpload
import UploadBroadcast.R2ExactProfile

/-!
# Original-field same-chart relays for all eight nonzero-defect families

This combines actual quiver-reflection rank calculations and finite-field
kernel selection. The inputs contain only task indecomposability and its seven
family dimensions, with n >= 1 and at least three field elements.
-/
namespace UploadBroadcast.NonzeroSameChart
open Module Profile NonzeroDefectProfile NonzeroFamilyRanks NonzeroDefectRelays

variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- The relay-existence and all-fifteen profile content of `lem:same-chart`.
The displayed local-upload dimension is also proved for the actual relay. -/
theorem exists_same_chart_relay [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P = fullAmbient g n-codimension g ∧
      (∑ i, finrank K ↥(P ⊓ T.A i)) = finrank K P ∧
      (∀ r : Fin 6, entry (inducedTask T P hg) (.inl r) =
        (fullFirst g n r : ℝ) + (firstIncrement g r : ℝ)) ∧
      (∀ i ell : Three, 2 * entry (inducedTask T P hg) (.inr (i,ell)) =
        (doubledSecond g n : ℝ)) := by
  by_cases hg : g = .R2
  · subst g
    obtain ⟨P,hgen,hf,hd,hu,hprofile⟩ :=
      R2ExactProfile.full_R2_profile_and_upload hq T hT n hn h
    refine ⟨P,hgen,hf,?_,hu,?_,?_⟩
    · simp only [fullAmbient,codimension,ite_true]
      omega
    · intro r
      rw [hprofile (.inl r),full_first_profile T hT .R2 n hn h r]
      fin_cases r <;> simp [firstIncrement]
    · intro i ell
      rw [hprofile (.inr (i,ell))]
      exact full_second_profile T hT .R2 n hn h i ell
  · obtain ⟨P,hgen,hf,hd,hu,hfirst,hsecond⟩ :=
      NonzeroHyperplaneUpload.exists_full_hyperplane_upload_profile hq T hT g hg n hn h
    refine ⟨P,hgen,hf,?_,hu.trans hd.symm,hfirst,hsecond⟩
    simpa only [codimension,if_neg hg] using hd

/-- Full-task profiles and a realizing relay, with no requested-profile or
geometric-rank hypotheses. -/
theorem same_chart_full_and_relay [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) :
    (∀ r : Fin 6, entry T (.inl r) = (fullFirst g n r : ℝ)) ∧
    (∀ i ell : Three, 2 * entry T (.inr (i,ell)) = (doubledSecond g n : ℝ)) ∧
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P = fullAmbient g n-codimension g ∧
      (∑ i, finrank K ↥(P ⊓ T.A i)) = finrank K P ∧
      (∀ r : Fin 6, entry (inducedTask T P hg) (.inl r) =
        (fullFirst g n r : ℝ) + (firstIncrement g r : ℝ)) ∧
      (∀ i ell : Three, 2 * entry (inducedTask T P hg) (.inr (i,ell)) =
        (doubledSecond g n : ℝ)) :=
  ⟨full_first_profile T hT g n hn h,full_second_profile T hT g n hn h,
    exists_same_chart_relay hq T hT g n hn h⟩

end UploadBroadcast.NonzeroSameChart
