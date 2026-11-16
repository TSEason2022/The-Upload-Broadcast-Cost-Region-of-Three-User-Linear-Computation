import UploadBroadcast.NonzeroSameChart
import UploadBroadcast.GeometricUploadConverse
import UploadBroadcast.ResidualOperational

/-! Original-field same-chart relays attain the operational upload infimum,
including nonlinear codes, arbitrary blocklengths, and closure. -/
namespace UploadBroadcast.NonzeroSameChartOptimality
open Module Profile NonzeroDefectProfile NonzeroFamilyRanks NonzeroDefectRelays
set_option maxHeartbeats 3000000
variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- The actual signal-intersection bridge follows from full family ranks. -/
theorem full_signal_bridge (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) :
    T.U 2 ⊔ (T.U 0 ⊓ T.U 1) = ⊤ := by
  have hc := full_rankConditions T hT g n hn h
  have hu : T.U 0 ≤ T.U 2 ⊔ (T.U 0 ⊓ T.U 1) := by
    calc
      T.U 0 = (T.U 0 ⊓ T.U 1) ⊔ (T.U 0 ⊓ T.U 2) :=
        (hc.pair_intersections_span 0 1 2 (by decide) (by decide) (by decide)).symm
      _ ≤ T.U 2 ⊔ (T.U 0 ⊓ T.U 1) := sup_le le_sup_right (inf_le_right.trans le_sup_left)
  apply top_unique
  rw [←hc.pair_span 2 0 (by decide)]
  exact sup_le le_sup_left hu

/-- The family rank f−χ is precisely the nonlinear converse expression. -/
theorem family_converse_arithmetic (g : Family) (n : ℕ) (hn : 1 ≤ n) :
    ((fullAmbient g n-codimension g : ℕ) : ℝ) =
      2 * (fullAmbient g n : ℝ) -
        ((fullSide g n 0 : ℝ) + fullSide g n 1 + fullSide g n 2) := by
  have h : 2*fullAmbient g n = (fullAmbient g n-codimension g) +
      (fullSide g n 0 + fullSide g n 1 + fullSide g n 2) := by
    cases g <;> simp [fullAmbient,fullSide,codimension] <;> omega
  have hr := congrArg (fun t : ℕ => (t : ℝ)) h
  push_cast at hr
  linarith

/-- Genuine nonlinear converse for each actual indecomposable in the eight
families. Only dimensions and indecomposability are inputs. -/
theorem family_code_lower [Finite K] {L : ℕ} {m : Three → ℕ} {s : ℕ}
    (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n)
    (c : T.Code L (fun i => Fin (m i)) (Fin s)) (hL : 0 < L) :
    ((fullAmbient g n-codimension g : ℕ) : ℝ) ≤ c.uploadCost := by
  have hd (i j : Three) (hij : i ≠ j) : Disjoint (T.A i) (T.A j) :=
    disjoint_iff.mpr (full_side_pair_eq_bot T hT g n hn h i j hij)
  have ha : T.A 0 ⊔ T.A 1 ⊔ T.A 2 = ⊤ := by
    simpa only [Task.Spanning,Profile.three_iSup] using full_spanning T hT g n hn h
  have hh := GeometricUploadConverse.code_lower T (hd 0 1 (by decide))
    (hd 0 2 (by decide)) (hd 1 2 (by decide)) ha
    (full_rankConditions T hT g n hn h).pair_span (full_signal_bridge T hT g n hn h) c hL
  rw [h.ambient,h.side,h.side,h.side,←family_converse_arithmetic g n hn] at hh
  exact hh

/-- Any locally generated feasible relay with the constructed family rank
attains U*, proved with an actual scalar code and a nonlinear converse. -/
theorem relay_rank_eq_uploadOptimum [Finite K]
    (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n)
    (P : Submodule K F) (hg : T.LocallyGenerated P) (hf : T.RelayFeasible P)
    (hd : finrank K P = fullAmbient g n-codimension g) :
    (finrank K P : ℝ) = T.uploadOptimum := by
  obtain ⟨owner,c,hc⟩ := ResidualOperational.finiteCode_of_local_relay T P hg hf
  letI := c.finite_upload
  letI := c.finite_broadcast
  symm
  apply Task.uploadOptimum_eq_of_code c.toCode (by decide) _ hc
  intro L m s d hL
  rw [hd]
  exact family_code_lower T hT g n hn h d hL

/-- Source `lem:same-chart`, canonical arm order: all full and induced
fifteen-entry profiles and equality to the actual upload optimum. -/
theorem same_chart_full_and_optimal_relay [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) :
    (∀ r : Fin 6, entry T (.inl r) = (fullFirst g n r : ℝ)) ∧
    (∀ i ell : Three, 2 * entry T (.inr (i,ell)) = (doubledSecond g n : ℝ)) ∧
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P = fullAmbient g n-codimension g ∧
      (finrank K P : ℝ) = T.uploadOptimum ∧
      (∑ i, finrank K ↥(P ⊓ T.A i)) = finrank K P ∧
      (∀ r : Fin 6, entry (inducedTask T P hg) (.inl r) =
        (fullFirst g n r : ℝ) + (firstIncrement g r : ℝ)) ∧
      (∀ i ell : Three, 2 * entry (inducedTask T P hg) (.inr (i,ell)) =
        (doubledSecond g n : ℝ)) := by
  obtain ⟨h₁,h₂,P,hg,hf,hd,hu,h₃,h₄⟩ := NonzeroSameChart.same_chart_full_and_relay hq T hT g n hn h
  exact ⟨h₁,h₂,P,hg,hf,hd,relay_rank_eq_uploadOptimum T hT g n hn h P hg hf hd,hu,h₃,h₄⟩

end UploadBroadcast.NonzeroSameChartOptimality
