import UploadBroadcast.SourceMainTheorem
import UploadBroadcast.BinaryMenuOptimality
import UploadBroadcast.ResidualRowPaperEndpoint

/-! Current public interfaces. These combine existing proofs while retaining
an explicit menu witness and the current nonlinear obstruction formulation.
No manuscript text is embedded here. -/
namespace UploadBroadcast.CurrentSourceAlignment
open Module Profile NonzeroDefectRelays NonzeroDefectProfile NonzeroFamilyRanks
open NonzeroBinaryMenus
variable {K F : Type} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- An optimal relay is realized for each listed vector, not merely for a
choice made after seeing capacities. -/
theorem every_listed_additional_bound (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Kind) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T (family g) n)
    (d : Fin 6 → ℕ) (hd : ∃ k : Fin 6, d = menu g k) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (finrank K P : ℝ) = T.uploadOptimum ∧
      (∀ r : Fin 6, entry (inducedTask T P hl) (.inl r) ≤ entry T (.inl r)+(d r : ℝ)) ∧
      (∀ r : Three × Three, entry (inducedTask T P hl) (.inr r) = entry T (.inr r)) := by
  obtain ⟨k, rfl⟩ := hd
  exact BinaryMenuOptimality.additional_optimal_menu T hT g n hn h k

/-- The selected vector itself, its capacity bound, and its operational relay
are returned together. This preserves the quantifier order of menu selection. -/
theorem additional_bound_and_relay_fit (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Kind) (hT1 : g ≠ .T1) (hO : g ≠ .O)
    (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T (family g) n) (b : Fin 6 → ℕ)
    (hcap : ∀ p : Fin 3, BinaryMenuAllocation.charge (extraFamily g) p ≤
      b (BinaryMenuAllocation.pairLeft p)+b (BinaryMenuAllocation.pairRight p)) :
    ∃ k : Fin 6, (∀ r, menu g k r ≤ b r) ∧
      ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
        T.RelayFeasible P ∧ (finrank K P : ℝ) = T.uploadOptimum ∧
        (∀ r : Fin 6, entry (inducedTask T P hl) (.inl r) ≤
          entry T (.inl r)+(menu g k r : ℝ)) ∧
        (∀ r : Three × Three, entry (inducedTask T P hl) (.inr r) = entry T (.inr r)) := by
  obtain ⟨k, hk⟩ := BinaryMenuAllocation.menu_fits (extraFamily g) b hcap
  have hm : menu g = BinaryMenuAllocation.menu (extraFamily g) := by
    cases g
    · exact False.elim (hT1 rfl)
    · exact False.elim (hO rfl)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  refine ⟨k, ?_, BinaryMenuOptimality.additional_optimal_menu T hT g n hn h k⟩
  simpa only [hm] using hk

/-- R2 has a separate codimension-two construction with the same explicit
selected-vector interface. -/
theorem r2_bound_and_relay_fit (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (n : ℕ) (hn : 2 ≤ n) (h : Dimensions T .R2 n) (b : Fin 6 → ℕ)
    (hcap : ∀ p : Fin 3, BinaryMenuAllocation.charge .R2 p ≤
      b (BinaryMenuAllocation.pairLeft p)+b (BinaryMenuAllocation.pairRight p)) :
    ∃ k : Fin 6, (∀ r, BinaryMenuAllocation.menu .R2 k r ≤ b r) ∧
      ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
        T.RelayFeasible P ∧ (finrank K P : ℝ) = T.uploadOptimum ∧
        (∀ r : Fin 6, entry (inducedTask T P hl) (.inl r) ≤
          entry T (.inl r)+(BinaryMenuAllocation.menu .R2 k r : ℝ)) ∧
        (∀ r : Three × Three, entry (inducedTask T P hl) (.inr r) = entry T (.inr r)) := by
  obtain ⟨k, hk⟩ := BinaryMenuAllocation.menu_fits .R2 b hcap
  exact ⟨k, hk, BinaryMenuOptimality.r2_optimal_menu T hT n (by omega) h k⟩

/-- A concrete binary task has a two-instance optimal linear code but no
one-instance nonlinear code at the broadcast minimum, hence none at both minima. -/
theorem binary_task_requires_two_instances :
    BinaryOperationalTightness.task.LinearJointAt 2 ∧
      ∀ (m : Three → ℕ) (s : ℕ)
        (c : BinaryOperationalTightness.task.Code 1 (fun i => Fin (m i)) (Fin s)),
        c.broadcastCost ≠ broadcastOptimum
          BinaryOperationalTightness.task.A BinaryOperationalTightness.task.U := by
  refine ⟨nonlinear_uniform_bound_tight.1, ?_⟩
  intro m s c
  exact ne_of_gt (nonlinear_uniform_bound_tight.2 m s c)

end UploadBroadcast.CurrentSourceAlignment
