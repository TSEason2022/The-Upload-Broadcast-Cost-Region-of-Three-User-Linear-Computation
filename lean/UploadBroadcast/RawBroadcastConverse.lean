import UploadBroadcast.BroadcastOperational
import UploadBroadcast.AllocationProfile

set_option maxHeartbeats 1000000

namespace UploadBroadcast.BroadcastOperational
open MeasureTheory ProbabilityTheory
variable {K F S : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] [Finite S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Fully informed all-fifteen lower bound, with no upload feasibility hypothesis. -/
theorem rawRankBound_le_cost {L : ℕ} (hL : 0 < L) (s : Source K F L → S)
    (A U : Three → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (decode : ∀ i, S → Source K (A i) L → Source K (U i) L)
    (hz : ∀ x i, decode i (s x) (observe K F (A i) x) = observe K F (U i) x) :
    Allocation.rawRankBound A U ≤
      Real.logb (Nat.card K) (Nat.card (Set.range s)) / L := by
  have hd (i : Three) : (Allocation.demandRank A U i : ℝ) =
      (Module.finrank K (U i) : ℝ) - Module.finrank K (A i) := by
    rw [Allocation.demandRank_eq_finrank_sub A U i (hAU i), Nat.cast_sub (Submodule.finrank_mono (hAU i))]
  apply Finset.sup'_le
  intro r _
  cases r with
  | inl r =>
    have hh := first_family hL s A U hAU decode hz
      (Profile.firstOrder r).1 (Profile.firstOrder r).2.1 (Profile.firstOrder r).2.2
    fin_cases r <;>
      dsimp [Allocation.rawEntry, Allocation.rawFirstEntry, Profile.firstOrder] at hh ⊢ <;>
      simp only [hd] <;> linarith
  | inr r =>
    obtain ⟨i,ell⟩ := r
    fin_cases i
    · have he : ell = 0 ∨ ell = 1 ∨ ell = 2 := by fin_cases ell <;> decide
      have hh := second_family hL s A U hAU decode hz 0 1 2 ell he
      change Allocation.rawSecondEntry A U 0 1 2 ell ≤ _
      simp only [Allocation.rawSecondEntry, hd, inf_assoc, inf_left_comm, inf_comm]
      simp only [inf_assoc, inf_left_comm, inf_comm] at hh
      linarith
    · have he : ell = 1 ∨ ell = 2 ∨ ell = 0 := by fin_cases ell <;> decide
      have hh := second_family hL s A U hAU decode hz 1 2 0 ell he
      change Allocation.rawSecondEntry A U 1 2 0 ell ≤ _
      simp only [Allocation.rawSecondEntry, hd, inf_assoc, inf_left_comm, inf_comm]
      simp only [inf_assoc, inf_left_comm, inf_comm] at hh
      linarith
    · have he : ell = 2 ∨ ell = 0 ∨ ell = 1 := by fin_cases ell <;> decide
      have hh := second_family hL s A U hAU decode hz 2 0 1 ell he
      change Allocation.rawSecondEntry A U 2 0 1 ell ≤ _
      simp only [Allocation.rawSecondEntry, hd, inf_assoc, inf_left_comm, inf_comm]
      simp only [inf_assoc, inf_left_comm, inf_comm] at hh
      linarith

end UploadBroadcast.BroadcastOperational
