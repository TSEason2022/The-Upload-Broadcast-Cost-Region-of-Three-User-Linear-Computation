import UploadBroadcast.AllocationWaterfill
import UploadBroadcast.Model
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-! Conditional ranks of actual coefficient subspaces satisfy the
hypotheses of the exact numerical LCBC allocation theorems. -/
namespace UploadBroadcast.Allocation
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Conditional rank is monotone in its first subspace. -/
theorem condRank_mono {C D : Submodule K F} (A : Submodule K F) (h : C ≤ D) :
    UploadBroadcast.condRank C A ≤ UploadBroadcast.condRank D A := by
  unfold UploadBroadcast.condRank
  exact Nat.sub_le_sub_right (Submodule.finrank_mono (sup_le_sup_left h A)) _

variable (A U : Fin 3 → Submodule K F)

noncomputable def commonRank : ℕ :=
  min (condRank (U 0 ⊓ U 1 ⊓ U 2) (A 0))
    (min (condRank (U 0 ⊓ U 1 ⊓ U 2) (A 1)) (condRank (U 0 ⊓ U 1 ⊓ U 2) (A 2)))

noncomputable def pairRank (i j : Fin 3) : ℕ :=
  min (condRank (U i ⊓ U j) (A i)) (condRank (U i ⊓ U j) (A j))

noncomputable def pairSumRank (i j k : Fin 3) : ℕ :=
  condRank ((U i ⊓ U j) ⊔ (U i ⊓ U k)) (A i)

noncomputable def enlargedRank (i j k : Fin 3) : ℕ :=
  condRank (U i ⊓ (U j ⊔ U k)) (A i)

noncomputable def demandRank (i : Fin 3) : ℕ := condRank (U i) (A i)

theorem commonRank_le (i : Fin 3) :
    commonRank A U ≤ condRank (U 0 ⊓ U 1 ⊓ U 2) (A i) := by
  fin_cases i
  · exact min_le_left _ _
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · exact le_trans (min_le_right _ _) (min_le_right _ _)

omit [FiniteDimensional K F] in
theorem common_le_signal (i : Fin 3) : U 0 ⊓ U 1 ⊓ U 2 ≤ U i := by
  fin_cases i
  · exact le_trans inf_le_left inf_le_left
  · exact le_trans inf_le_left inf_le_right
  · exact inf_le_right

theorem commonRank_le_pairRank (i j : Fin 3) : commonRank A U ≤ pairRank A U i j := by
  apply le_min
  · exact le_trans (commonRank_le A U i)
      (condRank_mono (A i) (le_inf (common_le_signal U i) (common_le_signal U j)))
  · exact le_trans (commonRank_le A U j)
      (condRank_mono (A j) (le_inf (common_le_signal U i) (common_le_signal U j)))

theorem pairRank_comm (i j : Fin 3) : pairRank A U i j = pairRank A U j i := by
  unfold pairRank
  rw [inf_comm (U i) (U j)]
  exact min_comm _ _

theorem pairRank_le_pairSumRank_left (i j k : Fin 3) :
    pairRank A U i j ≤ pairSumRank A U i j k :=
  le_trans (min_le_left _ _) (condRank_mono (A i) le_sup_left)

theorem pairRank_le_pairSumRank_right (i j k : Fin 3) :
    pairRank A U i k ≤ pairSumRank A U i j k :=
  le_trans (min_le_left _ _) (condRank_mono (A i) le_sup_right)

theorem pairSumRank_le_enlargedRank (i j k : Fin 3) :
    pairSumRank A U i j k ≤ enlargedRank A U i j k := by
  apply condRank_mono
  exact sup_le (inf_le_inf le_rfl le_sup_left) (inf_le_inf le_rfl le_sup_right)

theorem enlargedRank_le_demandRank (i j k : Fin 3) :
    enlargedRank A U i j k ≤ demandRank A U i := condRank_mono (A i) inf_le_left

/-- All numerical rank hypotheses follow from actual subspace inclusion;
no condition of the LP theorem is postulated for the task. -/
theorem actual_rank_bounds :
    RankBounds (commonRank A U) (pairRank A U 1 2) (pairRank A U 0 2) (pairRank A U 0 1)
      (pairSumRank A U 0 1 2) (pairSumRank A U 1 0 2) (pairSumRank A U 2 0 1)
      (enlargedRank A U 0 1 2) (enlargedRank A U 1 0 2) (enlargedRank A U 2 0 1) := by
  have h₁ := commonRank_le_pairRank A U 1 2
  have h₂ := commonRank_le_pairRank A U 0 2
  have h₃ := commonRank_le_pairRank A U 0 1
  have h₂₁ := pairRank_le_pairSumRank_right A U 0 1 2
  have h₃₁ := pairRank_le_pairSumRank_left A U 0 1 2
  have h₁₂ := pairRank_le_pairSumRank_right A U 1 0 2
  have h₃₂ := pairRank_le_pairSumRank_left A U 1 0 2
  rw [pairRank_comm A U 1 0] at h₃₂
  have h₁₃ := pairRank_le_pairSumRank_right A U 2 0 1
  rw [pairRank_comm A U 2 1] at h₁₃
  have h₂₃ := pairRank_le_pairSumRank_left A U 2 0 1
  rw [pairRank_comm A U 2 0] at h₂₃
  have hb₁ := pairSumRank_le_enlargedRank A U 0 1 2
  have hb₂ := pairSumRank_le_enlargedRank A U 1 0 2
  have hb₃ := pairSumRank_le_enlargedRank A U 2 0 1
  unfold RankBounds
  exact ⟨by exact_mod_cast Nat.zero_le (commonRank A U),
    by exact_mod_cast h₁,by exact_mod_cast h₂,by exact_mod_cast h₃,
    by exact_mod_cast h₂₁,by exact_mod_cast h₃₁,by exact_mod_cast h₁₂,
    by exact_mod_cast h₃₂,by exact_mod_cast h₁₃,by exact_mod_cast h₂₃,
    by exact_mod_cast hb₁,by exact_mod_cast hb₂,by exact_mod_cast hb₃⟩

/-- The paper's demand dimension formula, requiring only Aᵢ≤Uᵢ. -/
theorem demandRank_eq_finrank_sub (i : Fin 3) (h : A i ≤ U i) :
    demandRank A U i = Module.finrank K (U i)-Module.finrank K (A i) := by
  unfold demandRank condRank
  rw [sup_eq_right.mpr h]

/-- Every triple of actual coefficient subspaces has the claimed integer
allocation at the ceiling of its numerical LP optimum. This uses no upload
feasibility assumption and no operational coding theorem. -/
theorem actual_integer_lcbc_allocation :
    let r : ℤ := commonRank A U
    let u₁ : ℤ := pairRank A U 1 2
    let u₂ : ℤ := pairRank A U 0 2
    let u₃ : ℤ := pairRank A U 0 1
    let p₁ : ℤ := pairSumRank A U 0 1 2
    let p₂ : ℤ := pairSumRank A U 1 0 2
    let p₃ : ℤ := pairSumRank A U 2 0 1
    let b₁ : ℤ := enlargedRank A U 0 1 2
    let b₂ : ℤ := enlargedRank A U 1 0 2
    let b₃ : ℤ := enlargedRank A U 2 0 1
    let m₁ : ℤ := demandRank A U 0
    let m₂ : ℤ := demandRank A U 1
    let m₃ : ℤ := demandRank A U 2
    ∃ X Y Z a : ℤ,
      LCBCFeasible r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ r X Y Z a ∧
      0 ≤ m₁-r-Y-Z-a ∧ 0 ≤ m₂-r-X-Z-a ∧ 0 ≤ m₃-r-X-Y-a ∧
      m₁+m₂+m₃-2*r-X-Y-Z-a =
        ⌈lcbcCostValue r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ (m₁+m₂+m₃)⌉ := by
  dsimp only
  apply integer_lcbc_cost_ceiling
  · simpa only [Int.cast_natCast] using actual_rank_bounds A U
  · exact_mod_cast enlargedRank_le_demandRank A U 0 1 2
  · exact_mod_cast enlargedRank_le_demandRank A U 1 0 2
  · exact_mod_cast enlargedRank_le_demandRank A U 2 0 1

end UploadBroadcast.Allocation
