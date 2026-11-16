import UploadBroadcast.Model
import Mathlib.Topology.Order.Basic

/-! The final topological assembly of the region theorem. The construction
of the corner and the operational lower bounds are explicit hypotheses, not
unproved axioms. This file alone does not prove the paper's main theorem. -/
namespace UploadBroadcast
namespace Task
variable {K F : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] (T : Task K F)

/-- Coordinatewise upper-budget rectangle. -/
def budgetRectangle (u d : ℝ) : Set (ℝ × ℝ) :=
  {b | u ≤ b.1 ∧ d ≤ b.2}

theorem isClosed_budgetRectangle (u d : ℝ) : IsClosed (budgetRectangle u d) := by
  exact (isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_const continuous_snd)

/-- Exact reduction of the paper's region equality to its two independent
converses and a blocklength-two corner construction. -/
theorem region_eq_rectangle_of_corner (u d : ℝ)
    (hcorner : (u,d) ∈ T.achievableAt 2)
    (hlower : ∀ L b, b ∈ T.achievableAt L → u ≤ b.1 ∧ d ≤ b.2) :
    T.achievableAt 2 = budgetRectangle u d ∧
    T.costRegion = budgetRectangle u d := by
  have htwo : T.achievableAt 2 = budgetRectangle u d := by
    ext b
    constructor
    · exact hlower 2 b
    · intro hb
      exact T.achievableAt_mono hcorner hb.1 hb.2
  refine ⟨htwo, ?_⟩
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro b hb
      rcases Set.mem_iUnion.mp hb with ⟨L,hL⟩
      exact hlower L b hL
    · exact isClosed_budgetRectangle u d
  · intro b hb
    apply subset_closure
    exact Set.mem_iUnion.mpr ⟨2, htwo.symm ▸ hb⟩

end Task
end UploadBroadcast
