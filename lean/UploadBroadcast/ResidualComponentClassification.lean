import UploadBroadcast.ActiveComponentClassification
import UploadBroadcast.ResidualComponentAdditivity

/-! Source-facing exhaustive family assignment on intrinsic active residuals.
The active and non-omniscience exclusions are derived from residual geometry,
not supplied as extra classification certificates. -/
namespace UploadBroadcast.ResidualComponentClassification
open Module Profile NonzeroDefectProfile NonzeroFamilyRanks
open ActiveComponentClassification ResidualComponentAdditivity
variable {K F : Type} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- The actual dimension family in a concrete arm order, or an actual
coefficient chart to the regular resonant model. The low-index T₂ boundary
is deliberately separate from the eight positive-index families. -/
def PositiveAssignment (T : Task K F) : Prop :=
  (∃ k : Fin 6,
    (∃ (g : Family) (n : ℕ), 1 ≤ n ∧
      Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) g n) ∨
    Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) .T1 0 ∨
    Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) .T2 0) ∨
  (∃ (n : ℕ) (e : F ≃ₗ[K] ResonantEndomorphisms.Ambient K (JordanResonance.V K n)),
    mapTask e T = ResonantRelay.jordanTask K n)

/-- Positive-excess family assignment under the actual residual conditions. -/
theorem positive_excess_assignment (T : Task K F) (h : ActiveResidual T)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (hpos : finrank K F < finrank K (T.A 0)+finrank K (T.A 1)+finrank K (T.A 2)) :
    PositiveAssignment T :=
  active_residual_assignment T hi
    (by simpa only [Task.Spanning,three_iSup] using h.spanning) hpos
    (exists_nontrivial_demand T h hi.1) (exists_nonfull_signal T h hpos)

omit [Finite K] in
/-- There is no negative-excess residual component. -/
theorem nonnegative_excess (T : Task K F) (h : ActiveResidual T) :
    finrank K F ≤ finrank K (T.A 0)+finrank K (T.A 1)+finrank K (T.A 2) := by
  have h01 := Submodule.finrank_sup_add_finrank_inf_eq (T.A 0) (T.A 1)
  have h012 := Submodule.finrank_sup_add_finrank_inf_eq (T.A 0 ⊔ T.A 1) (T.A 2)
  rw [h.spanning,finrank_top] at h012
  omega

/-- Complete actual component exhaustion: the zero-excess case is separated
from the eight nonzero-defect families, both tripod boundaries, and R_n. -/
theorem residual_exhaustion (T : Task K F) (h : ActiveResidual T)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤) :
    (finrank K (T.A 0)+finrank K (T.A 1)+finrank K (T.A 2) = finrank K F) ∨
      PositiveAssignment T := by
  have hn := nonnegative_excess T h
  by_cases hz : finrank K (T.A 0)+finrank K (T.A 1)+finrank K (T.A 2) = finrank K F
  · exact Or.inl hz
  · exact Or.inr (positive_excess_assignment T h hi (by omega))

end UploadBroadcast.ResidualComponentClassification
