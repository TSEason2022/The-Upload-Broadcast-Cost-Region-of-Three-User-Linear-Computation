import UploadBroadcast.SourceMainTheorem
import UploadBroadcast.MatrixTaskEndpoints

/-!
# Reuse the paper-facing theorems

Run from the repository root: `lake env lean examples/ReusableAPI.lean`.
These generic examples use the original finite field, including the binary field.
They introduce no geometric selection hypothesis and no custom axiom.
See `docs/REUSING_THE_PROOFS.md` for cost conventions and computability limits.
-/

namespace UploadBroadcast.ReusableAPI

section CoefficientSpace
variable {K F : Type} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] (T : Task K F)

/-- The exact length-two budget region already equals the closed region. -/
theorem closed_and_two_region :
    T.achievableAt 2 = Task.budgetRectangle T.minimumUploadFormula (Profile.rankBound T) ∧
    T.costRegion = Task.budgetRectangle T.minimumUploadFormula (Profile.rankBound T) :=
  T.main_region

/-- Open the existential to obtain an actual code, not just a numerical bound. -/
theorem joint_two_code :
    ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode 2 r b),
      c.toCode.uploadCost = T.minimumUploadFormula ∧
      c.toCode.broadcastCost = Profile.rankBound T := by
  obtain ⟨r, b, c, hu, hd⟩ := T.joint_two
  refine ⟨r, b, c, ?_, ?_⟩
  · simpa only [T.minimum_upload] using hu
  · simpa only [task_general_broadcastOptimum_eq_rankBound] using hd

/-- Exactly when both source optima are integral, one linear instance suffices. -/
theorem scalar_criterion :
    T.LinearJointAt 1 ↔
      (∃ z : ℤ, T.minimumUploadFormula = (z : ℝ)) ∧
      (∃ z : ℤ, Profile.rankBound T = (z : ℝ)) := by
  simpa only [T.minimum_upload, task_general_broadcastOptimum_eq_rankBound]
    using T.scalar_joint_iff_integral

/-- Integral upload optimum gives exact scalar ceiling attainment for broadcast. -/
theorem scalar_ceiling (hU : ∃ z : ℤ, T.uploadOptimum = (z : ℝ)) :
    ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode 1 r b),
      c.toCode.uploadCost = T.uploadOptimum ∧
      c.toCode.broadcastCost = ((⌈broadcastOptimum T.A T.U⌉ : ℤ) : ℝ) :=
  T.scalar_budget hU

/-- This proves least positive blocklength, not merely an upper bound. -/
theorem minimum_blocklength :
    IsLeast {L : ℕ | 0 < L ∧ T.LinearJointAt L} T.linearJointLengthFormula :=
  T.minimum_linear_blocklength

/-- Reuse the closed minimum-upload formula independently of region membership. -/
theorem upload_formula : T.uploadOptimum = T.minimumUploadFormula :=
  T.minimum_upload

end CoefficientSpace

section Matrices
variable {K : Type} [Field K] {d : ℕ}

/-- Supply ordinary side/demand matrices and the original feasibility condition.
The columns need not be independent and the side spaces need not span K^d. -/
def matrixData (sideWidth demandWidth : Three → ℕ)
    (side : ∀ i, Matrix (Fin d) (Fin (sideWidth i)) K)
    (demand : ∀ i, Matrix (Fin d) (Fin (demandWidth i)) K)
    (feasible : ∀ i,
      Submodule.span K (Set.range (side i).col) ⊔
        Submodule.span K (Set.range (demand i).col) ≤
          ⨆ j, Submodule.span K (Set.range (side j).col)) :
    MatrixFrontend.Data (K := K) d where
  sideWidth := sideWidth
  demandWidth := demandWidth
  side := side
  demand := demand
  feasible := feasible

variable (D : MatrixFrontend.Data (K := K) d)

/-- Code correctness means recovery of the literal matrix product Xᵀ V_i. -/
theorem matrix_zero_error {L : ℕ} {r : Three → ℕ} {b : ℕ}
    (c : D.LinearCode L r b) (X : Matrix (Fin d) (Fin L) K) (i : Three) :
    c.decode i
      (c.broadcast (fun j => c.encode j (X.transpose * D.side j)),
        X.transpose * D.side i) = X.transpose * D.demand i :=
  c.zero_error X i

variable [Finite K]

/-- Transport the full region theorem to the original matrix observations. -/
theorem matrix_region :
    D.achievableAt 2 =
      Task.budgetRectangle D.task.minimumUploadFormula (Profile.rankBound D.task) ∧
    D.costRegion =
      Task.budgetRectangle D.task.minimumUploadFormula (Profile.rankBound D.task) := by
  rw [D.achievableAt_eq, D.costRegion_eq]
  exact D.task.main_region

/-- Obtain a length-two matrix-linear encoder, relay, and decoder with exact costs. -/
theorem matrix_joint_two_code :
    ∃ (r : Three → ℕ) (b : ℕ) (c : D.LinearCode 2 r b),
      c.toCode.uploadCost = D.task.minimumUploadFormula ∧
      c.toCode.broadcastCost = Profile.rankBound D.task := by
  obtain ⟨r, b, c, hu, hd⟩ := joint_two_code D.task
  refine ⟨r, b, MatrixFrontend.Data.LinearCode.ofTask c, ?_, ?_⟩
  · simpa only [MatrixFrontend.Data.LinearCode.ofTask_uploadCost] using hu
  · simpa only [MatrixFrontend.Data.LinearCode.ofTask_broadcastCost] using hd

/-- The matrix-to-task code transport retains both actual alphabet costs. -/
theorem matrix_linear_costs {L : ℕ} {r : Three → ℕ} {b : ℕ}
    (c : D.LinearCode L r b) :
    c.toTask.toCode.uploadCost = c.toCode.uploadCost ∧
    c.toTask.toCode.broadcastCost = c.toCode.broadcastCost :=
  ⟨c.toTask_uploadCost, c.toTask_broadcastCost⟩

/-- Ambient normalization preserves every original blocklength budget region. -/
theorem matrix_ambient_region (L : ℕ) :
    D.achievableAt L = D.task.normalized.achievableAt L :=
  D.ambient_achievableAt_eq L

end Matrices
end UploadBroadcast.ReusableAPI

-- Transitive axiom reports cover every declaration introduced above.
#print axioms UploadBroadcast.ReusableAPI.closed_and_two_region
#print axioms UploadBroadcast.ReusableAPI.joint_two_code
#print axioms UploadBroadcast.ReusableAPI.scalar_criterion
#print axioms UploadBroadcast.ReusableAPI.scalar_ceiling
#print axioms UploadBroadcast.ReusableAPI.minimum_blocklength
#print axioms UploadBroadcast.ReusableAPI.upload_formula
#print axioms UploadBroadcast.ReusableAPI.matrixData
#print axioms UploadBroadcast.ReusableAPI.matrix_zero_error
#print axioms UploadBroadcast.ReusableAPI.matrix_region
#print axioms UploadBroadcast.ReusableAPI.matrix_joint_two_code
#print axioms UploadBroadcast.ReusableAPI.matrix_linear_costs
#print axioms UploadBroadcast.ReusableAPI.matrix_ambient_region
