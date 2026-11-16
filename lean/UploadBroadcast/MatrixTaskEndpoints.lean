import UploadBroadcast.MatrixTaskFrontend
import UploadBroadcast.FullResidualAssembly
import UploadBroadcast.PassiveLinearCode

/-! The original matrix model, redundant-column normalization, and restriction
of the coefficient ambient space to the total side-information span. -/
namespace UploadBroadcast.MatrixFrontend.Data
variable {K : Type*} [Field K] {d : ℕ} (D : Data (K := K) d)

/-- The matrix problem and its spanning coefficient-space normalization have
identical nonlinear zero-error budget regions at every original blocklength. -/
theorem ambient_achievableAt_eq [Finite K] (L : ℕ) :
    D.achievableAt L = D.task.normalized.achievableAt L :=
  (D.achievableAt_eq L).trans (D.task.normalized_achievableAt_eq L)

/-- The restricted ambient space really is spanned by the three side spaces. -/
theorem ambient_spanning : D.task.normalized.Spanning := D.task.normalized_spanning

/-- Scalar and vector linear codes are transported without changing L,r,s. -/
theorem ambient_linearCode_nonempty_iff (L : ℕ) (r : Three → ℕ) (s : ℕ) :
    Nonempty (D.LinearCode L r s) ↔ Nonempty (D.task.normalized.LinearCode L r s) := by
  constructor
  · rintro ⟨c⟩
    exact ⟨D.task.normalizationRetraction.deleteLinear c.toTask⟩
  · rintro ⟨c⟩
    exact ⟨LinearCode.ofTask (D.task.normalizationRetraction.restoreLinear c)⟩

/-- Ambient restriction incurs no additional linear communication cost. -/
theorem ambient_linear_forward [Finite K] {L : ℕ} {r : Three → ℕ} {s : ℕ}
    (c : D.LinearCode L r s) :
    ∃ c' : D.task.normalized.LinearCode L r s,
      c'.toCode.uploadCost ≤ c.toCode.uploadCost ∧
      c'.toCode.broadcastCost ≤ c.toCode.broadcastCost := by
  refine ⟨D.task.normalizationRetraction.deleteLinear c.toTask, ?_⟩
  simpa using D.task.normalizationRetraction.deleteLinear_costs c.toTask

/-- Restoring the original source dimensions incurs no extra linear cost. -/
theorem ambient_linear_reverse [Finite K] {L : ℕ} {r : Three → ℕ} {s : ℕ}
    (c : D.task.normalized.LinearCode L r s) :
    ∃ c' : D.LinearCode L r s,
      c'.toCode.uploadCost ≤ c.toCode.uploadCost ∧
      c'.toCode.broadcastCost ≤ c.toCode.broadcastCost := by
  refine ⟨LinearCode.ofTask (D.task.normalizationRetraction.restoreLinear c), ?_⟩
  simpa using D.task.normalizationRetraction.restoreLinear_costs c

end UploadBroadcast.MatrixFrontend.Data
