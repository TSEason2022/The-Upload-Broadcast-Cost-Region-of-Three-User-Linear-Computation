import UploadBroadcast.OriginalUploadCanonical

namespace UploadBroadcast.Task.PrivateTripodChart
open Module
variable {K F X₁ X₂ X₃ : Type*} [Field K] [AddCommGroup F] [Module K F]
  {S : Task K F} (c : S.PrivateTripodChart)

/-- Source private rank, evaluated in an actual private/tripod chart. -/
noncomputable def privateDimension : ℕ := ResidualTaskAssembly.privateDimension c.toTask
/-- Source common pure-demand rank. -/
noncomputable def commonDimension : ℕ := ResidualTaskAssembly.commonDimension c.toTask
/-- Source noncommon pure plus zero-private mixed row rank. -/
noncomputable def tripodDimension : ℕ :=
  ResidualTaskAssembly.tripodDimension c.toTask c.sides.1 c.sides.2.1 c.sides.2.2

noncomputable def omegaValue (x₀ x₁ x₂ : ℕ) : ℝ :=
  Allocation.omniscienceValue ((c.commonDimension : ℝ)+x₀)
    ((c.commonDimension : ℝ)+x₁) ((c.commonDimension : ℝ)+x₂)
noncomputable def uploadFormula (x₀ x₁ x₂ : ℕ) : ℝ :=
  (c.privateDimension : ℝ) + c.tripodDimension + c.omegaValue x₀ x₁ x₂

variable [AddCommGroup X₁] [Module K X₁] [AddCommGroup X₂] [Module K X₂]
  [AddCommGroup X₃] [Module K X₃]

/-- Formula identification packaged before specializing nested original-task types. -/
theorem actualOmega_eq (x₀ x₁ x₂ : ℕ) (h₀ : finrank K X₁ = x₀)
    (h₁ : finrank K X₂ = x₁) (h₂ : finrank K X₃ = x₂) :
    Omniscience.optimum (K := K)
      (V := CommonTripodAssembly.commonRows (ResidualTaskAssembly.privateTrim c.toTask))
      (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) = c.omegaValue x₀ x₁ x₂ := by
  unfold Omniscience.optimum omegaValue commonDimension ResidualTaskAssembly.commonDimension
  rw [h₀,h₁,h₂]

theorem canonicalValue_eq_formula (x₀ x₁ x₂ : ℕ) (h₀ : finrank K X₁ = x₀)
    (h₁ : finrank K X₂ = x₁) (h₂ : finrank K X₃ = x₂) :
    ResidualTaskAssembly.canonicalUploadValue
      (C := CommonTripodAssembly.commonRows (ResidualTaskAssembly.privateTrim c.toTask))
      (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) c.toTask c.sides.1 c.sides.2.1 c.sides.2.2 =
      c.uploadFormula x₀ x₁ x₂ := by
  unfold ResidualTaskAssembly.canonicalUploadValue uploadFormula privateDimension tripodDimension
  rw [c.actualOmega_eq x₀ x₁ x₂ h₀ h₁ h₂]
end UploadBroadcast.Task.PrivateTripodChart
