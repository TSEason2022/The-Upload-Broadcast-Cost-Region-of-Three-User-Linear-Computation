import UploadBroadcast.OriginalUploadOptimum
import UploadBroadcast.CommonTripodRanks

namespace UploadBroadcast.ResidualTaskAssembly
open ResidualUpload Module
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K P₁ P₂ P₃ D : Type*} [Field K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]
  [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K D]
  (task : Task K (Ambient P₁ P₂ P₃ D))
  (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
  (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
  (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)

/-- The paper's sum of the remotely used private dimensions. -/
noncomputable def privateDimension : ℕ :=
  finrank K (used₁ task) + finrank K (used₂ task) + finrank K (used₃ task)

/-- The common pure-demand dimension, after the source's private trimming. -/
noncomputable def commonDimension : ℕ :=
  finrank K (CommonTripodAssembly.commonRows (privateTrim task))

/-- Noncommon active tripod rows, computed before the common split. -/
noncomputable def tripodDimension : ℕ :=
  finrank K (selectedTrimData task h₀ h₁ h₂).activeRows - commonDimension task

omit [FiniteDimensional K P₁] [FiniteDimensional K P₂] [FiniteDimensional K P₃] in
/-- The actual final residual row dimension is precisely the original
pre-split rank expression, for any constructed graph lifts. -/
theorem finalRows_finrank :
    finrank K (finalDemandData task h₀ h₁ h₂).activeRows = tripodDimension task h₀ h₁ h₂ :=
  CommonTripodRanks.residual_activeRows_finrank (privateTrim task)
    (privateTrim_sides task h₀ h₁ h₂).1 (privateTrim_sides task h₀ h₁ h₂).2.1
    (privateTrim_sides task h₀ h₁ h₂).2.2 (commonComplement (privateTrim task))
    (commonComplement_isCompl (privateTrim task)) (selectedTrimData task h₀ h₁ h₂)
    (finalDemandData task h₀ h₁ h₂)

omit [FiniteDimensional K P₁] [FiniteDimensional K P₂] [FiniteDimensional K P₃] in
/-- Source formula: noncommon pure rank plus the genuine relation rank after
zero-private cancellation, computed from the original trimmed demands. -/
theorem tripodDimension_eq_pure_mixed :
    let t := privateTrim task
    let g := selectedTrimData task h₀ h₁ h₂
    let S := pureRows₁ t ⊔ pureRows₂ t ⊔ pureRows₃ t
    tripodDimension task h₀ h₁ h₂ =
      (finrank K S - commonDimension task) +
      finrank K ((LinearMap.ker (DemandData.incidence (task := t))).map
        (S.mkQ.comp g.relationRows)) :=
  (selectedTrimData task h₀ h₁ h₂).noncommon_activeRows_finrank

/-- The same mixed row term is exactly the stacked-rank difference [B;G]-B. -/
theorem tripodDimension_eq_stacked_rank :
    let t := privateTrim task
    let g := selectedTrimData task h₀ h₁ h₂
    let S := pureRows₁ t ⊔ pureRows₂ t ⊔ pureRows₃ t
    tripodDimension task h₀ h₁ h₂ = (finrank K S - commonDimension task) +
      (finrank K (LinearMap.range ((DemandData.incidence (task := t)).prod
        (S.mkQ.comp g.relationRows))) -
      finrank K (LinearMap.range (DemandData.incidence (task := t)))) := by
  dsimp only
  rw [tripodDimension_eq_pure_mixed]
  rw [(selectedTrimData task h₀ h₁ h₂).mixedRows_stacked_rank]

end UploadBroadcast.ResidualTaskAssembly
