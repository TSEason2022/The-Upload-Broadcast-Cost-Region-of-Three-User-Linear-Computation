import UploadBroadcast.OriginalUploadRanks
import UploadBroadcast.GlobalUploadOptimal
import UploadBroadcast.UploadAttainment

namespace UploadBroadcast.ResidualTaskAssembly
open ResidualUpload Module
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K P₁ P₂ P₃ D C X₁ X₂ X₃ : Type*} [Field K] [Finite K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]
  [AddCommGroup C] [Module K C] [AddCommGroup X₁] [Module K X₁]
  [AddCommGroup X₂] [Module K X₂] [AddCommGroup X₃] [Module K X₃]
  [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K D]
  [FiniteDimensional K C] [FiniteDimensional K X₁]
  [FiniteDimensional K X₂] [FiniteDimensional K X₃]
  (task : Task K (Ambient P₁ P₂ P₃ D))
  (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
  (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
  (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)

local notation "O" => OmniscienceOperational.task (K := K) (V := C)
  (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)
local notation "uO" => Omniscience.optimum (K := K) (V := C)
  (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)

/-- Source-order residual rank plus the canonical omniscience value. -/
noncomputable def canonicalUploadValue : ℝ :=
  (privateDimension task : ℝ) + tripodDimension task h₀ h₁ h₂ + uO

/-- The full original-task rank formula for the entirely constructed residual
in canonical omniscience coordinates. -/
theorem finalCanonical_uploadOptimum :
    (Profile.directSum O (finalResidual task h₀ h₁ h₂)).uploadOptimum =
      canonicalUploadValue (C := C) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) task h₀ h₁ h₂ := by
  let g := finalDemandData task h₀ h₁ h₂
  obtain ⟨hs₀,hs₁,hs₂⟩ := g.activeRowReduction_sides rfl rfl rfl
  obtain ⟨hu₁,hu₂,hu₃⟩ := finalResidual_fully_used task h₀ h₁ h₂
  have h := GlobalUploadOptimal.canonical_uploadOptimum
    (W := C) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)
    (finalResidual task h₀ h₁ h₂) (g.signalBridge rfl rfl rfl)
    (by intro i; fin_cases i <;> rfl) rfl rfl hs₀ hs₁ hs₂ hu₁ hu₂ hu₃
    (finalResidual_zero_common task h₀ h₁ h₂)
  rw [h]
  change (finrank K (used₁ task) + finrank K (used₂ task) + finrank K (used₃ task) +
      finrank K (finalDemandData task h₀ h₁ h₂).activeRows : ℝ) + uO = _
  rw [finalRows_finrank]
  simp only [canonicalUploadValue,privateDimension,Nat.cast_add]

omit [Finite K] in
/-- The final residual relay has exactly the source residual dimension. -/
theorem finalResidual_exists_relay :
    ∃ Q : Submodule K (Ambient (used₁ task) (used₂ task) (used₃ task)
      (finalDemandData task h₀ h₁ h₂).activeRows),
      (finalResidual task h₀ h₁ h₂).LocallyGenerated Q ∧
      (finalResidual task h₀ h₁ h₂).RelayFeasible Q ∧
      finrank K Q = privateDimension task + tripodDimension task h₀ h₁ h₂ := by
  let g := finalDemandData task h₀ h₁ h₂
  obtain ⟨hs₀,hs₁,hs₂⟩ := g.activeRowReduction_sides rfl rfl rfl
  obtain ⟨Q,hl,hf,hq⟩ := ResidualRelayAssembly.exists_relay_of_zero_common
    (finalResidual task h₀ h₁ h₂) hs₀ hs₁ hs₂ (finalResidual_zero_common task h₀ h₁ h₂)
  refine ⟨Q,hl,hf,?_⟩
  rw [hq]
  change _ + finrank K (finalDemandData task h₀ h₁ h₂).activeRows = _
  rw [finalRows_finrank]
  rfl

/-- Two original-field instances suffice, with exactly twice the source
minimum in nominal upload symbols and with the actual cost bounded by it. -/
theorem finalCanonical_two_instance :
    ∃ (r : Three → ℕ) (b : ℕ)
      (c : (Profile.directSum O (finalResidual task h₀ h₁ h₂)).LinearCode 2 r b),
      ((∑ i,r i : ℕ) : ℝ) / 2 =
        canonicalUploadValue (C := C) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) task h₀ h₁ h₂ ∧
      c.toCode.uploadCost ≤
        canonicalUploadValue (C := C) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) task h₀ h₁ h₂ := by
  obtain ⟨Q,hl,hf,hq⟩ := finalResidual_exists_relay task h₀ h₁ h₂
  obtain ⟨r,b,c,hn,hc⟩ := UploadAttainment.two_instance
    (V := C) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) (finalResidual task h₀ h₁ h₂) Q hl hf
  have hv : uO + (finrank K Q : ℝ) =
      canonicalUploadValue (C := C) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) task h₀ h₁ h₂ := by
    rw [hq,Nat.cast_add]
    unfold canonicalUploadValue
    ring
  exact ⟨r,b,c,hn.trans hv,hc.trans_eq hv⟩

/-- If the omniscience part is integral, one original-field instance suffices. -/
theorem finalCanonical_scalar (n : ℕ) (hn : (n : ℝ) = uO) :
    ∃ (r : Three → ℕ) (b : ℕ)
      (c : (Profile.directSum O (finalResidual task h₀ h₁ h₂)).LinearCode 1 r b),
      ((∑ i,r i : ℕ) : ℝ) =
        canonicalUploadValue (C := C) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) task h₀ h₁ h₂ ∧
      c.toCode.uploadCost ≤
        canonicalUploadValue (C := C) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) task h₀ h₁ h₂ := by
  obtain ⟨Q,hl,hf,hq⟩ := finalResidual_exists_relay task h₀ h₁ h₂
  obtain ⟨r,b,c,hnom,hc⟩ := UploadAttainment.scalar
    (V := C) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) (finalResidual task h₀ h₁ h₂) Q hl hf n hn
  have hv : uO + (finrank K Q : ℝ) =
      canonicalUploadValue (C := C) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) task h₀ h₁ h₂ := by
    rw [hq,Nat.cast_add]
    unfold canonicalUploadValue
    ring
  exact ⟨r,b,c,hnom.trans hv,hc.trans_eq hv⟩
end UploadBroadcast.ResidualTaskAssembly
