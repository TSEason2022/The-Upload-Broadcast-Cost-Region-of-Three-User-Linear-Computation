import UploadBroadcast.OriginalUploadChart
import UploadBroadcast.PairOmniscienceAdapter

namespace UploadBroadcast.OriginalUpload
open ResidualUpload ResidualTaskAssembly Module
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F P₁ P₂ P₃ D : Type*} [Field K]
  [AddCommGroup F] [Module K F]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]
  {pair : Task K F} (s : pair.ActivePairSelection)
  (hactive : ∀ i, pair.pairKnown i ≤ pair.U i)
  (task : Task K (Ambient P₁ P₂ P₃ D))
  (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
  (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
  (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)

local notation "Crow" => CommonTripodAssembly.commonRows (privateTrim task)
local notation "O" => OmniscienceOperational.task (K := K) (V := Crow)
  (X₁ := pair.pairKnown 0) (X₂ := pair.pairKnown 1) (X₃ := pair.pairKnown 2)
local notation "uO" => Omniscience.optimum (K := K) (V := Crow)
  (X₁ := pair.pairKnown 0) (X₂ := pair.pairKnown 1) (X₃ := pair.pairKnown 2)

/-- The constructed pair and common factors are genuinely the canonical Ω
coefficient task, via an original-field ambient equivalence. -/
noncomputable def omegaRetraction :
    PassiveRetraction (splitOmniscience task s.pairOmniscienceTask) O := by
  have r := (splitOmniscience task s.pairOmniscienceTask).coordinateRetraction
    (PairOmniscienceAdapter.combinedEquiv s)
  change PassiveRetraction _ (Profile.mapTask (PairOmniscienceAdapter.combinedEquiv s)
    (Profile.directSum s.pairOmniscienceTask (CommonTripodAssembly.commonTask (privateTrim task)))) at r
  rw [PairOmniscienceAdapter.mapTask_combined s hactive
    (CommonTripodAssembly.commonTask (privateTrim task)) (fun _ => rfl) (fun _ => rfl)] at r
  exact r

/-- Actual maps through every reduction, including the Ω coordinate adapter.
No operational product-substitution or code separability is assumed. -/
noncomputable def reduction :
    PassiveRetraction (Profile.directSum s.pairOmniscienceTask task)
      (Profile.directSum O (finalResidual task h₀ h₁ h₂)) :=
  (splitActiveRetraction task h₀ h₁ h₂ s.pairOmniscienceTask).trans
    ((omegaRetraction s hactive task).prod (PassiveRetraction.refl (finalResidual task h₀ h₁ h₂)))

variable [Finite K] [FiniteDimensional K F]
  [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K D]

include hactive

/-- Exact minimum in the original pair-plus-canonical-residual task, using
the source-order pre-common private and tripod rank parameters. -/
theorem uploadOptimum :
    (Profile.directSum s.pairOmniscienceTask task).uploadOptimum =
      canonicalUploadValue (C := Crow) (X₁ := pair.pairKnown 0)
        (X₂ := pair.pairKnown 1) (X₃ := pair.pairKnown 2) task h₀ h₁ h₂ :=
  (reduction s hactive task h₀ h₁ h₂).uploadOptimum_eq.trans
    (finalCanonical_uploadOptimum task h₀ h₁ h₂)

/-- Actual two-instance linear uploads, restored through the full coupled task. -/
theorem two_instance :
    ∃ (r : Three → ℕ) (b : ℕ) (c : (Profile.directSum s.pairOmniscienceTask task).LinearCode 2 r b),
      ((∑ i,r i : ℕ) : ℝ) / 2 =
        canonicalUploadValue (C := Crow) (X₁ := pair.pairKnown 0)
          (X₂ := pair.pairKnown 1) (X₃ := pair.pairKnown 2) task h₀ h₁ h₂ ∧
      c.toCode.uploadCost ≤
        canonicalUploadValue (C := Crow) (X₁ := pair.pairKnown 0)
          (X₂ := pair.pairKnown 1) (X₃ := pair.pairKnown 2) task h₀ h₁ h₂ := by
  obtain ⟨r,b,c,hn,hc⟩ := finalCanonical_two_instance
    (C := Crow) (X₁ := pair.pairKnown 0) (X₂ := pair.pairKnown 1) (X₃ := pair.pairKnown 2)
    task h₀ h₁ h₂
  let R := reduction s hactive task h₀ h₁ h₂
  exact ⟨r,b,R.restoreLinear c,hn,(R.restoreLinear_costs c).1.trans hc⟩

/-- Integral omniscience cost permits scalar uploads over the original field. -/
theorem scalar (n : ℕ) (hn : (n : ℝ) = uO) :
    ∃ (r : Three → ℕ) (b : ℕ) (c : (Profile.directSum s.pairOmniscienceTask task).LinearCode 1 r b),
      ((∑ i,r i : ℕ) : ℝ) =
        canonicalUploadValue (C := Crow) (X₁ := pair.pairKnown 0)
          (X₂ := pair.pairKnown 1) (X₃ := pair.pairKnown 2) task h₀ h₁ h₂ ∧
      c.toCode.uploadCost ≤
        canonicalUploadValue (C := Crow) (X₁ := pair.pairKnown 0)
          (X₂ := pair.pairKnown 1) (X₃ := pair.pairKnown 2) task h₀ h₁ h₂ := by
  obtain ⟨r,b,c,hN,hc⟩ := finalCanonical_scalar
    (C := Crow) (X₁ := pair.pairKnown 0) (X₂ := pair.pairKnown 1) (X₃ := pair.pairKnown 2)
    task h₀ h₁ h₂ n hn
  let R := reduction s hactive task h₀ h₁ h₂
  exact ⟨r,b,R.restoreLinear c,hN,(R.restoreLinear_costs c).1.trans hc⟩
end UploadBroadcast.OriginalUpload

namespace UploadBroadcast.Task.PrivateTripodChart
open Module
variable {K F E W : Type*} [Field K] [Finite K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {S : Task K F} (c : S.PrivateTripodChart) {pair : Task K E}
  (s : pair.ActivePairSelection) (ha : ∀ i, pair.pairKnown i ≤ pair.U i)
  (T : Task K W) (r : PassiveRetraction T (Profile.directSum s.pairOmniscienceTask c.toTask))

include s ha r

/-- Generic source restoration, before instantiating nested original-task charts. -/
theorem uploadOptimum_from : T.uploadOptimum =
    c.uploadFormula (finrank K (pair.pairKnown 0)) (finrank K (pair.pairKnown 1))
      (finrank K (pair.pairKnown 2)) :=
  (r.uploadOptimum_eq.trans (OriginalUpload.uploadOptimum s ha c.toTask
    c.sides.1 c.sides.2.1 c.sides.2.2)).trans
      (c.canonicalValue_eq_formula _ _ _ rfl rfl rfl)

theorem two_instance_from :
    ∃ (a : Three → ℕ) (b : ℕ) (code : T.LinearCode 2 a b),
      ((∑ i,a i : ℕ) : ℝ)/2 =
        c.uploadFormula (finrank K (pair.pairKnown 0)) (finrank K (pair.pairKnown 1))
          (finrank K (pair.pairKnown 2)) ∧
      code.toCode.uploadCost =
        c.uploadFormula (finrank K (pair.pairKnown 0)) (finrank K (pair.pairKnown 1))
          (finrank K (pair.pairKnown 2)) := by
  obtain ⟨a,b,code,hn,hc⟩ := OriginalUpload.two_instance s ha c.toTask c.sides.1 c.sides.2.1 c.sides.2.2
  have he := c.canonicalValue_eq_formula (finrank K (pair.pairKnown 0))
    (finrank K (pair.pairKnown 1)) (finrank K (pair.pairKnown 2)) rfl rfl rfl
  let code' := r.restoreLinear code
  refine ⟨a,b,code',hn.trans he,le_antisymm ?_ ?_⟩
  · exact ((r.restoreLinear_costs code).1.trans hc).trans_eq he
  · rw [← c.uploadOptimum_from s ha T r]
    exact code'.uploadOptimum_le (by decide)

theorem scalar_from (n : ℕ)
    (hn : (n : ℝ) = c.omegaValue (finrank K (pair.pairKnown 0))
      (finrank K (pair.pairKnown 1)) (finrank K (pair.pairKnown 2))) :
    ∃ (a : Three → ℕ) (b : ℕ) (code : T.LinearCode 1 a b),
      ((∑ i,a i : ℕ) : ℝ) =
        c.uploadFormula (finrank K (pair.pairKnown 0)) (finrank K (pair.pairKnown 1))
          (finrank K (pair.pairKnown 2)) ∧
      code.toCode.uploadCost =
        c.uploadFormula (finrank K (pair.pairKnown 0)) (finrank K (pair.pairKnown 1))
          (finrank K (pair.pairKnown 2)) := by
  obtain ⟨a,b,code,hN,hc⟩ := OriginalUpload.scalar s ha c.toTask c.sides.1 c.sides.2.1 c.sides.2.2 n
    (hn.trans (c.actualOmega_eq _ _ _ rfl rfl rfl).symm)
  have he := c.canonicalValue_eq_formula (finrank K (pair.pairKnown 0))
    (finrank K (pair.pairKnown 1)) (finrank K (pair.pairKnown 2)) rfl rfl rfl
  let code' := r.restoreLinear code
  refine ⟨a,b,code',hN.trans he,le_antisymm ?_ ?_⟩
  · exact ((r.restoreLinear_costs code).1.trans hc).trans_eq he
  · rw [← c.uploadOptimum_from s ha T r]
    exact code'.uploadOptimum_le (by decide)
end UploadBroadcast.Task.PrivateTripodChart
