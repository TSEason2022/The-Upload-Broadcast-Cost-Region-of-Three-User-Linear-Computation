import UploadBroadcast.ConditionedResidualBridges
import UploadBroadcast.ResidualRelayAssembly
import UploadBroadcast.ResidualPureTransport

/-! Exact attained-alphabet scalar upload cost of the constructed active residual. -/
namespace UploadBroadcast.ResidualRowShape
open Module ResidualUpload ResidualTaskAssembly
variable {K P₁ P₂ P₃ D : Type*} [Field K] [Finite K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]
  [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K D]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

/-- The source's residual upload number is attained by a scalar linear code
on the actual canonical reduction, with equality for the actual upload
alphabets. Both the bridge and the private inverse hypotheses are constructed. -/
theorem canonicalReduction_scalar_upload_exact
    (task : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)
    (hz : pureRows₁ task ⊓ pureRows₂ task ⊓ pureRows₃ task = ⊥) :
    let res := canonicalReduction task h₀ h₁ h₂
    let d := finrank K (used₁ task) + finrank K (used₂ task) + finrank K (used₃ task) +
      finrank K (selectedTrimData task h₀ h₁ h₂).activeRows
    ∃ r : Three → ℕ, ∃ c : res.LinearCode 1 r d,
      (∑ i, r i) = d ∧ c.toCode.uploadCost = d ∧ c.toCode.broadcastCost ≤ d := by
  let res := canonicalReduction task h₀ h₁ h₂
  let a := canonicalReductionBridge task h₀ h₁ h₂
  obtain ⟨ha,hb,hc⟩ := canonicalReduction_sides task h₀ h₁ h₂
  obtain ⟨hua,hub,huc⟩ := canonicalReduction_fully_used task h₀ h₁ h₂
  have hzero := canonicalReduction_common_pure_eq_bot task h₀ h₁ h₂ hz
  obtain ⟨r,c,hr,hu,hd⟩ := ResidualRelayAssembly.exists_scalar_linear_upload res ha hb hc hzero
  let fc : res.FiniteCode 1 (fun i => Fin (r i) → K)
      (Fin (finrank K (used₁ task) + finrank K (used₂ task) + finrank K (used₃ task) +
        finrank K (selectedTrimData task h₀ h₁ h₂).activeRows) → K) :=
    { toCode := c.toCode
      positive_blocklength := by decide
      finite_upload := fun _ => inferInstance
      finite_broadcast := inferInstance }
  have splits : ∀ i : Three, ResidualConverse.PrivateSplit res i
      (![LinearMap.range a.v,LinearMap.range a.r,LinearMap.range (a.r-a.v)] i) :=
    ResidualPrivateSplit.fully_used_splits res ha hb hc hua hub huc
  have lo := ResidualConverse.explicit_residual_upload_lower_bound a res fc ha hb hc
    rfl rfl rfl splits
  refine ⟨r,c,hr,?_,?_⟩
  rotate_left
  · simpa only [Nat.cast_add] using hd
  apply le_antisymm
  · simpa only [Nat.cast_add] using hu
  · simpa only [fc,Nat.cast_add] using lo

end UploadBroadcast.ResidualRowShape
