import UploadBroadcast.OriginalJointReduction
import UploadBroadcast.CanonicalResidualScalar
import UploadBroadcast.GlobalUploadOptimal

/-! Operational Ω-plus-active-residual upload additivity. The converse applies
to joint nonlinear encoders, not merely independent component coding. -/
namespace UploadBroadcast.OmniscienceResidualAdditivity
open Module ResidualUpload ResidualTaskAssembly
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K P₁ P₂ P₃ D : Type*} [Field K] [Finite K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]
  [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K D]

/-- The fully constructed canonical reduction has its exact scalar upload
optimum, against all nonlinear codes and all blocklengths. -/
theorem canonicalReduction_uploadOptimum
    (T : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : T.A 0=A₁ K P₁ P₂ P₃ D) (h₁ : T.A 1=A₂ K P₁ P₂ P₃ D)
    (h₂ : T.A 2=A₃ K P₁ P₂ P₃ D)
    (hz : pureRows₁ T ⊓ pureRows₂ T ⊓ pureRows₃ T=⊥) :
    (canonicalReduction T h₀ h₁ h₂).uploadOptimum =
      ((finrank K (used₁ T)+finrank K (used₂ T)+finrank K (used₃ T)+
        finrank K (selectedTrimData T h₀ h₁ h₂).activeRows : ℕ) : ℝ) := by
  let res := canonicalReduction T h₀ h₁ h₂
  let a := canonicalReductionBridge T h₀ h₁ h₂
  obtain ⟨ha,hb,hc⟩ := canonicalReduction_sides T h₀ h₁ h₂
  obtain ⟨hua,hub,huc⟩ := canonicalReduction_fully_used T h₀ h₁ h₂
  obtain ⟨r,c,_,hu,_⟩ := ResidualRowShape.canonicalReduction_scalar_upload_exact T h₀ h₁ h₂ hz
  apply Task.uploadOptimum_eq_of_code c.toCode (by decide) _ hu.le
  intro L m s code hL
  let fc : res.FiniteCode L (fun i => Fin (m i)) (Fin s) :=
    { toCode := code
      positive_blocklength := hL
      finite_upload := fun _ => inferInstance
      finite_broadcast := inferInstance }
  have splits : ∀ i : Three, ResidualConverse.PrivateSplit res i
      (![LinearMap.range a.v,LinearMap.range a.r,LinearMap.range (a.r-a.v)] i) :=
    ResidualPrivateSplit.fully_used_splits res ha hb hc hua hub huc
  have lo := ResidualConverse.explicit_residual_upload_lower_bound a res fc ha hb hc
    rfl rfl rfl splits
  simpa only [fc,Nat.cast_add] using lo

variable {C X₁ X₂ X₃ : Type*}
  [AddCommGroup C] [Module K C] [FiniteDimensional K C]
  [AddCommGroup X₁] [Module K X₁] [FiniteDimensional K X₁]
  [AddCommGroup X₂] [Module K X₂] [FiniteDimensional K X₂]
  [AddCommGroup X₃] [Module K X₃] [FiniteDimensional K X₃]
local notation "O" => OmniscienceOperational.task (K:=K) (V:=C) (X₁:=X₁) (X₂:=X₂) (X₃:=X₃)
local notation "uO" => Omniscience.optimum (K:=K) (V:=C) (X₁:=X₁) (X₂:=X₂) (X₃:=X₃)

/-- Canonical coordinates suffice for arbitrary common-zero residual tasks;
private and empty-row reductions are made internally. -/
theorem canonical_additivity (T : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : T.A 0=A₁ K P₁ P₂ P₃ D) (h₁ : T.A 1=A₂ K P₁ P₂ P₃ D)
    (h₂ : T.A 2=A₃ K P₁ P₂ P₃ D)
    (hz : pureRows₁ T ⊓ pureRows₂ T ⊓ pureRows₃ T=⊥) :
    (Profile.directSum O T).uploadOptimum=uO+T.uploadOptimum := by
  let res := canonicalReduction T h₀ h₁ h₂
  let red := canonicalRetraction T h₀ h₁ h₂
  let a := canonicalReductionBridge T h₀ h₁ h₂
  obtain ⟨ha,hb,hc⟩ := canonicalReduction_sides T h₀ h₁ h₂
  obtain ⟨hua,hub,huc⟩ := canonicalReduction_fully_used T h₀ h₁ h₂
  have hzero := canonicalReduction_common_pure_eq_bot T h₀ h₁ h₂ hz
  have hj := GlobalUploadOptimal.canonical_uploadOptimum
    (W:=C) (X₁:=X₁) (X₂:=X₂) (X₃:=X₃) res a
    (by intro i; fin_cases i <;> rfl) rfl rfl ha hb hc hua hub huc hzero
  have hres := canonicalReduction_uploadOptimum T h₀ h₁ h₂ hz
  have hp := ((PassiveRetraction.refl O).prod red).uploadOptimum_eq
  rw [hp,red.uploadOptimum_eq]
  rw [hj,hres]
  simp only [Nat.cast_add]
  ring

variable {F : Type*} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Exact upload additivity for arbitrary actual active residuals, including
joint nonlinear encoding across Ω and every residual component. -/
theorem uploadOptimum_add (S : Task K F) (hS : ResidualComponentAdditivity.ActiveResidual S) :
    (Profile.directSum O S).uploadOptimum=uO+S.uploadOptimum := by
  obtain ⟨P₁,P₂,P₃,e,he₀,he₁,he₂⟩ := ResidualTaskAssembly.exists_canonical_chart
    (S.A 0) (S.A 1) (S.A 2) hS.disjoint₀₁ hS.disjoint₀₂ hS.disjoint₁₂ hS.spanning
  let c : S.PrivateTripodChart := ⟨P₁,P₂,P₃,e,he₀,he₁,he₂⟩
  have hc : ResidualComponentAdditivity.ActiveResidual c.toTask := hS.map e.symm
  have hz := ResidualComponentAdditivity.canonical_zero_common c.toTask c.sides.1 c.sides.2.1 c.sides.2.2 hc.common_zero
  have hh := canonical_additivity (C:=C) (X₁:=X₁) (X₂:=X₂) (X₃:=X₃)
    c.toTask c.sides.1 c.sides.2.1 c.sides.2.2 hz
  rw [(c.rightRetraction O).uploadOptimum_eq,c.toRetraction.uploadOptimum_eq]
  exact hh

/-- Dimension-form version of the same equality, useful for integral scalar
relay budgets after the genuine residual converse has been proved. -/
theorem uploadOptimum_add_value (S : Task K F) (hS : ResidualComponentAdditivity.ActiveResidual S) :
    (Profile.directSum O S).uploadOptimum=uO+ResidualComponentAdditivity.uploadValue S := by
  rw [uploadOptimum_add S hS,ResidualComponentAdditivity.minimum_upload S hS]

end UploadBroadcast.OmniscienceResidualAdditivity
