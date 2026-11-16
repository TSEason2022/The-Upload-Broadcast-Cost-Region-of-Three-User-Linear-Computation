import UploadBroadcast.GlobalUploadGeometry
import UploadBroadcast.ResidualPrivateSplit
import UploadBroadcast.OperationalBounds

/-! Global operational upload converse with all residual private and common
function certificates constructed from fully used canonical active data. -/
namespace UploadBroadcast.GlobalUploadAssembly
open ResidualUpload ResidualTaskAssembly GlobalUploadGeometry
variable {K E P₁ P₂ P₃ T L : Type*} [Field K] [Finite K]
  [AddCommGroup E] [Module K E] [AddCommGroup P₁] [Module K P₁]
  [AddCommGroup P₂] [Module K P₂] [AddCommGroup P₃] [Module K P₃]
  [AddCommGroup T] [Module K T] [AddCommGroup L] [Module K L]
  [FiniteDimensional K E] [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K T]
local notation "V" => Ambient P₁ P₂ P₃ T

noncomputable def canonicalValue (om : Task K E) : ℝ :=
  ((Module.finrank K P₁ : ℝ)+Module.finrank K P₂+Module.finrank K P₃+Module.finrank K T) +
    max (max ((Module.finrank K E : ℝ)-Module.finrank K (om.A 0))
      (max ((Module.finrank K E : ℝ)-Module.finrank K (om.A 1))
        ((Module.finrank K E : ℝ)-Module.finrank K (om.A 2))))
      ((((Module.finrank K E : ℝ)-Module.finrank K (om.A 0))+
        ((Module.finrank K E : ℝ)-Module.finrank K (om.A 1))+
        ((Module.finrank K E : ℝ)-Module.finrank K (om.A 2)))/2)

/-- No private-slice, signal-intersection, independence, entropy, or residual
lower-bound certificate is assumed here: each is constructed from the actual
fully used canonical coordinates and active demand data. -/
theorem fully_used_active_directSum_lower_bound {n : ℕ} {M : Three → Type*} {B : Type*}
    (om : Task K E) (res : Task K V) (hom : ∀ i, om.U i = ⊤)
    (a : SignalBridge.Data (K := K) (F := V) (T := T) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (L := L))
    (hU : ∀ i, res.U i = ![a.U₁,a.U₂,a.U₃] i)
    (hv : a.v = ResidualPrivateSplit.tripod₁) (hr : a.r = ResidualPrivateSplit.tripod₂)
    (h₀ : res.A 0 = A₁ K P₁ P₂ P₃ T) (h₁ : res.A 1 = A₂ K P₁ P₂ P₃ T)
    (h₂ : res.A 2 = A₃ K P₁ P₂ P₃ T)
    (hu₁ : used₁ res = ⊤) (hu₂ : used₂ res = ⊤) (hu₃ : used₃ res = ⊤)
    (code : (Profile.directSum om res).FiniteCode n M B) :
    canonicalValue (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := T) om ≤ code.toCode.uploadCost := by
  have d₀₁ : Disjoint (res.A 0) (res.A 1) := by rw [h₀,h₁]; exact sides_disjoint₁₂
  have d₀₂ : Disjoint (res.A 0) (res.A 2) := by rw [h₀,h₂]; exact sides_disjoint₁₃
  have d₁₂ : Disjoint (res.A 1) (res.A 2) := by rw [h₁,h₂]; exact sides_disjoint₂₃
  have pair : ∀ i j : Three, i ≠ j → Disjoint (res.A i) (res.A j) := by
    intro i j hij
    have d₁₀ := d₀₁.symm
    have d₂₀ := d₀₂.symm
    have d₂₁ := d₁₂.symm
    fin_cases i <;> fin_cases j <;> simp_all
  have priv : ∀ i, ResidualConverse.PrivateSplit res i (tripodSpaces a.v a.r i) := by
    rw [hv,hr]
    exact ResidualPrivateSplit.fully_used_splits res h₀ h₁ h₂ hu₁ hu₂ hu₃
  let r := of_active_data res a hU pair priv
  exact canonical_directSum_upload_lower_bound om res hom r h₀ h₁ h₂ code

/-- The global converse remains valid on the full regularized closed region. -/
theorem fully_used_active_costRegion_lower_bound
    (om : Task K E) (res : Task K V) (hom : ∀ i, om.U i = ⊤)
    (a : SignalBridge.Data (K := K) (F := V) (T := T) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (L := L))
    (hU : ∀ i, res.U i = ![a.U₁,a.U₂,a.U₃] i)
    (hv : a.v = ResidualPrivateSplit.tripod₁) (hr : a.r = ResidualPrivateSplit.tripod₂)
    (h₀ : res.A 0 = A₁ K P₁ P₂ P₃ T) (h₁ : res.A 1 = A₂ K P₁ P₂ P₃ T)
    (h₂ : res.A 2 = A₃ K P₁ P₂ P₃ T)
    (hu₁ : used₁ res = ⊤) (hu₂ : used₂ res = ⊤) (hu₃ : used₃ res = ⊤)
    {b : ℝ × ℝ} (hb : b ∈ (Profile.directSum om res).costRegion) :
    canonicalValue (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := T) om ≤ b.1 := by
  apply Task.upload_lower_on_region _ _ hb
  intro n m s code hn
  let fc : (Profile.directSum om res).FiniteCode n (fun i => Fin (m i)) (Fin s) :=
    { toCode := code
      positive_blocklength := hn
      finite_upload := fun _ => inferInstance
      finite_broadcast := inferInstance }
  exact fully_used_active_directSum_lower_bound om res hom a hU hv hr h₀ h₁ h₂ hu₁ hu₂ hu₃ fc

end UploadBroadcast.GlobalUploadAssembly
