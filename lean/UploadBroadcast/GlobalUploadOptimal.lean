import UploadBroadcast.GlobalUploadAssembly
import UploadBroadcast.ResidualRelayAssembly
import UploadBroadcast.LinearCodeSum
import UploadBroadcast.OmniscienceTaskCode

namespace UploadBroadcast.GlobalUploadOptimal
open ResidualUpload ResidualTaskAssembly GlobalUploadAssembly
variable {K E P₁ P₂ P₃ T : Type*} [Field K] [Finite K]
  [AddCommGroup E] [Module K E] [AddCommGroup P₁] [Module K P₁]
  [AddCommGroup P₂] [Module K P₂] [AddCommGroup P₃] [Module K P₃]
  [AddCommGroup T] [Module K T]
  [FiniteDimensional K E] [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K T]
local notation "Rspace" => Ambient P₁ P₂ P₃ T

/-- Combine an actual two-instance omniscience code with the constructed
scalar residual relay. The result is linear over the original field. -/
theorem exists_two_instance_upper (om : Task K E) (res : Task K Rspace)
    {a : Three → ℕ} {s : ℕ} (co : om.LinearCode 2 a s) (u : ℝ)
    (ho : ((∑ i,a i : ℕ) : ℝ)/2 ≤ u)
    (h₀ : res.A 0 = A₁ K P₁ P₂ P₃ T) (h₁ : res.A 1 = A₂ K P₁ P₂ P₃ T)
    (h₂ : res.A 2 = A₃ K P₁ P₂ P₃ T)
    (hz : pureRows₁ res ⊓ pureRows₂ res ⊓ pureRows₃ res = ⊥) :
    ∃ (r : Three → ℕ) (n : ℕ) (c : (Profile.directSum om res).LinearCode 2 r n),
      c.toCode.uploadCost ≤
        (Module.finrank K P₁+Module.finrank K P₂+Module.finrank K P₃+Module.finrank K T : ℝ)+u := by
  obtain ⟨b,cr,hb,_,_⟩ := ResidualRelayAssembly.exists_scalar_linear_upload res h₀ h₁ h₂ hz
  let c := co.directSum cr.repeatScalar
  refine ⟨_,_,c,?_⟩
  have hc := (co.directSum_cost_bounds cr.repeatScalar).1
  have hb' : (∑ i,(b i : ℝ)) =
      (Module.finrank K P₁+Module.finrank K P₂+Module.finrank K P₃+Module.finrank K T : ℝ) := by
    exact_mod_cast hb
  have ha : (∑ i,(a i : ℝ))/2 ≤ u := by simpa only [Nat.cast_sum] using ho
  simp only [Nat.cast_add,Finset.sum_add_distrib] at hc
  change c.toCode.uploadCost ≤ _ at hc
  rw [hb'] at hc
  linarith

/-- The matching code and the nonlinear converse identify the operational
infimum, including arbitrary blocklengths and closure. -/
theorem uploadOptimum_eq_of_omniscience_code {L : Type*} [AddCommGroup L] [Module K L]
    (om : Task K E) (res : Task K Rspace) (hom : ∀ i, om.U i = ⊤)
    {r : Three → ℕ} {s : ℕ} (co : om.LinearCode 2 r s)
    (ho : ((∑ i,r i : ℕ) : ℝ)/2 ≤
      canonicalValue (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := T) om -
      (Module.finrank K P₁+Module.finrank K P₂+Module.finrank K P₃+Module.finrank K T : ℝ))
    (a : SignalBridge.Data (K := K) (F := Rspace) (T := T) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (L := L))
    (hU : ∀ i, res.U i = ![a.U₁,a.U₂,a.U₃] i)
    (hv : a.v = ResidualPrivateSplit.tripod₁) (hr : a.r = ResidualPrivateSplit.tripod₂)
    (h₀ : res.A 0 = A₁ K P₁ P₂ P₃ T) (h₁ : res.A 1 = A₂ K P₁ P₂ P₃ T)
    (h₂ : res.A 2 = A₃ K P₁ P₂ P₃ T)
    (hu₁ : used₁ res = ⊤) (hu₂ : used₂ res = ⊤) (hu₃ : used₃ res = ⊤)
    (hz : pureRows₁ res ⊓ pureRows₂ res ⊓ pureRows₃ res = ⊥) :
    (Profile.directSum om res).uploadOptimum =
      canonicalValue (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := T) om := by
  obtain ⟨b,n,c,hc⟩ := exists_two_instance_upper om res co _ ho h₀ h₁ h₂ hz
  apply Task.uploadOptimum_eq_of_code c.toCode (by decide) _ (by linarith [hc])
  intro n m s code hn
  let fc : (Profile.directSum om res).FiniteCode n (fun i => Fin (m i)) (Fin s) :=
    { toCode := code
      positive_blocklength := hn
      finite_upload := fun _ => inferInstance
      finite_broadcast := inferInstance }
  exact fully_used_active_directSum_lower_bound om res hom a hU hv hr h₀ h₁ h₂ hu₁ hu₂ hu₃ fc

section CanonicalOmniscience
variable {W X₁ X₂ X₃ : Type*}
  [AddCommGroup W] [Module K W] [AddCommGroup X₁] [Module K X₁]
  [AddCommGroup X₂] [Module K X₂] [AddCommGroup X₃] [Module K X₃]
  [FiniteDimensional K W] [FiniteDimensional K X₁]
  [FiniteDimensional K X₂] [FiniteDimensional K X₃]

omit [Finite K] [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K T] in
/-- The operational expression agrees with the paper's canonical
omniscience value plus residual dimension. -/
theorem canonicalValue_eq :
    canonicalValue (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := T)
      (OmniscienceOperational.task (K := K) (V := W) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)) =
    (Module.finrank K P₁+Module.finrank K P₂+Module.finrank K P₃+Module.finrank K T : ℝ) +
      Omniscience.optimum (K := K) (V := W) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) := by
  have hd (A : Submodule K (OmniscienceOperational.Space W X₁ X₂ X₃)) :
      (condRank ⊤ A : ℝ) = Module.finrank K (OmniscienceOperational.Space W X₁ X₂ X₃) - Module.finrank K A := by
    unfold condRank
    rw [sup_top_eq,finrank_top,Nat.cast_sub A.finrank_le]
  rw [OmniscienceOperational.optimum_eq_deficits]
  simp only [canonicalValue,OmniscienceOperational.task,Allocation.omniscienceValue,hd,max_assoc]
/-- Exact minimum upload for the canonical omniscience-plus-active-residual
model. Both the omniscience code and the residual relay are constructed. -/
theorem canonical_uploadOptimum {L : Type*} [AddCommGroup L] [Module K L]
    (res : Task K Rspace)
    (a : SignalBridge.Data (K := K) (F := Rspace) (T := T) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (L := L))
    (hU : ∀ i, res.U i = ![a.U₁,a.U₂,a.U₃] i)
    (hv : a.v = ResidualPrivateSplit.tripod₁) (hr : a.r = ResidualPrivateSplit.tripod₂)
    (h₀ : res.A 0 = A₁ K P₁ P₂ P₃ T) (h₁ : res.A 1 = A₂ K P₁ P₂ P₃ T)
    (h₂ : res.A 2 = A₃ K P₁ P₂ P₃ T)
    (hu₁ : used₁ res = ⊤) (hu₂ : used₂ res = ⊤) (hu₃ : used₃ res = ⊤)
    (hz : pureRows₁ res ⊓ pureRows₂ res ⊓ pureRows₃ res = ⊥) :
    (Profile.directSum (OmniscienceOperational.task (K := K) (V := W)
      (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)) res).uploadOptimum =
    (Module.finrank K P₁+Module.finrank K P₂+Module.finrank K P₃+Module.finrank K T : ℝ) +
      Omniscience.optimum (K := K) (V := W) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) := by
  let om := OmniscienceOperational.task (K := K) (V := W)
    (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)
  obtain ⟨r,co,hn,_,_⟩ := OmniscienceOperational.exists_two_instance_optimal
    (K := K) (V := W) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)
  have he := canonicalValue_eq (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := T)
    (W := W) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)
  rw [← he]
  apply uploadOptimum_eq_of_omniscience_code om res (fun _ => rfl) co _ a hU hv hr
    h₀ h₁ h₂ hu₁ hu₂ hu₃ hz
  change ((∑ i,r i : ℕ) : ℝ)/2 ≤ _
  rw [show canonicalValue (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := T) om = _ from he]
  linarith

end CanonicalOmniscience

end UploadBroadcast.GlobalUploadOptimal
