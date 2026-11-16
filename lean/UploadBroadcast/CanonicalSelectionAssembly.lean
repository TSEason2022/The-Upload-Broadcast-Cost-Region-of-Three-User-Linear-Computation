import UploadBroadcast.ResidualBackgroundSelection
import UploadBroadcast.OmniscienceResidualAdditivity
import UploadBroadcast.OmniscienceRelayConstruction
import UploadBroadcast.OmniscienceRelayProfile

/-! Assemble an actual Ω relay with a selected active-residual relay, then
restore the product order and all original-task reductions. -/
namespace UploadBroadcast.CanonicalSelectionAssembly
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Module ResidualComponentAdditivity
variable {K V W : Type*} [Field K] [Finite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

omit [Finite K] [FiniteDimensional K V] [FiniteDimensional K W] in
theorem map_directSum_swap (T : Task K V) (S : Task K W) :
    Profile.mapTask (LinearEquiv.prodComm K V W) (Profile.directSum T S)=Profile.directSum S T := by
  apply FiniteProductCoordinates.task_eq_of_spaces
  · funext i
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨hy.2,hy.1⟩
    · intro hx
      exact ⟨(x.2,x.1),⟨hx.2,hx.1⟩,rfl⟩
  · funext i
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨hy.2,hy.1⟩
    · intro hx
      exact ⟨(x.2,x.1),⟨hx.2,hx.1⟩,rfl⟩

noncomputable def swapRetraction (T : Task K V) (S : Task K W) :
    PassiveRetraction (Profile.directSum T S) (Profile.directSum S T) := by
  have r := (Profile.directSum T S).coordinateRetraction (LinearEquiv.prodComm K V W)
  rw [map_directSum_swap] at r
  exact r

theorem residual_upload_integral (S : Task K V) (hS : ActiveResidual S) :
    ∃ z : ℤ, S.uploadOptimum=(z:ℝ) := by
  refine ⟨2*(finrank K V : ℤ)-((finrank K (S.A 0) : ℤ)+finrank K (S.A 1)+finrank K (S.A 2)),?_⟩
  rw [minimum_upload S hS]
  simp only [uploadValue,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]

variable {C X₁ X₂ X₃ : Type*}
  [AddCommGroup C] [Module K C] [FiniteDimensional K C]
  [AddCommGroup X₁] [Module K X₁] [FiniteDimensional K X₁]
  [AddCommGroup X₂] [Module K X₂] [FiniteDimensional K X₂]
  [AddCommGroup X₃] [Module K X₃] [FiniteDimensional K X₃]
local notation "O" => OmniscienceOperational.task (K:=K) (V:=C) (X₁:=X₁) (X₂:=X₂) (X₃:=X₃)
local notation "uO" => Omniscience.optimum (K:=K) (V:=C) (X₁:=X₁) (X₂:=X₂) (X₃:=X₃)

/-- Integrality of the total operational minimum forces a scalar integral
Ω optimum, because the residual optimum is an actual integer rank. -/
theorem omniscience_scalar_parameter (S : Task K V) (hS : ActiveResidual S)
    (h : ∃ z : ℤ, (Profile.directSum O S).uploadOptimum=(z:ℝ)) :
    ∃ n : ℕ, (n:ℝ)=uO := by
  obtain ⟨z,hz⟩ := h
  obtain ⟨d,hd⟩ := residual_upload_integral S hS
  rw [OmniscienceResidualAdditivity.uploadOptimum_add S hS,hd] at hz
  have he : ((z-d:ℤ):ℝ)=uO := by push_cast; linarith
  have hu : 0≤uO := by
    rw [OmniscienceOperational.optimum_eq_deficits]
    unfold Allocation.omniscienceValue
    positivity
  have hnonneg : (0:ℤ)≤z-d := by exact_mod_cast (show (0:ℝ)≤((z-d:ℤ):ℝ) from he.symm ▸ hu)
  refine ⟨(z-d).toNat,?_⟩
  have hh : ((z-d).toNat:ℝ)=((z-d:ℤ):ℝ) := by exact_mod_cast Int.toNat_of_nonneg hnonneg
  exact hh.trans he

end UploadBroadcast.CanonicalSelectionAssembly

namespace UploadBroadcast.CanonicalSelectionAssembly
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Module ResidualComponentAdditivity
variable {K V C X₁ X₂ X₃ : Type} [Field K] [Finite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup C] [Module K C] [FiniteDimensional K C]
  [AddCommGroup X₁] [Module K X₁] [FiniteDimensional K X₁]
  [AddCommGroup X₂] [Module K X₂] [FiniteDimensional K X₂]
  [AddCommGroup X₃] [Module K X₃] [FiniteDimensional K X₃]
local notation "O" => OmniscienceOperational.task (K:=K) (V:=C) (X₁:=X₁) (X₂:=X₂) (X₃:=X₃)
local notation "uO" => Omniscience.optimum (K:=K) (V:=C) (X₁:=X₁) (X₂:=X₂) (X₃:=X₃)

/-- Actual residual selection, actual Ω scalar uploads, product separation,
and an actual order-swap chart supply the full scalar relay witness. -/
theorem scalarSelection_of_background (hbg : ResidualBackgroundSelection K)
    (S : Task K V) (hS : ActiveResidual S) :
    (Profile.directSum O S).ScalarRelaySelection := by
  intro D hD hU
  obtain ⟨n,hn⟩ := omniscience_scalar_parameter S hS hU
  let swap := swapRetraction O S
  have hD' : Profile.rankBound (Profile.directSum S O) ≤ (D:ℝ) := by
    rw [←swap.rankBound_eq,←task_general_broadcastOptimum_eq_rankBound]
    exact hD
  obtain ⟨P,hPl,hPf,hPm,hbudget⟩ := hbg V _ S hS O (fun _ => rfl) D hD'
  obtain ⟨Q,hQl,hQf,hQd,_,_⟩ := OmniscienceRelayConstruction.exists_scalar
    (K:=K) (V:=C) (X₁:=X₁) (X₂:=X₂) (X₃:=X₃) n hn
  have hQvalue : (n:ℝ)=Allocation.omniscienceValue
      (condRank ⊤ ((O).A 0)) (condRank ⊤ ((O).A 1)) (condRank ⊤ ((O).A 2)) :=
    hn.trans (OmniscienceOperational.optimum_eq_deficits (K:=K) (V:=C)
      (X₁:=X₁) (X₂:=X₂) (X₃:=X₃))
  obtain ⟨R,hRl,hRf,hRd,hRb,hsep⟩ := OmniscienceRelayProfile.assemble_binary S O
    (fun _ => rfl) P Q hPl hPf hQl hQf hS.disjoint₀₁ hS.disjoint₀₂ hS.disjoint₁₂
    (finrank K P) n rfl hQd hPm hQvalue (D:ℝ) hbudget
  let w : (Profile.directSum S O).ScalarRelayWitness D :=
    { space := R
      locallyGenerated := hRl
      feasible := hRf
      upload_optimal := by
        rw [hRd,Nat.cast_add,hPm,hn,←swap.uploadOptimum_eq,
          OmniscienceResidualAdditivity.uploadOptimum_add S hS]
        ring
      profile_bound := hRb
      binary_separation := fun _ => hsep }
  exact ⟨swap.restoreRelayWitness w⟩

end UploadBroadcast.CanonicalSelectionAssembly

namespace UploadBroadcast
variable {K : Type} [Field K] [Finite K]

/-- No additional geometric or optimality premise is introduced by the
Ω/background assembly; the remaining input is precisely the residual theorem. -/
theorem canonicalScalarSelection_of_residualBackground (h : ResidualBackgroundSelection K) :
    CanonicalScalarSelection K := by
  intro C X₁ X₂ X₃ V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S hS
  exact CanonicalSelectionAssembly.scalarSelection_of_background h S hS

end UploadBroadcast
