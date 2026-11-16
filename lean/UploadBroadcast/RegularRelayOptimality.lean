import UploadBroadcast.ResonantFiniteAssembly
import UploadBroadcast.ResonantKernelSupport
import UploadBroadcast.ResidualComponentAdditivity
import UploadBroadcast.PhysicalCycleRelay

namespace UploadBroadcast.RegularRelayOptimality
open Module ResidualComponentAdditivity GlobalMenuAssembly
variable {K : Type*} [Field K]

/-- The original Jordan task's scalar relay rank is its actual active-residual
upload rank expression, calculated from the original coefficient subspaces. -/
theorem jordan_uploadValue (n : ℕ) :
    uploadValue (ResonantRelay.jordanTask K n) = (3*(n+1)+1 : ℕ) := by
  let X := JordanResonance.V K n
  have h₀ : finrank K ((ResonantRelay.jordanTask K n).A 0)=n+2 := by
    change finrank K (ResonantKernelSupport.side₁ (K := K) X X X)=n+2
    rw [ResonantKernelSupport.side₁_finrank]
    simp [X,JordanResonance.V,Module.finrank_pi]
  have h₁ : finrank K ((ResonantRelay.jordanTask K n).A 1)=n+2 := by
    change finrank K (ResonantKernelSupport.side₂ (K := K) X X X)=n+2
    rw [ResonantKernelSupport.side₂_finrank]
    simp [X,JordanResonance.V,Module.finrank_pi]
  have h₂ : finrank K ((ResonantRelay.jordanTask K n).A 2)=n+2 := by
    change finrank K (ResonantKernelSupport.side₃ (K := K) X X X)=n+2
    rw [ResonantKernelSupport.side₃_finrank]
    simp [X,JordanResonance.V,Module.finrank_pi]
  unfold uploadValue
  rw [h₀,h₁,h₂]
  simp only [ResonantEndomorphisms.Ambient,Module.finrank_prod,JordanResonance.V,
    Module.finrank_pi,Fintype.card_fin,Module.finrank_self,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  ring

variable {V : Type*} [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A genuine original-space regular classification chart supplies the exact
operational upload rank and the complete actual local relay menu. -/
theorem from_actual_chart (T : Task K V) (ha : ActiveResidual T) (n : ℕ)
    (e : V ≃ₗ[K] ResonantEndomorphisms.Ambient K (JordanResonance.V K n))
    (he : Profile.mapTask e T=ResonantRelay.jordanTask K n) :
    (3*(n+1)+1 : ℕ)=T.uploadOptimum ∧
    RealizesMenu T (3*(n+1)+1) ResonantFiniteAssembly.increment := by
  have hu : uploadValue T=uploadValue (ResonantRelay.jordanTask K n) := by
    rw [← he,uploadValue_map]
  refine ⟨?_,?_⟩
  · rw [minimum_upload T ha,hu,jordan_uploadValue]
  · exact PhysicalCycleRelay.menu_of_equiv T _ e he _ _ (ResonantFiniteAssembly.jordan_realizes n)

omit [Finite K] in
/-- The fully informed actual component profiles are likewise derived from
the coordinate classification, rather than accepted as family attributes. -/
theorem full_profiles (T : Task K V) (n : ℕ)
    (e : V ≃ₗ[K] ResonantEndomorphisms.Ambient K (JordanResonance.V K n))
    (he : Profile.mapTask e T=ResonantRelay.jordanTask K n) :
    (∀ r : Fin 6, Profile.entry T (.inl r)=(n : ℝ)+1) ∧
    (∀ i l : Three, 2*Profile.entry T (.inr (i,l))=3*((n : ℝ)+1)) := by
  constructor
  · intro r
    have hh := ResonantRelay.jordan_full_firstProfile K n r
    rw [← he,Profile.entry_mapTask] at hh
    exact hh
  · intro i l
    have hh := ResonantRelay.jordan_full_secondProfile K n i l
    rw [← he,Profile.entry_mapTask] at hh
    exact hh

end UploadBroadcast.RegularRelayOptimality
