import UploadBroadcast.BinaryAchievability
import UploadBroadcast.SemilinearTaskTransport
import UploadBroadcast.AllocationProfile

namespace UploadBroadcast
namespace BinaryFieldTransport
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- The canonical genuine ring equivalence for any field with two elements. -/
noncomputable def fieldEquiv [Fintype K] (hK : Fintype.card K = 2) : ZMod 2 ≃+* K :=
  ZMod.ringEquivOfPrime K Nat.prime_two hK

section Pullback
variable {R : Type*} [Field R] (σ : R ≃+* K)
local instance : RingHomInvPair σ.toRingHom σ.symm.toRingHom := RingHomInvPair.of_ringEquiv σ
local instance : RingHomInvPair σ.symm.toRingHom σ.toRingHom := RingHomInvPair.symm _ _

/-- Restrict the field action along an isomorphism without changing vectors. -/
def ambient : letI := Module.compHom F σ.toRingHom; F ≃ₛₗ[σ.toRingHom] F :=
  letI := Module.compHom F σ.toRingHom
  { toFun := id
    invFun := id
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

/-- Pullback of a signal or side-information space along the field change. -/
def subspace (P : Submodule K F) : letI := Module.compHom F σ.toRingHom; Submodule R F :=
  letI := Module.compHom F σ.toRingHom
  { carrier := P
    zero_mem' := P.zero_mem
    add_mem' := P.add_mem
    smul_mem' c _ hx := P.smul_mem (σ c) hx }

@[simp] theorem map_subspace (P : Submodule K F) :
    letI := Module.compHom F σ.toRingHom
    (subspace σ P).map (ambient (F := F) σ).toLinearMap = P := by
  letI := Module.compHom F σ.toRingHom
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩; exact hy
  · intro hx; exact ⟨x,hx,rfl⟩

end Pullback
end BinaryFieldTransport
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
/-- Every cardinality-two field inherits the verified binary construction via
an explicit field isomorphism, with actual encoders and decoders over that field. -/
theorem card_two_scalar_lcbc_achievability
    [Fintype K] [FiniteDimensional K F] (hK : Fintype.card K = 2)
    (A U : Fin 3 → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥) :
    ∃ n : ℕ, (n : ℤ) = ⌈Allocation.actualNumericLP A U⌉ ∧
      Nonempty (ScalarBroadcastCode A U n) := by
  let σ := BinaryFieldTransport.fieldEquiv hK
  letI : RingHomInvPair σ.toRingHom σ.symm.toRingHom := RingHomInvPair.of_ringEquiv σ
  letI : RingHomInvPair σ.symm.toRingHom σ.toRingHom := RingHomInvPair.symm _ _
  letI : Module (ZMod 2) F := Module.compHom F σ.toRingHom
  let e := BinaryFieldTransport.ambient (F := F) σ
  letI : FiniteDimensional (ZMod 2) F := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  let A₂ := fun i => BinaryFieldTransport.subspace σ (A i)
  let U₂ := fun i => BinaryFieldTransport.subspace σ (U i)
  have hA (i) : (A₂ i).map e.toLinearMap = A i := BinaryFieldTransport.map_subspace σ (A i)
  have hU (i) : (U₂ i).map e.toLinearMap = U i := BinaryFieldTransport.map_subspace σ (U i)
  have hAU₂ : ∀ i, A₂ i ≤ U₂ i := fun i => hAU i
  have hspan₂ : (⨆ i, A₂ i) = ⊤ := by
    apply Submodule.map_injective_of_injective (f := e.toLinearMap) e.injective
    rw [Submodule.map_iSup, Submodule.map_top, LinearMap.range_eq_top.mpr (show Function.Surjective e.toLinearMap from e.surjective)]
    simpa only [hA] using hspan
  have hsep₂ : A₂ 0 ⊓ (A₂ 1 ⊔ A₂ 2) = ⊥ := by
    apply Submodule.map_injective_of_injective (f := e.toLinearMap) e.injective
    rw [Submodule.map_inf e.toLinearMap e.injective, Submodule.map_sup, Submodule.map_bot]
    simpa only [hA] using hsep
  have hLP : Allocation.actualNumericLP A₂ U₂ = Allocation.actualNumericLP A U := by
    have hh := SemilinearTransport.actualNumericLP_map σ e A₂ U₂
    simpa only [hA, hU] using hh.symm
  obtain ⟨n,hn,⟨c⟩⟩ := binary_scalar_lcbc_achievability A₂ U₂ hAU₂ hspan₂ hsep₂
  refine ⟨n, hn.trans (congrArg Int.ceil hLP), ?_⟩
  have cc := SemilinearTransport.code σ e c
  simpa only [hA, hU] using Nonempty.intro cc

/-- The transported encoder has the same verified scalar length and the
attained-alphabet cost bound over the user's original field. -/
theorem card_two_scalar_lcbc_achievability_cost
    [Fintype K] [FiniteDimensional K F] (hK : Fintype.card K = 2)
    (A U : Fin 3 → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥) :
    ∃ (n : ℕ) (c : ScalarBroadcastCode A U n),
      (n : ℤ) = ⌈Allocation.actualNumericLP A U⌉ ∧
      Real.logb (Nat.card K) (Nat.card (Set.range c.encode)) ≤ n := by
  obtain ⟨n,hn,⟨c⟩⟩ := card_two_scalar_lcbc_achievability hK A U hAU hspan hsep
  exact ⟨n,c,hn,scalarBroadcastCode_cost_le c⟩

/-- The scalar binary endpoint uses the paper's raw fifteen-entry rank
formula, with no additional task/upload-feasibility premise. -/
theorem card_two_scalar_profile_achievability_cost
    [Fintype K] [FiniteDimensional K F] (hK : Fintype.card K = 2)
    (A U : Fin 3 → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥) :
    ∃ (n : ℕ) (c : ScalarBroadcastCode A U n),
      (n : ℤ) = ⌈Allocation.rawRankBound A U⌉ ∧
      Real.logb (Nat.card K) (Nat.card (Set.range c.encode)) ≤ n := by
  simpa only [Allocation.actualNumericLP_eq_rawRankBound] using
    card_two_scalar_lcbc_achievability_cost hK A U hAU hspan hsep

end UploadBroadcast
