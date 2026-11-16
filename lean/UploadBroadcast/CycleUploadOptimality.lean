import UploadBroadcast.CycleUploadGeometry

namespace UploadBroadcast.CycleUploadOptimality
open Module CycleRepair ResidualComponentAdditivity
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 30000
set_option synthInstance.maxSize 4096
variable (K : Type*) [Field K] (n : ℕ)

local instance ambient_fd : FiniteDimensional K (Ambient K n) := by infer_instance

private theorem actual_task_ext {F : Type*} [AddCommGroup F] [Module K F]
    {T S : Task K F} (ha : T.A=S.A) (hu : T.U=S.U) : T=S := by
  cases T
  cases S
  cases ha
  cases hu
  rfl

private theorem active_swap_of_triple_zero
    {F : Type*} [AddCommGroup F] [Module K F] (T : Task K F)
    (h : ActiveResidual T) (hz : T.U 0 ⊓ T.U 1 ⊓ T.U 2=⊥) :
    ActiveResidual (Profile.reindexTask cycleUserSwap T) := by
  constructor
  · exact h.disjoint₀₁.symm
  · exact h.disjoint₁₂
  · exact h.disjoint₀₂
  · change T.A 1 ⊔ T.A 0 ⊔ T.A 2=⊤
    simpa only [sup_comm (T.A 1) (T.A 0)] using h.spanning
  · intro i j hij
    exact h.private_active _ _ (cycleUserSwap.injective.ne hij)
  · change T.A 1 ⊓ (T.A 0 ⊔ T.A 2) ≤ T.U 2 ⊔ (T.U 1 ⊓ T.U 0)
    rw [inf_comm (T.U 1) (T.U 0)]
    intro x hx
    obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp hx.2
    have ha' : a ∈ T.A 0 ⊓ (T.A 1 ⊔ T.A 2) := by
      refine ⟨ha,?_⟩
      have hh := (T.A 1 ⊔ T.A 2).sub_mem (Submodule.mem_sup_left hx.1)
        (Submodule.mem_sup_right hb)
      simpa only [←he,add_sub_cancel_right] using hh
    rw [←he]
    exact Submodule.add_mem _ (h.tripod_active ha')
      (Submodule.mem_sup_left (T.side_le_signal 2 hb))
  · unfold commonSeed
    change (T.A 1 ⊓ (T.U 1 ⊓ T.U 0 ⊓ T.U 2)) ⊓ _=⊥
    rw [inf_comm (T.U 1) (T.U 0),hz,inf_bot_eq,bot_inf_eq]

private def headVector : Vec K (n+1) := fun i => if i=0 then 1 else 0

private theorem headVector_fixed :
    JordanResonance.automorphism K n (headVector K n)=headVector K n := by
  funext i
  rw [JordanResonance.automorphism_apply]
  suffices JordanResonance.shift K n (headVector K n) i=0 by rw [this,add_zero]
  dsimp [JordanResonance.shift]
  split
  · rename_i h
    have hn : (⟨i.val+1,h⟩ : Fin (n+1))≠0 := by
      intro he
      have hh := congrArg Fin.val he
      simp only [Fin.val_mk,Fin.val_zero] at hh
      omega
    simp [headVector,hn]
  · rfl

private theorem headVector_head : JordanResonance.head K n (headVector K n)=1 := by
  simp [headVector]

theorem canonical_active : ActiveResidual (canonicalTask K n) :=
  task_active K (n+1) _ _ (headVector K n) (headVector_fixed K n)
    (headVector_head K n) (JordanResonance.fixed_head_eq_zero K n)

theorem reverse_active (A : Vec K n ≃ₗ[K] Vec K n) (H : Vec K n →ₗ[K] K)
    (w : Vec K n) (hw : A w=w) (hh : H w=1)
    (hjoint : ∀ v : Vec K n, A v=v → H v=0 → v=0) :
    ActiveResidual (reverseTask K n A.toLinearMap H) := by
  let B := A.symm.toLinearMap
  let G := H.comp B
  have hw' : B w=w := (A.symm_apply_eq).mpr hw.symm
  have hg : G w=1 := by
    change H (B w)=1
    rw [hw',hh]
  have hj : ∀ v : Vec K n, B v=v → G v=0 → v=0 := by
    intro v hv hh
    apply hjoint v
    · have hv' := congrArg A hv
      simpa only [B,LinearEquiv.coe_coe,A.apply_symm_apply] using hv'.symm
    · change H (B v)=0 at hh
      rwa [hv] at hh
  let S := task K n B G
  have ha : ActiveResidual S := task_active K n B G w hw' hg hj
  have hf := ha.map (cycleFlip K n)
  have hz : (Profile.mapTask (cycleFlip K n) S).U 0 ⊓
      (Profile.mapTask (cycleFlip K n) S).U 1 ⊓
      (Profile.mapTask (cycleFlip K n) S).U 2=⊥ := by
    change (signal K n B G 0).map _ ⊓ (signal K n B G 1).map _ ⊓
      (signal K n B G 2).map _=⊥
    rw [←Submodule.map_inf (cycleFlip K n).toLinearMap (cycleFlip K n).injective,
      ←Submodule.map_inf (cycleFlip K n).toLinearMap (cycleFlip K n).injective,
      triple_eq_bot K n B G hj,Submodule.map_bot]
  have hs := active_swap_of_triple_zero K (Profile.mapTask (cycleFlip K n) S) hf hz
  have he : Profile.mapTask (cycleFlip K n) S =
      Profile.reindexTask cycleUserSwap (reverseTask K n A.toLinearMap H) :=
    cycleFlip_task K n A H
  rw [he] at hs
  have he' : Profile.reindexTask cycleUserSwap
      (Profile.reindexTask cycleUserSwap (reverseTask K n A.toLinearMap H))=
        reverseTask K n A.toLinearMap H := by
    apply actual_task_ext <;> funext i <;> fin_cases i <;> rfl
  rwa [he'] at hs

theorem canonical_reverse_active : ActiveResidual (canonicalReverseTask K n) :=
  reverse_active K (n+1) (JordanResonance.equivalence K n) (JordanResonance.head K n)
    (headVector K n) (headVector_fixed K n) (headVector_head K n)
    (JordanResonance.fixed_head_eq_zero K n)

theorem uploadValue_side_eq {F : Type*} [AddCommGroup F] [Module K F]
    [FiniteDimensional K F] (T S : Task K F) (h : T.A=S.A) :
    uploadValue T=uploadValue S := by
  unfold uploadValue
  rw [h]

variable [Finite K]

/-- The concrete positive relay rank is the actual nonlinear, regularized U*. -/
theorem canonical_positive_optimal :
    (finrank K (LinearMap.range (relayMap K (n+1))) : ℝ)=
      (canonicalTask K n).uploadOptimum := by
  have hd : (finrank K (LinearMap.range (relayMap K (n+1))) : ℝ)=
      ((3*(n+1)+4 : ℕ) : ℝ) := congrArg (fun d : ℕ => (d : ℝ)) (relay_finrank K (n+1))
  have hv := task_uploadValue K (n+1) (JordanResonance.automorphism K n)
    (JordanResonance.head K n)
  exact hd.trans (hv.symm.trans
    (minimum_upload (canonicalTask K n) (canonical_active K n)).symm)

/-- The concrete reverse relay has the same genuine operational optimality. -/
theorem canonical_reverse_optimal :
    (finrank K (LinearMap.range (reverseRelayMap K (n+1))) : ℝ)=
      (canonicalReverseTask K n).uploadOptimum := by
  have hd : (finrank K (LinearMap.range (reverseRelayMap K (n+1))) : ℝ)=
      ((3*(n+1)+4 : ℕ) : ℝ) := congrArg (fun d : ℕ => (d : ℝ)) (reverse_relay_finrank K (n+1))
  have he : uploadValue (canonicalReverseTask K n)=uploadValue (canonicalTask K n) :=
    uploadValue_side_eq K (canonicalReverseTask K n) (canonicalTask K n) rfl
  have hv : uploadValue (canonicalReverseTask K n)=((3*(n+1)+4 : ℕ) : ℝ) :=
    he.trans (task_uploadValue K (n+1) (JordanResonance.automorphism K n)
      (JordanResonance.head K n))
  exact hd.trans (hv.symm.trans
    (minimum_upload (canonicalReverseTask K n) (canonical_reverse_active K n)).symm)

end UploadBroadcast.CycleUploadOptimality
