import UploadBroadcast.CycleProfile
import UploadBroadcast.ProfileTransport

/-! Explicit ambient linear transport from the positive to the reverse demand cycle. -/
namespace UploadBroadcast.CycleRepair
variable (K : Type*) [Field K] (n : ℕ)

/-- Swap the first two private blocks, V with R, and y with z. -/
def cycleFlip : Ambient K n ≃ₗ[K] Ambient K n where
  toFun p := (![p.1 1, p.1 0, p.1 2], ![p.2 1, p.2 0, p.2 2, p.2 4, p.2 3])
  invFun p := (![p.1 1, p.1 0, p.1 2], ![p.2 1, p.2 0, p.2 2, p.2 4, p.2 3])
  left_inv := by intro p; apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv := by intro p; apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_add' := by intro p q; apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_smul' := by intro c p; apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

/-- Relabel the first two users. -/
def cycleUserSwap : Equiv.Perm (Fin 3) := Equiv.swap 0 1

@[simp] theorem cycleUserSwap_zero : cycleUserSwap 0 = 1 := by decide
@[simp] theorem cycleUserSwap_one : cycleUserSwap 1 = 0 := by decide
@[simp] theorem cycleUserSwap_two : cycleUserSwap 2 = 2 := by decide

@[simp] theorem cycleFlip_twice (p : Ambient K n) :
    cycleFlip K n (cycleFlip K n p) = p := (cycleFlip K n).left_inv p

private theorem flip_side_point (i : Fin 3) (o : Vec K n × K × K) :
    cycleFlip K n (sideMap K n i o) =
      sideMap K n (cycleUserSwap i) (o.1, (if i = 2 then -o.2.1 else o.2.1), o.2.2) := by
  apply Prod.ext
  · funext j; fin_cases i <;> fin_cases j <;> simp [cycleFlip, sideMap]
  · funext j; fin_cases i <;> fin_cases j <;> simp [cycleFlip, sideMap]

theorem cycleFlip_side (i : Fin 3) :
    (side K n i).map (cycleFlip K n).toLinearMap = side K n (cycleUserSwap i) := by
  apply le_antisymm
  · rintro p ⟨q, ⟨o, rfl⟩, rfl⟩
    exact ⟨_, flip_side_point K n i o |>.symm⟩
  · rintro p ⟨o, rfl⟩
    refine ⟨sideMap K n i (o.1, (if i = 2 then -o.2.1 else o.2.1), o.2.2), ⟨_, rfl⟩, ?_⟩
    rw [show (cycleFlip K n).toLinearMap _ = cycleFlip K n _ from rfl, flip_side_point]
    fin_cases i <;> simp

private theorem positive_signal_mem (A : Vec K n →ₗ[K] Vec K n)
    (H : Vec K n →ₗ[K] K) (i : Fin 3) (p : Ambient K n) :
    p ∈ signal K n A H i ↔
      (![p.1 1 = p.1 2 ∧ p.2 1 = 0 ∧ p.2 2 = 0,
         p.1 0 = p.1 2 ∧ p.2 0 = 0 ∧ p.2 4 = 0,
         p.1 1 = A (p.1 0) ∧ p.2 0 + p.2 1 = H (p.1 0) ∧ p.2 3 = 0] i) := by
  fin_cases i
  · exact signal₁_mem K n A H p
  · exact signal₂_mem K n A H p
  · exact signal₃_mem K n A H p

private theorem reverse_signal_mem (A : Vec K n →ₗ[K] Vec K n)
    (H : Vec K n →ₗ[K] K) (i : Fin 3) (p : Ambient K n) :
    p ∈ reverseSignal K n A H i ↔
      (![p.1 1 = p.1 2 ∧ p.2 1 = 0 ∧ p.2 3 = 0,
         p.1 0 = p.1 2 ∧ p.2 0 = 0 ∧ p.2 2 = 0,
         p.1 1 = A (p.1 0) ∧ p.2 0 + p.2 1 = H (p.1 0) ∧ p.2 4 = 0] i) := by
  constructor
  · intro hp
    obtain ⟨a, ⟨oa, rfl⟩, b, ⟨ob, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hp
    fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, reverseDemandMap]
  · intro hp
    fin_cases i
    · refine Submodule.mem_sup.mpr ⟨sideMap K n 0 (p.1 0, p.2 0, p.2 4), ⟨_, rfl⟩,
        reverseDemandMap K n A H 0 (p.1 1, p.2 2), ⟨_, rfl⟩, ?_⟩
      simp only [Matrix.cons_val_zero] at hp
      apply Prod.ext <;> funext j <;> fin_cases j <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, reverseDemandMap, hp.1, hp.2.1, hp.2.2]
    · refine Submodule.mem_sup.mpr ⟨sideMap K n 1 (p.1 1, p.2 1, p.2 3), ⟨_, rfl⟩,
        reverseDemandMap K n A H 1 (p.1 0, p.2 4), ⟨_, rfl⟩, ?_⟩
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hp
      apply Prod.ext <;> funext j <;> fin_cases j <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, reverseDemandMap, hp.1, hp.2.1, hp.2.2]
    · refine Submodule.mem_sup.mpr ⟨sideMap K n 2 (p.1 2, p.2 1, p.2 2), ⟨_, rfl⟩,
        reverseDemandMap K n A H 2 (p.1 0, p.2 3), ⟨_, rfl⟩, ?_⟩
      simp only [Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero] at hp
      apply Prod.ext
      · funext j; fin_cases j <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, reverseDemandMap, hp.1]
      · funext j; fin_cases j <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, reverseDemandMap, hp.2.2]
        linear_combination -hp.2.1

/-- Pointwise transport, including the scalar side-space correction at user three. -/
theorem cycleFlip_signal_mem (A : Vec K n ≃ₗ[K] Vec K n)
    (H : Vec K n →ₗ[K] K) (i : Fin 3) (p : Ambient K n) :
    cycleFlip K n p ∈ reverseSignal K n A.toLinearMap H (cycleUserSwap i) ↔
      p ∈ signal K n A.symm.toLinearMap (H.comp A.symm.toLinearMap) i := by
  rw [reverse_signal_mem, positive_signal_mem]
  fin_cases i
  · simp [cycleFlip]
  · simp [cycleFlip]
  · simp only [cycleUserSwap_two, Matrix.cons_val_two, Matrix.cons_val_one,
      Matrix.cons_val_zero, cycleFlip, LinearEquiv.coe_mk, LinearMap.coe_mk,
      AddHom.coe_mk, LinearEquiv.coe_coe, LinearMap.comp_apply]
    constructor
    · rintro ⟨ha, hh, hz⟩
      have hv : p.1 1 = A.symm (p.1 0) := by rw [ha, A.symm_apply_apply]
      exact ⟨hv, by simpa [← hv, add_comm] using hh, hz⟩
    · rintro ⟨ha, hh, hz⟩
      exact ⟨by rw [ha, A.apply_symm_apply], by simpa [ha, add_comm] using hh, hz⟩

/-- Actual equality of the transported signal subspaces. -/
theorem cycleFlip_signal (A : Vec K n ≃ₗ[K] Vec K n)
    (H : Vec K n →ₗ[K] K) (i : Fin 3) :
    (signal K n A.symm.toLinearMap (H.comp A.symm.toLinearMap) i).map
      (cycleFlip K n).toLinearMap = reverseSignal K n A.toLinearMap H (cycleUserSwap i) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (cycleFlip_signal_mem K n A H i q).mpr hq
  · intro hp
    refine ⟨cycleFlip K n p, ?_, cycleFlip_twice K n p⟩
    apply (cycleFlip_signal_mem K n A H i _).mp
    simpa using hp

/-- The positive relay hyperplane maps exactly onto the reverse relay hyperplane. -/
theorem cycleFlip_relay :
    (LinearMap.range (relayMap K n)).map (cycleFlip K n).toLinearMap =
      LinearMap.range (reverseRelayMap K n) := by
  rw [relay_range_eq_kernel, reverse_relay_range_eq_kernel]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [LinearMap.mem_ker, relayForm, reverseRelayForm, cycleFlip] using hq
  · intro hp
    refine ⟨cycleFlip K n p, ?_, cycleFlip_twice K n p⟩
    simpa [LinearMap.mem_ker, relayForm, reverseRelayForm, cycleFlip] using hp

/-- The actual induced reverse relay task, in ambient coordinates. -/
def reverseRepairedTask (A : Vec K n →ₗ[K] Vec K n) (H : Vec K n →ₗ[K] K) :
    UploadBroadcast.Task K (Ambient K n) where
  A := fun i => side K n i ⊓ LinearMap.range (reverseRelayMap K n)
  U := fun i => reverseSignal K n A H i ⊓ LinearMap.range (reverseRelayMap K n)
  side_le_signal := fun _ => inf_le_inf le_sup_left le_rfl
  feasible := by
    intro i
    have h : (⨆ j : Fin 3, side K n j ⊓ LinearMap.range (reverseRelayMap K n)) =
        LinearMap.range (reverseRelayMap K n) := by
      simpa only [inf_comm] using (reverse_relay_locally_generated K n).symm
    rw [h]
    exact inf_le_right

private theorem task_ext {T S : UploadBroadcast.Task K (Ambient K n)}
    (ha : T.A = S.A) (hu : T.U = S.U) : T = S := by
  cases T
  cases S
  cases ha
  cases hu
  rfl

/-- Equality of full tasks, not merely their ranks. -/
theorem cycleFlip_task (A : Vec K n ≃ₗ[K] Vec K n) (H : Vec K n →ₗ[K] K) :
    Profile.mapTask (cycleFlip K n)
      (task K n A.symm.toLinearMap (H.comp A.symm.toLinearMap)) =
    Profile.reindexTask cycleUserSwap (reverseTask K n A.toLinearMap H) := by
  apply task_ext
  · funext i
    exact cycleFlip_side K n i
  · funext i
    exact cycleFlip_signal K n A H i

/-- Equality of repaired tasks follows by mapping each intersection with the relay. -/
theorem cycleFlip_repairedTask (A : Vec K n ≃ₗ[K] Vec K n) (H : Vec K n →ₗ[K] K) :
    Profile.mapTask (cycleFlip K n)
      (repairedTask K n A.symm.toLinearMap (H.comp A.symm.toLinearMap)) =
    Profile.reindexTask cycleUserSwap (reverseRepairedTask K n A.toLinearMap H) := by
  apply task_ext
  · funext i
    change ((side K n i) ⊓ _).map _ = _
    rw [Submodule.map_inf (cycleFlip K n).toLinearMap (cycleFlip K n).injective, cycleFlip_side, cycleFlip_relay]
    rfl
  · funext i
    change ((signal K n A.symm.toLinearMap (H.comp A.symm.toLinearMap) i) ⊓ _).map _ = _
    rw [Submodule.map_inf (cycleFlip K n).toLinearMap (cycleFlip K n).injective, cycleFlip_signal, cycleFlip_relay]
    rfl

end UploadBroadcast.CycleRepair
