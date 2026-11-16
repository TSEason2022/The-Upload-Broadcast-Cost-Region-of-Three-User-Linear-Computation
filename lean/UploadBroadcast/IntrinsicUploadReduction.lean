import UploadBroadcast.IntrinsicUploadSelections

/-! Arbitrary active/passive pair reduction choices retain exactly the same
intrinsic pair-quotient task, including its actual signal subspaces. -/
namespace UploadBroadcast.Task.ActivePairSelection
open Module IntrinsicUploadRanks
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  {T : Task K F} (s : T.ActivePairSelection)

lemma totalPassive_mem_pair (i : Three) (x : F) (hx : x ∈ T.pairKnown i) :
    s.totalPassiveProjection x ∈ T.pairKnown i := by
  classical
  have he : s.totalPassiveProjection x = s.passiveProjection i x := by
    simp only [totalPassiveProjection,LinearMap.sum_apply]
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact s.passiveProjection_own j x (T.pairKnown_le i j hji hx)
    · simp
  rw [he,s.passiveProjection_apply,s.chart_pair]
  exact Subtype.prop _

lemma totalPassive_mem_pairOmniscience (x : F) :
    s.totalPassiveProjection x ∈ T.pairOmniscience := by
  classical
  simp only [totalPassiveProjection,LinearMap.sum_apply]
  apply T.pairOmniscience.sum_mem
  intro i _
  rw [s.passiveProjection_apply,s.chart_pair]
  exact (le_iSup T.pairKnown i) (Subtype.prop _)

/-- Pair sums commute with removal of passive pair directions. -/
theorem pairReduced_pairOmniscience :
    s.pairReducedTask.pairOmniscience =
      T.pairOmniscience.comap (LinearMap.ker s.totalPassiveProjection).subtype := by
  let p := Task.complementaryProjection s.totalPassiveProjection s.totalPassiveProjection_idempotent
  apply le_antisymm
  · apply iSup_le
    intro i
    rw [s.pairReducedTask_pairKnown]
    exact Submodule.comap_mono (le_iSup T.pairKnown i)
  · have hm : T.pairOmniscience.map p ≤ s.pairReducedTask.pairOmniscience := by
      rw [Task.pairOmniscience,Submodule.map_iSup]
      apply iSup_le
      intro i
      rintro y ⟨x,hx,rfl⟩
      apply (le_iSup s.pairReducedTask.pairKnown i)
      rw [s.pairReducedTask_pairKnown]
      change x-s.totalPassiveProjection x ∈ T.pairKnown i
      exact (T.pairKnown i).sub_mem hx (s.totalPassive_mem_pair i x hx)
    intro x hx
    have hpx : p x = x := by
      apply Subtype.ext
      change (x : F)-s.totalPassiveProjection x = x
      rw [show s.totalPassiveProjection x = 0 from x.property,sub_zero]
    exact hpx ▸ hm ⟨x,hx,rfl⟩

variable (t : s.pairReducedTask.ActivePairSelection)

/-- Embed the twice-selected residual into the original pair quotient. -/
def postResidualQuotientMap :
    LinearMap.ker t.totalPairProjection →ₗ[K] (F ⧸ T.pairOmniscience) :=
  T.pairOmniscience.mkQ.comp ((LinearMap.ker s.totalPassiveProjection).subtype.comp
    (LinearMap.ker t.totalPairProjection).subtype)

lemma postResidual_pair_zero (x : LinearMap.ker s.totalPassiveProjection) :
    T.pairOmniscience.mkQ (t.totalPairProjection x : F) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have hx : t.totalPairProjection x ∈ s.pairReducedTask.pairOmniscience := by
    rw [←t.totalPairProjection_range]
    exact ⟨x,rfl⟩
  exact (s.pairReduced_pairOmniscience.le hx)

lemma postResidual_project_apply (x : F) :
    s.postResidualQuotientMap t
      (Task.complementaryProjection t.totalPairProjection t.totalPairProjection_idempotent
        (Task.complementaryProjection s.totalPassiveProjection s.totalPassiveProjection_idempotent x)) =
      T.pairOmniscience.mkQ x := by
  change T.pairOmniscience.mkQ
    ((x-s.totalPassiveProjection x) -
      (t.totalPairProjection (Task.complementaryProjection s.totalPassiveProjection
        s.totalPassiveProjection_idempotent x) : F)) = _
  rw [map_sub,s.postResidual_pair_zero t,sub_zero,map_sub,
    show T.pairOmniscience.mkQ (s.totalPassiveProjection x) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr (s.totalPassive_mem_pairOmniscience x),sub_zero]

lemma postResidualQuotientMap_bijective : Function.Bijective (s.postResidualQuotientMap t) := by
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm _ bot_le
    intro x hx
    have hxJ : ((x : LinearMap.ker s.totalPassiveProjection) : F) ∈ T.pairOmniscience :=
      (Submodule.Quotient.mk_eq_zero _).mp hx
    have hxJ' : (x : LinearMap.ker s.totalPassiveProjection) ∈ s.pairReducedTask.pairOmniscience :=
      s.pairReduced_pairOmniscience.ge hxJ
    have he := t.totalPairProjection_on_omniscience ⟨x,hxJ'⟩
    have hz : t.totalPairProjection (x : LinearMap.ker s.totalPassiveProjection) = 0 := x.property
    have hx0 : (x : LinearMap.ker s.totalPassiveProjection) = 0 := he.symm.trans hz
    exact Subtype.ext hx0
  · intro q
    obtain ⟨x,rfl⟩ := T.pairOmniscience.mkQ_surjective q
    exact ⟨_,s.postResidual_project_apply t x⟩

/-- The exact residual after arbitrary active/passive separation and arbitrary
pair factor extraction is the original intrinsic pair quotient. -/
noncomputable def postResidualQuotientEquiv :
    LinearMap.ker t.totalPairProjection ≃ₗ[K] (F ⧸ T.pairOmniscience) :=
  LinearEquiv.ofBijective (s.postResidualQuotientMap t) (s.postResidualQuotientMap_bijective t)

theorem postResidualQuotient_mapTask :
    Profile.mapTask (s.postResidualQuotientEquiv t) t.pairResidualTask =
      T.quotientTask T.pairOmniscience := by
  have hcomp : (s.postResidualQuotientEquiv t).toLinearMap.comp
      ((Task.complementaryProjection t.totalPairProjection t.totalPairProjection_idempotent).comp
        ((Task.complementaryProjection s.totalPassiveProjection s.totalPassiveProjection_idempotent).comp
          s.simultaneous.toLinearMap)) = T.pairOmniscience.mkQ := by
    apply LinearMap.ext
    intro x
    change s.postResidualQuotientMap t
      (Task.complementaryProjection t.totalPairProjection t.totalPairProjection_idempotent
        (Task.complementaryProjection s.totalPassiveProjection s.totalPassiveProjection_idempotent
          (s.simultaneous x))) = _
    rw [s.postResidual_project_apply]
    exact LinearMap.congr_fun s.simultaneous_mkQ x
  have hA : (Profile.mapTask (s.postResidualQuotientEquiv t) t.pairResidualTask).A =
      (T.quotientTask T.pairOmniscience).A := by
    funext i
    change ((((T.A i).map _).map _).map _).map _ = (T.A i).map _
    simp only [←Submodule.map_comp,LinearMap.comp_assoc,hcomp]
  have hU : (Profile.mapTask (s.postResidualQuotientEquiv t) t.pairResidualTask).U =
      (T.quotientTask T.pairOmniscience).U := by
    funext i
    change ((((T.U i).map _).map _).map _).map _ = (T.U i).map _
    simp only [←Submodule.map_comp,LinearMap.comp_assoc,hcomp]
  cases h : Profile.mapTask (s.postResidualQuotientEquiv t) t.pairResidualTask
  cases h' : T.quotientTask T.pairOmniscience
  simp only [h,h'] at hA hU
  cases hA
  cases hU
  rfl
end UploadBroadcast.Task.ActivePairSelection
