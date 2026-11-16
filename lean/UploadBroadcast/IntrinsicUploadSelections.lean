import UploadBroadcast.IntrinsicUploadRanks

/-!
# Independence of arbitrary pair complements and private/tripod charts

Every pair-complement residual is identified with the same intrinsic quotient.
No equality of desired dimensions is a field of the chart or selection data.
-/
namespace UploadBroadcast.IntrinsicUploadRanks
open Module
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F V : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup V] [Module K V]

private theorem task_ext {T S : Task K F}
    (hA : T.A = S.A) (hU : T.U = S.U) : T = S := by
  cases T; cases S; cases hA; cases hU; rfl

/-- A zero-dimensional left factor has an actual coordinate equivalence. -/
def dropZero [Subsingleton V] : (V × F) ≃ₗ[K] F where
  toFun x := x.2
  invFun x := (0,x)
  left_inv _ := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem map_dropZero [Subsingleton V] (R : Task K V) (T : Task K F) :
    Profile.mapTask dropZero (Profile.directSum R T) = T := by
  apply task_ext <;> funext i
  all_goals
    ext x
    constructor
    · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
      exact hb
    · intro hx
      exact ⟨(0,x),⟨Submodule.zero_mem _,hx⟩,rfl⟩

/-- Adding a genuinely zero coefficient factor does not change any upload
optimum, by an actual coordinate map. -/
theorem uploadOptimum_dropZero [Finite K] [FiniteDimensional K F]
    [FiniteDimensional K V] [Subsingleton V] (R : Task K V) (T : Task K F) :
    (Profile.directSum R T).uploadOptimum = T.uploadOptimum := by
  have h := ((Profile.directSum R T).coordinateRetraction dropZero).uploadOptimum_eq
  rwa [map_dropZero] at h

/-- A zero task used only to instantiate the previously proved coupled
pair-plus-residual upload theorem. -/
def emptyTask : Task K (⊥ : Submodule K K) where
  A _ := ⊥
  U _ := ⊥
  side_le_signal _ := le_refl _
  feasible _ := bot_le

noncomputable def emptySelection : (emptyTask (K := K)).ActivePairSelection :=
  Classical.choice ((emptyTask (K := K)).exists_activePairSelection_of_commonKnown_eq_bot
    (Subsingleton.elim _ _))

theorem empty_active : ∀ i, (emptyTask (K := K)).pairKnown i ≤ (emptyTask (K := K)).U i :=
  fun _ => (Subsingleton.elim _ _).le

end UploadBroadcast.IntrinsicUploadRanks

namespace UploadBroadcast.Task.PrivateTripodChart
open Module ResidualTaskAssembly IntrinsicUploadRanks
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F V : Type*} [Field K] [Finite K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {T : Task K F} {S : Task K V} (c : T.PrivateTripodChart) (d : S.PrivateTripodChart)

/-- The rank formula computed in every legal chart equals the optimum of
that pair-free task, independently of any selected original-task reduction. -/
theorem uploadOptimum_self : T.uploadOptimum = c.uploadFormula 0 0 0 := by
  have h := OriginalUpload.uploadOptimum (emptySelection (K := K)) empty_active
    c.toTask c.sides.1 c.sides.2.1 c.sides.2.2
  have he := uploadOptimum_dropZero (emptySelection (K := K)).pairOmniscienceTask c.toTask
  have hv := c.canonicalValue_eq_formula (X₁ := (emptyTask (K := K)).pairKnown 0)
    (X₂ := (emptyTask (K := K)).pairKnown 1) (X₃ := (emptyTask (K := K)).pairKnown 2)
    0 0 0 finrank_zero_of_subsingleton finrank_zero_of_subsingleton
      finrank_zero_of_subsingleton
  exact c.toRetraction.uploadOptimum_eq.trans (he.symm.trans (h.trans hv))

/-- All five rank counts are invariant under every actual task coordinate
isomorphism and every legal private/tripod chart on either side. -/
theorem dimensions_equiv (e : F ≃ₗ[K] V) (he : Profile.mapTask e T = S) :
    c.privateDimension = d.privateDimension ∧ c.commonDimension = d.commonDimension ∧
    c.pureDimension = d.pureDimension ∧ c.mixedDimension = d.mixedDimension ∧
    c.tripodDimension = d.tripodDimension := by
  obtain ⟨hc₀,hc₁,hc₂⟩ := c.dimensions_eq_intrinsic
  obtain ⟨hd₀,hd₁,hd₂⟩ := d.dimensions_eq_intrinsic
  obtain ⟨he₁,he₂,he₀⟩ := ranks_map T e
  rw [he] at he₀ he₁ he₂
  have hp : c.privateDimension = d.privateDimension := hc₀.trans (he₀.symm.trans hd₀.symm)
  have hcom : c.commonDimension = d.commonDimension := hc₁.trans (he₁.symm.trans hd₁.symm)
  have hpu : c.pureDimension = d.pureDimension := hc₂.trans (he₂.symm.trans hd₂.symm)
  have heq : T.uploadOptimum = S.uploadOptimum := by
    have hh := (T.coordinateRetraction e).uploadOptimum_eq
    rwa [he] at hh
  have hf : c.uploadFormula 0 0 0 = d.uploadFormula 0 0 0 :=
    c.uploadOptimum_self.symm.trans (heq.trans d.uploadOptimum_self)
  have ht : c.tripodDimension = d.tripodDimension := by
    unfold uploadFormula omegaValue at hf
    rw [hp,hcom] at hf
    exact_mod_cast (show (c.tripodDimension : ℝ) = d.tripodDimension by linarith)
  refine ⟨hp,hcom,hpu,?_,ht⟩
  have hh := c.tripod_eq_pure_add_mixed
  have hh' := d.tripod_eq_pure_add_mixed
  omega
end UploadBroadcast.Task.PrivateTripodChart

namespace UploadBroadcast.Task.ActivePairSelection
open Module IntrinsicUploadRanks
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  {T : Task K F} (s : T.ActivePairSelection)

/-- Every arbitrary pair complement is canonically the quotient by the
intrinsic sum of the three pair-known spaces. -/
noncomputable def residualQuotientEquiv :
    LinearMap.ker s.totalPairProjection ≃ₗ[K] (F ⧸ T.pairOmniscience) :=
  (Submodule.quotientEquivOfIsCompl T.pairOmniscience _ s.pairResidual_complementary).symm

/-- The equivalence carries the actual side and signal images, not just the
ambient dimension, to the intrinsic quotient task. -/
theorem residualQuotient_mapTask :
    Profile.mapTask s.residualQuotientEquiv s.pairResidualTask =
      T.quotientTask T.pairOmniscience := by
  have hcomp : s.residualQuotientEquiv.toLinearMap.comp
      (Task.complementaryProjection s.totalPairProjection s.totalPairProjection_idempotent) =
        T.pairOmniscience.mkQ := by
    apply LinearMap.ext
    intro x
    change T.pairOmniscience.mkQ (x-s.totalPairProjection x) = T.pairOmniscience.mkQ x
    rw [map_sub,show T.pairOmniscience.mkQ (s.totalPairProjection x) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr (by rw [←s.totalPairProjection_range]; exact ⟨x,rfl⟩),sub_zero]
  apply IntrinsicUploadRanks.task_ext
  · funext i
    change ((T.A i).map _).map _ = (T.A i).map _
    rw [←Submodule.map_comp,hcomp]
  · funext i
    change ((T.U i).map _).map _ = (T.U i).map _
    rw [←Submodule.map_comp,hcomp]
end UploadBroadcast.Task.ActivePairSelection

namespace UploadBroadcast.IntrinsicUploadRanks
variable {K F V W : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem mapTask_trans (T : Task K F) (e : F ≃ₗ[K] V) (f : V ≃ₗ[K] W) :
    Profile.mapTask f (Profile.mapTask e T) = Profile.mapTask (e.trans f) T := by
  apply task_ext <;> funext i
  · exact (Submodule.map_comp e.toLinearMap f.toLinearMap (T.A i)).symm
  · exact (Submodule.map_comp e.toLinearMap f.toLinearMap (T.U i)).symm
end UploadBroadcast.IntrinsicUploadRanks

namespace UploadBroadcast.Task.ActivePairSelection
open Module IntrinsicUploadRanks
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  {T : Task K F} (s t : T.ActivePairSelection)

/-- Every pair-complement choice gives the same residual task up to a concrete
linear equivalence through the intrinsic quotient. -/
noncomputable def residualChoiceEquiv :
    LinearMap.ker s.totalPairProjection ≃ₗ[K] LinearMap.ker t.totalPairProjection :=
  s.residualQuotientEquiv.trans t.residualQuotientEquiv.symm

theorem residualChoice_mapTask :
    Profile.mapTask (s.residualChoiceEquiv t) s.pairResidualTask = t.pairResidualTask := by
  rw [residualChoiceEquiv,←mapTask_trans,s.residualQuotient_mapTask,
    ←t.residualQuotient_mapTask]
  exact ResidualRelayAssembly.mapTask_inverse _ t.residualQuotientEquiv.symm

/-- Source coordinate independence for arbitrary active-pair selections,
arbitrary complementary side charts, and arbitrary private/tripod charts.
The three pair ranks and all five residual rank counts agree. -/
theorem upload_ranks_selection_independent [Finite K] [FiniteDimensional K F]
    (c : s.pairResidualTask.PrivateTripodChart) (d : t.pairResidualTask.PrivateTripodChart) :
    (∀ i, finrank K (s.activeFactor i) = finrank K (t.activeFactor i)) ∧
    c.privateDimension = d.privateDimension ∧ c.commonDimension = d.commonDimension ∧
    c.pureDimension = d.pureDimension ∧ c.mixedDimension = d.mixedDimension ∧
    c.tripodDimension = d.tripodDimension := by
  refine ⟨?_,c.dimensions_equiv d (s.residualChoiceEquiv t) (s.residualChoice_mapTask t)⟩
  intro i
  exact (s.active_factor_finrank i).trans (t.active_factor_finrank i).symm

/-- The simultaneous active-pair correction is invisible in the intrinsic
pair quotient, for every selected graph correction. -/
theorem simultaneous_mkQ :
    T.pairOmniscience.mkQ.comp s.simultaneous.toLinearMap = T.pairOmniscience.mkQ := by
  apply LinearMap.ext
  intro x
  change T.pairOmniscience.mkQ (x-(∑ i,s.corrections i) x) = T.pairOmniscience.mkQ x
  rw [map_sub,show T.pairOmniscience.mkQ ((∑ i,s.corrections i) x) = 0 from ?_,sub_zero]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [LinearMap.sum_apply]
  apply T.pairOmniscience.sum_mem
  intro i _
  change s.chart i (s.correction i ((s.chart i).symm x).2,0) ∈ T.pairOmniscience
  rw [s.chart_pair]
  exact (le_iSup T.pairKnown i) (s.correction i ((s.chart i).symm x).2).property

/-- Quotient side and demand subspaces are exactly unchanged by the global
active-pair shear, independently of every complement and lift. -/
theorem simultaneous_quotientTask :
    (Profile.mapTask s.simultaneous T).quotientTask T.pairOmniscience =
      T.quotientTask T.pairOmniscience := by
  apply IntrinsicUploadRanks.task_ext
  · funext i
    change ((T.A i).map _).map _ = (T.A i).map _
    rw [←Submodule.map_comp,s.simultaneous_mkQ]
  · funext i
    change ((T.U i).map _).map _ = (T.U i).map _
    rw [←Submodule.map_comp,s.simultaneous_mkQ]
end UploadBroadcast.Task.ActivePairSelection
