import UploadBroadcast.IntrinsicUploadReduction

/-!
# Source endpoint: intrinsic upload parameters for every legal normal form

The active-pair complement, simultaneous graph correction, residual pair
complement, private/tripod chart, and demand-graph lifts are all arbitrary.
Their exact subspace geometry, not the desired rank equality, is required.
-/
namespace UploadBroadcast.Task.ActivePairSelection
open Module IntrinsicUploadRanks
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 16384
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  {T : Task K F} (s u : T.ActivePairSelection)
  (t : s.pairReducedTask.ActivePairSelection) (v : u.pairReducedTask.ActivePairSelection)

noncomputable def postResidualChoiceEquiv :
    LinearMap.ker t.totalPairProjection ≃ₗ[K] LinearMap.ker v.totalPairProjection :=
  (s.postResidualQuotientEquiv t).trans (u.postResidualQuotientEquiv v).symm

theorem postResidualChoice_mapTask :
    Profile.mapTask (s.postResidualChoiceEquiv u t v) t.pairResidualTask = v.pairResidualTask := by
  rw [postResidualChoiceEquiv,←mapTask_trans,s.postResidualQuotient_mapTask,
    ←u.postResidualQuotient_mapTask v]
  exact ResidualRelayAssembly.mapTask_inverse _ (u.postResidualQuotientEquiv v).symm

/-- Every rank is unchanged when both pair-selection stages and the residual
private/tripod chart are varied independently. -/
theorem all_rank_choices_independent [Finite K] [FiniteDimensional K F]
    (c : t.pairResidualTask.PrivateTripodChart) (d : v.pairResidualTask.PrivateTripodChart) :
    (∀ i, finrank K (s.pairReducedTask.pairKnown i) = finrank K (u.pairReducedTask.pairKnown i)) ∧
    c.privateDimension = d.privateDimension ∧ c.commonDimension = d.commonDimension ∧
    c.pureDimension = d.pureDimension ∧ c.mixedDimension = d.mixedDimension ∧
    c.tripodDimension = d.tripodDimension := by
  refine ⟨?_,c.dimensions_equiv d (s.postResidualChoiceEquiv u t v)
    (s.postResidualChoice_mapTask u t v)⟩
  intro i
  exact (s.pairReduced_pairKnown_finrank i).trans
    ((s.active_factor_finrank i).trans ((u.active_factor_finrank i).symm.trans
      (u.pairReduced_pairKnown_finrank i).symm))
end UploadBroadcast.Task.ActivePairSelection

namespace UploadBroadcast.Task.PrivateTripodChart
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 16384
open Module ResidualTaskAssembly
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] {T : Task K F} (c : T.PrivateTripodChart)

omit [FiniteDimensional K F] in
/-- The chart's mixed count can be evaluated using any legal graph lifts. -/
theorem mixedDimension_eq_any_lifts (g : DemandData (privateTrim c.toTask)) :
    c.mixedDimension =
      let S := pureRows₁ (privateTrim c.toTask) ⊔ pureRows₂ (privateTrim c.toTask) ⊔
        pureRows₃ (privateTrim c.toTask)
      finrank K ((LinearMap.ker (DemandData.incidence (task := privateTrim c.toTask))).map
        (S.mkQ.comp g.relationRows)) :=
  IntrinsicUploadRanks.mixedRank_lift_independent (privateTrim c.toTask)
    (selectedTrimData c.toTask c.sides.1 c.sides.2.1 c.sides.2.2) g
end UploadBroadcast.Task.PrivateTripodChart

namespace UploadBroadcast.Task
open Module
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 16384
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- An actual coupled coefficient retraction for completely arbitrary legal
normal-form choices on the original common-side quotient. -/
noncomputable def uploadReductionWithChoices (T : Task K F)
    (s : (T.quotientTask T.commonKnown).ActivePairSelection)
    (t : s.pairReducedTask.ActivePairSelection)
    (c : t.pairResidualTask.PrivateTripodChart) :=
  let r₀ := Classical.choice (T.exists_quotientRetraction T.commonKnown T.commonKnown_le)
  let r₁ := ((T.quotientTask T.commonKnown).coordinateRetraction s.simultaneous).trans
    s.pairPassiveRetraction
  let r₂ : PassiveRetraction s.pairReducedTask
      (Profile.directSum t.pairOmniscienceTask t.pairResidualTask) := by
    have r := s.pairReducedTask.coordinateRetraction t.pairResidualEquivalence.symm
    rw [t.pairResidual_mapTask s.pairReduced_pairKnown_le] at r
    exact r
  c.afterRetraction t.pairOmniscienceTask T ((r₀.trans r₁).trans r₂)

/-- Every arbitrary selected active pair has the original intrinsic rank. -/
theorem pairRank_all_choices [FiniteDimensional K F] (T : Task K F)
    (s : (T.quotientTask T.commonKnown).ActivePairSelection) (i : Three) :
    finrank K (s.pairReducedTask.pairKnown i) = T.intrinsicActivePairRank i :=
  (s.pairReduced_pairKnown_finrank i).trans
    ((s.active_factor_finrank i).trans (T.intrinsicActivePairRank_quotient i).symm)

/-- The manuscript upload formula holds for every legal normal form, with
all choices quantified rather than hidden behind one canonical selection. -/
theorem minimum_upload_all_choices [Finite K] [FiniteDimensional K F] (T : Task K F)
    (s : (T.quotientTask T.commonKnown).ActivePairSelection)
    (t : s.pairReducedTask.ActivePairSelection)
    (c : t.pairResidualTask.PrivateTripodChart) :
    T.uploadOptimum = c.uploadFormula (T.intrinsicActivePairRank 0)
      (T.intrinsicActivePairRank 1) (T.intrinsicActivePairRank 2) := by
  have h := c.uploadOptimum_from t s.pairReduced_pairKnown_le T (T.uploadReductionWithChoices s t c)
  simpa only [T.pairRank_all_choices s 0,T.pairRank_all_choices s 1,
    T.pairRank_all_choices s 2] using h

/-- Full appendix coordinate-independence assertion for the original task:
all three pair ranks and the private, common, pure, mixed and total tripod
counts are independent of both reduction selections and both arbitrary charts.
The complete formula also equals the already verified original-task formula. -/
theorem intrinsic_upload_parameters [Finite K] [FiniteDimensional K F] (T : Task K F)
    (s u : (T.quotientTask T.commonKnown).ActivePairSelection)
    (t : s.pairReducedTask.ActivePairSelection) (v : u.pairReducedTask.ActivePairSelection)
    (c : t.pairResidualTask.PrivateTripodChart) (d : v.pairResidualTask.PrivateTripodChart) :
    (∀ i, finrank K (s.pairReducedTask.pairKnown i) = T.intrinsicActivePairRank i ∧
      finrank K (u.pairReducedTask.pairKnown i) = T.intrinsicActivePairRank i) ∧
    c.privateDimension = d.privateDimension ∧ c.commonDimension = d.commonDimension ∧
    c.pureDimension = d.pureDimension ∧ c.mixedDimension = d.mixedDimension ∧
    c.tripodDimension = d.tripodDimension ∧
    c.uploadFormula (T.intrinsicActivePairRank 0) (T.intrinsicActivePairRank 1)
      (T.intrinsicActivePairRank 2) = T.minimumUploadFormula := by
  obtain ⟨_,hp,hc,hpu,hm,ht⟩ := s.all_rank_choices_independent u t v c d
  refine ⟨fun i => ⟨T.pairRank_all_choices s i,T.pairRank_all_choices u i⟩,
    hp,hc,hpu,hm,ht,?_⟩
  exact (T.minimum_upload_all_choices s t c).symm.trans T.minimum_upload
end UploadBroadcast.Task
