import UploadBroadcast.OriginalUploadOptimum
import UploadBroadcast.PairReductionRanks

/-!
# Source endpoint for active reduction

Starting with an arbitrary feasible task, retain the active pair factor and
perform private trimming and passive tripod cancellation on the actual
private/tripod factor. Every intermediate map is a constructed coefficient
retraction, so the conclusion concerns jointly encoded nonlinear codes.

The side-preserving shear and pair decomposition are also recorded on the
original common quotient, before any passive coordinates are deleted.
-/
namespace UploadBroadcast
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

namespace Task.PrivateTripodChart
open ResidualTaskAssembly ResidualUpload
variable {S : Task K F} (c : S.PrivateTripodChart)

/-- The entire residual reduction, selected from the actual charted task. -/
noncomputable def activeResidual :=
  canonicalReduction c.toTask c.sides.1 c.sides.2.1 c.sides.2.2

/-- Actual coefficient maps, rather than equality of separately coded regions. -/
noncomputable def activeResidualRetraction : PassiveRetraction c.toTask c.activeResidual :=
  canonicalRetraction c.toTask c.sides.1 c.sides.2.1 c.sides.2.2

/-- One simultaneous private trim suffices; the following tripod operations
cannot reintroduce unused private coordinates. -/
theorem activeResidual_fully_used :
    used₁ c.activeResidual = ⊤ ∧ used₂ c.activeResidual = ⊤ ∧
      used₃ c.activeResidual = ⊤ :=
  canonicalReduction_fully_used c.toTask c.sides.1 c.sides.2.1 c.sides.2.2

/-- The surviving sides are exactly private-plus-v/r/(r-v) tripod sides. -/
theorem activeResidual_sides : type_of%
    (canonicalReduction_sides c.toTask c.sides.1 c.sides.2.1 c.sides.2.2) :=
  canonicalReduction_sides c.toTask c.sides.1 c.sides.2.1 c.sides.2.2

/-- The residual signal quotients are genuine subspaces of the two remote
private blocks and the retained tripod row space. -/
theorem activeResidual_signal_quotients :
    c.activeResidual.U 0 = c.activeResidual.A 0 ⊔
      ((c.activeResidual.U 0).map demandQuotient₁).map demandLift₁ ∧
    c.activeResidual.U 1 = c.activeResidual.A 1 ⊔
      ((c.activeResidual.U 1).map demandQuotient₂).map demandLift₂ ∧
    c.activeResidual.U 2 = c.activeResidual.A 2 ⊔
      ((c.activeResidual.U 2).map demandQuotient₃).map demandLift₃ :=
  actual_signal_quotients c.activeResidual c.activeResidual_sides.1
    c.activeResidual_sides.2.1 c.activeResidual_sides.2.2

/-- The row dimension after cancellation is the pure-span dimension plus
rank of the actual signed relation map on the zero-private kernel. -/
theorem activeResidual_rows_finrank [FiniteDimensional K F] :
    let t := privateTrim c.toTask
    let g := selectedTrimData c.toTask c.sides.1 c.sides.2.1 c.sides.2.2
    let P := pureRows₁ t ⊔ pureRows₂ t ⊔ pureRows₃ t
    Module.finrank K g.activeRows = Module.finrank K P +
      Module.finrank K ((LinearMap.ker (DemandData.incidence (task := t))).map
        (P.mkQ.comp g.relationRows)) :=
  (selectedTrimData c.toTask c.sides.1 c.sides.2.1 c.sides.2.2).activeRows_finrank

variable {V W : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Keep an arbitrary pair factor while reducing the actual coupled task. -/
noncomputable def withActivePairs (om : Task K V) :=
  Profile.directSum om c.activeResidual

noncomputable def afterActiveRetraction (om : Task K V) (T : Task K W)
    (r : PassiveRetraction T (Profile.directSum om c.toTask)) :=
  r.trans ((PassiveRetraction.refl om).prod c.activeResidualRetraction)

/-- Generic composition avoids re-synthesizing deeply nested original-task
ambient instances when exposing the source endpoint. -/
theorem afterActive_achievableAt_eq [Finite K] [FiniteDimensional K F]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (om : Task K V) (T : Task K W)
    (r : PassiveRetraction T (Profile.directSum om c.toTask)) (L : ℕ) :
    T.achievableAt L = (c.withActivePairs om).achievableAt L :=
  (c.afterActiveRetraction om T r).achievableAt_eq L

theorem afterActive_costRegion_eq [Finite K] [FiniteDimensional K F]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (om : Task K V) (T : Task K W)
    (r : PassiveRetraction T (Profile.directSum om c.toTask)) :
    T.costRegion = (c.withActivePairs om).costRegion :=
  (c.afterActiveRetraction om T r).costRegion_eq

/-- Complete geometric and operational residual conclusions in the same
constructed model, before specializing the original-task chart. -/
theorem afterActive_source [Finite K] [FiniteDimensional K F]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (om : Task K V) (T : Task K W)
    (r : PassiveRetraction T (Profile.directSum om c.toTask)) :
    (used₁ c.activeResidual = ⊤ ∧ used₂ c.activeResidual = ⊤ ∧
      used₃ c.activeResidual = ⊤) ∧
    (∀ L, T.achievableAt L = (c.withActivePairs om).achievableAt L) ∧
    T.costRegion = (c.withActivePairs om).costRegion :=
  ⟨c.activeResidual_fully_used,c.afterActive_achievableAt_eq om T r,
    c.afterActive_costRegion_eq om T r⟩

end Task.PrivateTripodChart

namespace Task
/-- Active pairs together with the fully trimmed private/tripod demand task. -/
noncomputable def activeReduction (T : Task K F) :=
  T.pairFreeChart.withActivePairs T.pairOmniscienceFactor

/-- Constructed reduction from the original task through common-known,
passive-pair, unused-private and passive-tripod removal. -/
noncomputable def activeReductionRetraction (T : Task K F) :=
  T.pairFreeChart.afterActiveRetraction T.pairOmniscienceFactor T T.pairCanonicalRetraction

/-- Exact source blocklength region equality, allowing arbitrary nonlinear
encoders, relay and decoders that couple the pair and residual factors. -/
theorem activeReduction_achievableAt_eq [Finite K] [FiniteDimensional K F]
    (T : Task K F) (L : ℕ) : type_of%
      (T.pairFreeChart.afterActive_achievableAt_eq T.pairOmniscienceFactor T
        T.pairCanonicalRetraction L) :=
  T.pairFreeChart.afterActive_achievableAt_eq T.pairOmniscienceFactor T
    T.pairCanonicalRetraction L

/-- The same constructed reduction preserves the closed regularized region. -/
theorem activeReduction_costRegion_eq [Finite K] [FiniteDimensional K F]
    (T : Task K F) : type_of%
      (T.pairFreeChart.afterActive_costRegion_eq T.pairOmniscienceFactor T
        T.pairCanonicalRetraction) :=
  T.pairFreeChart.afterActive_costRegion_eq T.pairOmniscienceFactor T T.pairCanonicalRetraction

/-- One global automorphism of the original common quotient preserves all
side spaces and simultaneously separates every active pair demand. Each
pair factor is split into complementary active and passive subspaces, and
the active dimension is the original intrinsic quotient-intersection rank. -/
theorem active_pair_source_geometry [FiniteDimensional K F] (T : Task K F) :
    let Q := T.quotientTask T.commonKnown
    let s := T.selectedPairs
    (∀ i, IsCompl (s.passive i) (s.activeFactor i)) ∧
    (∀ i, Module.finrank K (s.activeFactor i) = T.intrinsicActivePairRank i) ∧
    (∀ i, (Q.A i).map s.simultaneous.toLinearMap = Q.A i) ∧
    (∀ i, ((Q.U i).map s.simultaneous.toLinearMap).map (s.chart i).symm.toLinearMap =
      (s.activeFactor i).prod
        (((Q.U i).map (s.chart i).symm.toLinearMap).map
          (LinearMap.snd K (Q.pairKnown i) (s.residual i)))) :=
  ⟨T.selectedPairs.complementary,T.selectedPairs_activeFactor_finrank,
    T.selectedPairs.simultaneous_side,T.selectedPairs.simultaneous_separation⟩

/-- Source `prop:active-pair`, including the actual nonlinear reduction and
full private activity, with no chosen charts or preservation certificates as
hypotheses. The stronger endpoint also deletes the passive tripod rows. -/
theorem active_reduction_source [Finite K] [FiniteDimensional K F] (T : Task K F) :
    type_of% (And.intro (T.preResidual_pairKnown_finrank)
      (And.intro T.pairOmniscienceFactor_signal
        (T.pairFreeChart.afterActive_source T.pairOmniscienceFactor T T.pairCanonicalRetraction))) :=
  ⟨T.preResidual_pairKnown_finrank,T.pairOmniscienceFactor_signal,
    T.pairFreeChart.afterActive_source T.pairOmniscienceFactor T T.pairCanonicalRetraction⟩

end Task
end UploadBroadcast
