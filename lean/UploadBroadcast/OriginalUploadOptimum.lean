import UploadBroadcast.FullResidualAssembly
import UploadBroadcast.CommonTripodAssembly
import UploadBroadcast.ResidualPureTransport
import UploadBroadcast.ResidualTaskRanks
import UploadBroadcast.PassiveComposition
import UploadBroadcast.GlobalUploadAssembly

/-! Actual full-task reduction from an arbitrary feasible coefficient task.
Every operation is a concrete coefficient retraction, including products and
coordinate regrouping. Thus uploads may couple all factors nonlinearly. -/
namespace UploadBroadcast
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F V W : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

namespace Task.PrivateTripodChart
variable {S : Task K V} (c : S.PrivateTripodChart)
def toRetraction : PassiveRetraction S c.toTask := S.coordinateRetraction c.chart.symm

noncomputable def rightRetraction (T : Task K F) :
    PassiveRetraction (Profile.directSum T S) (Profile.directSum T c.toTask) :=
  (PassiveRetraction.refl T).prod c.toRetraction

noncomputable def afterRetraction (T : Task K F) (U : Task K W)
    (r : PassiveRetraction U (Profile.directSum T S)) :
    PassiveRetraction U (Profile.directSum T c.toTask) :=
  r.trans (c.rightRetraction T)
end Task.PrivateTripodChart

namespace Task
/-- Full active-pair reduction as one coefficient retraction. -/
noncomputable def pairReductionRetraction (T : Task K F) : PassiveRetraction T T.pairReduction :=
  (Classical.choice (T.exists_quotientRetraction T.commonKnown T.commonKnown_le)).trans
    (((T.quotientTask T.commonKnown).coordinateRetraction T.selectedPairs.simultaneous).trans
      T.selectedPairs.pairPassiveRetraction)

/-- Original-task coefficient transport through normalization, active-pair
reduction, pair separation and the residual private/tripod chart. -/
noncomputable def pairCanonicalRetraction (T : Task K F) :=
  let r₁ := T.normalizationRetraction.trans T.normalized.pairReductionRetraction
  let r₂ : PassiveRetraction T.preResidual
      (Profile.directSum T.pairOmniscienceFactor T.pairFreeResidual) := by
    have r := T.preResidual.coordinateRetraction T.residualPairSelection.pairResidualEquivalence.symm
    rw [T.residualPairSelection.pairResidual_mapTask T.normalized.pairReduction_pairKnown_le] at r
    exact r
  T.pairFreeChart.afterRetraction T.pairOmniscienceFactor T (r₁.trans r₂)

end Task

private theorem task_eq_spaces {T S : Task K F} (hA : T.A = S.A) (hU : T.U = S.U) : T = S := by
  cases T; cases S; cases hA; cases hU; rfl

/-- Associating direct sums is an exact coordinate identity, not an assumed
separability property of operational regions. -/
theorem mapTask_directSum_assoc (T : Task K F) (S : Task K V) (R : Task K W) :
    Profile.mapTask (LinearEquiv.prodAssoc K F V W).symm
      (Profile.directSum T (Profile.directSum S R)) =
      Profile.directSum (Profile.directSum T S) R := by
  apply task_eq_spaces
  · funext i
    ext x
    change x ∈ ((T.A i).prod ((S.A i).prod (R.A i))).map (LinearEquiv.prodAssoc K F V W).symm.toLinearMap ↔ _
    rw [Submodule.mem_map_equiv]
    change (x.1.1 ∈ T.A i ∧ x.1.2 ∈ S.A i ∧ x.2 ∈ R.A i) ↔
      (x.1.1 ∈ T.A i ∧ x.1.2 ∈ S.A i) ∧ x.2 ∈ R.A i
    tauto
  · funext i
    ext x
    change x ∈ ((T.U i).prod ((S.U i).prod (R.U i))).map (LinearEquiv.prodAssoc K F V W).symm.toLinearMap ↔ _
    rw [Submodule.mem_map_equiv]
    change (x.1.1 ∈ T.U i ∧ x.1.2 ∈ S.U i ∧ x.2 ∈ R.U i) ↔
      (x.1.1 ∈ T.U i ∧ x.1.2 ∈ S.U i) ∧ x.2 ∈ R.U i
    tauto

noncomputable def associateRetraction (T : Task K F) (S : Task K V) (R : Task K W) :
    PassiveRetraction (Profile.directSum T (Profile.directSum S R))
      (Profile.directSum (Profile.directSum T S) R) := by
  have r := (Profile.directSum T (Profile.directSum S R)).coordinateRetraction
    (LinearEquiv.prodAssoc K F V W).symm
  rw [mapTask_directSum_assoc] at r
  exact r

namespace ResidualTaskAssembly
open ResidualUpload
variable {P₁ P₂ P₃ D : Type*}
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]
  (task : Task K (Ambient P₁ P₂ P₃ D))
  (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
  (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
  (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)

/-- All private and passive-row operations combined as actual coefficient maps. -/
noncomputable def canonicalRetraction :
    PassiveRetraction task (canonicalReduction task h₀ h₁ h₂) := by
  let g := selectedTrimData task h₀ h₁ h₂
  obtain ⟨hs₀,hs₁,hs₂⟩ := privateTrim_sides task h₀ h₁ h₂
  obtain ⟨hc₀,hc₁,hc₂⟩ := g.correctedTask_sides hs₀ hs₁ hs₂
  obtain ⟨hr₀,hr₁,hr₂⟩ := g.correctedTask_rows
  exact (trimRetraction task h₀ h₁ h₂).trans
    (((privateTrim task).coordinateRetraction (privateGaugeShear g.emptyCorrection)).trans
      (rowRetraction g.correctedTask hc₀ hc₁ hc₂ g.activeRows hr₀ hr₁ hr₂))

noncomputable def commonComplement : Submodule K D :=
  Classical.choose (CommonTripodAssembly.commonRows task).exists_isCompl

theorem commonComplement_isCompl :
    IsCompl (CommonTripodAssembly.commonRows task) (commonComplement task) :=
  Classical.choose_spec (CommonTripodAssembly.commonRows task).exists_isCompl

/-- The actual complementary task after removing the common omniscience rows. -/
noncomputable def zeroCommonTask :=
  CommonTripodAssembly.residualTask task h₀ h₁ h₂ (commonComplement task)

noncomputable def commonRetraction :
    PassiveRetraction task
      (Profile.directSum (CommonTripodAssembly.commonTask task) (zeroCommonTask task h₀ h₁ h₂)) := by
  have r := task.coordinateRetraction
    (CommonTripodAssembly.splitEquiv (CommonTripodAssembly.commonRows task)
      (commonComplement task) (commonComplement_isCompl task)).symm
  rw [CommonTripodAssembly.common_product_mapTask task h₀ h₁ h₂
    (commonComplement task) (commonComplement_isCompl task)] at r
  exact r

/-- Common rows are separated after the original private coordinates have
been trimmed, matching the manuscript's order of rank definitions. -/
noncomputable def trimmedCommonTask :=
  zeroCommonTask (privateTrim task) (privateTrim_sides task h₀ h₁ h₂).1
    (privateTrim_sides task h₀ h₁ h₂).2.1 (privateTrim_sides task h₀ h₁ h₂).2.2

noncomputable def finalDemandData :=
  selectedDemandData (trimmedCommonTask task h₀ h₁ h₂) rfl rfl rfl

/-- The final residual, with full private use and active tripod rows. -/
noncomputable def finalResidual := (finalDemandData task h₀ h₁ h₂).activeRowReduction

noncomputable def DemandData.activeRetraction (g : DemandData task) :
    PassiveRetraction task g.activeRowReduction := by
  obtain ⟨hc₀,hc₁,hc₂⟩ := g.correctedTask_sides h₀ h₁ h₂
  obtain ⟨hr₀,hr₁,hr₂⟩ := g.correctedTask_rows
  exact (task.coordinateRetraction (privateGaugeShear g.emptyCorrection)).trans
    (rowRetraction g.correctedTask hc₀ hc₁ hc₂ g.activeRows hr₀ hr₁ hr₂)

noncomputable def splitActiveRetraction (om : Task K F) :
    PassiveRetraction (Profile.directSum om task)
      (Profile.directSum (Profile.directSum om (CommonTripodAssembly.commonTask (privateTrim task)))
        (finalResidual task h₀ h₁ h₂)) := by
  let c := CommonTripodAssembly.commonTask (privateTrim task)
  let z := trimmedCommonTask task h₀ h₁ h₂
  have r₁ := (PassiveRetraction.refl om).prod (trimRetraction task h₀ h₁ h₂)
  have r₂ := (PassiveRetraction.refl om).prod (commonRetraction (privateTrim task)
    (privateTrim_sides task h₀ h₁ h₂).1 (privateTrim_sides task h₀ h₁ h₂).2.1
    (privateTrim_sides task h₀ h₁ h₂).2.2)
  have r₃ := associateRetraction om c z
  have r₄ := (PassiveRetraction.refl (Profile.directSum om c)).prod
    (DemandData.activeRetraction z rfl rfl rfl (finalDemandData task h₀ h₁ h₂))
  exact ((r₁.trans r₂).trans r₃).trans r₄

theorem finalResidual_zero_common :
    pureRows₁ (finalResidual task h₀ h₁ h₂) ⊓ pureRows₂ (finalResidual task h₀ h₁ h₂) ⊓
      pureRows₃ (finalResidual task h₀ h₁ h₂) = ⊥ := by
  apply (finalDemandData task h₀ h₁ h₂).activeRowReduction_common_pure_eq_bot rfl rfl rfl
  exact CommonTripodAssembly.residual_commonRows_eq_bot (privateTrim task)
    (privateTrim_sides task h₀ h₁ h₂).1 (privateTrim_sides task h₀ h₁ h₂).2.1
    (privateTrim_sides task h₀ h₁ h₂).2.2 _ (commonComplement_isCompl _)

theorem finalResidual_fully_used :
    used₁ (finalResidual task h₀ h₁ h₂) = ⊤ ∧
    used₂ (finalResidual task h₀ h₁ h₂) = ⊤ ∧
    used₃ (finalResidual task h₀ h₁ h₂) = ⊤ := by
  obtain ⟨hu₁,hu₂,hu₃⟩ := (finalDemandData task h₀ h₁ h₂).activeRowReduction_used
  change used₁ (finalDemandData task h₀ h₁ h₂).activeRowReduction = _ ∧
    used₂ (finalDemandData task h₀ h₁ h₂).activeRowReduction = _ ∧
    used₃ (finalDemandData task h₀ h₁ h₂).activeRowReduction = _
  rw [hu₁,hu₂,hu₃]
  obtain ⟨hz₁,hz₂,hz₃⟩ := CommonTripodAssembly.residual_used (privateTrim task)
    (privateTrim_sides task h₀ h₁ h₂).1 (privateTrim_sides task h₀ h₁ h₂).2.1
    (privateTrim_sides task h₀ h₁ h₂).2.2 (commonComplement (privateTrim task))
    (commonComplement_isCompl (privateTrim task))
  change used₁ (zeroCommonTask (privateTrim task) _ _ _) = _ ∧
    used₂ (zeroCommonTask (privateTrim task) _ _ _) = _ ∧
    used₃ (zeroCommonTask (privateTrim task) _ _ _) = _
  rw [show used₁ (zeroCommonTask (privateTrim task) _ _ _) = _ from hz₁,
    show used₂ (zeroCommonTask (privateTrim task) _ _ _) = _ from hz₂,
    show used₃ (zeroCommonTask (privateTrim task) _ _ _) = _ from hz₃]
  exact privateTrim_fully_used task

noncomputable def splitOmniscience (om : Task K F) :=
  Profile.directSum om (CommonTripodAssembly.commonTask (privateTrim task))

noncomputable def afterRetraction (om : Task K F) (U : Task K V)
    (r : PassiveRetraction U (Profile.directSum om task)) :=
  r.trans (splitActiveRetraction task h₀ h₁ h₂ om)

end ResidualTaskAssembly
end UploadBroadcast
