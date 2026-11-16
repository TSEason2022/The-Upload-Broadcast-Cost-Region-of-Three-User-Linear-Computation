import UploadBroadcast.PassiveRelayTransport
import UploadBroadcast.ResidualComponentAdditivity
import UploadBroadcast.OriginalUploadModel

/-! Final source restoration interface. The remaining global geometry is
isolated as a canonical Ω-plus-active-residual selection principle; every
original-task reduction and restoration is constructed here. -/
namespace UploadBroadcast

/-- Canonical global selection statement. This is a named proposition,
not an axiom or an assertion that the unfinished geometry is already proved. -/
def CanonicalScalarSelection (K : Type) [Field K] [Finite K] : Prop :=
  ∀ (C X₁ X₂ X₃ V : Type)
    [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup X₁] [Module K X₁] [FiniteDimensional K X₁]
    [AddCommGroup X₂] [Module K X₂] [FiniteDimensional K X₂]
    [AddCommGroup X₃] [Module K X₃] [FiniteDimensional K X₃]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    ∀ S : Task K V, ResidualComponentAdditivity.ActiveResidual S →
      (Profile.directSum (OmniscienceOperational.task (K:=K) (V:=C)
        (X₁:=X₁) (X₂:=X₂) (X₃:=X₃)) S).ScalarRelaySelection

namespace Task.PrivateTripodChart
open ResidualTaskAssembly
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F E W : Type} [Field K] [Finite K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {S : Task K F} (c : S.PrivateTripodChart) {pair : Task K E}
  (s : pair.ActivePairSelection) (ha : ∀ i, pair.pairKnown i ≤ pair.U i)
  (T : Task K W) (r : PassiveRetraction T (Profile.directSum s.pairOmniscienceTask c.toTask))

include s ha r in
/-- Source restoration uses the original coupled retraction, with no
independent-coding assumption on the input task. -/
theorem scalarSelection_from_canonical (hselect : CanonicalScalarSelection K) : T.ScalarRelaySelection := by
  let R := finalResidual c.toTask c.sides.1 c.sides.2.1 c.sides.2.2
  have hR : ResidualComponentAdditivity.ActiveResidual R :=
    ResidualComponentAdditivity.finalResidual_active c.toTask c.sides.1 c.sides.2.1 c.sides.2.2
  have hs := hselect (CommonTripodAssembly.commonRows (privateTrim c.toTask))
    (pair.pairKnown 0) (pair.pairKnown 1) (pair.pairKnown 2) _ R hR
  let red := r.trans (OriginalUpload.reduction s ha c.toTask c.sides.1 c.sides.2.1 c.sides.2.2)
  exact red.scalarRelaySelection_of_reduced hs

end Task.PrivateTripodChart

namespace Task
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F : Type} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Once the canonical geometric selection theorem is proved, the source's
arbitrary original task follows with all reductions constructed internally. -/
theorem scalarRelaySelection_of_canonical (hselect : CanonicalScalarSelection K)
    (T : Task K F) : T.ScalarRelaySelection :=
  T.pairFreeChart.scalarSelection_from_canonical T.residualPairSelection
    T.normalized.pairReduction_pairKnown_le T T.pairCanonicalRetraction hselect

end Task
end UploadBroadcast
