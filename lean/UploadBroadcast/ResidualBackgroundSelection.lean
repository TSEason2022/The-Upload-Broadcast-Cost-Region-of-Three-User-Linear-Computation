import UploadBroadcast.OriginalJointReduction

namespace UploadBroadcast
/-- The residual geometric selection theorem with an arbitrary fully demanded
background. This proposition contains no assumption of a selected relay. -/
def ResidualBackgroundSelection (K : Type) [Field K] [Finite K] : Prop :=
  ∀ (V W : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W],
    ∀ (S : Task K V), ResidualComponentAdditivity.ActiveResidual S →
    ∀ (O : Task K W), (∀ i, O.U i=⊤) →
    ∀ D : ℤ, Profile.rankBound (Profile.directSum S O) ≤ (D : ℝ) →
      ∃ P : Submodule K V, ∃ hg : S.LocallyGenerated P,
        S.RelayFeasible P ∧ (Module.finrank K P : ℝ)=S.uploadOptimum ∧
        ∀ r, Profile.entry (S.inducedRelay P hg) r+Profile.entry O r ≤ (D : ℝ)
end UploadBroadcast
