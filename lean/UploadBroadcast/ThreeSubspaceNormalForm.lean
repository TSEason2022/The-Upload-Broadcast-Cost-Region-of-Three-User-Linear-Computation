import UploadBroadcast.ThreeSubspaceNormalFormCore

namespace UploadBroadcast
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

namespace InvariantTripleSplit
variable {A B C : Submodule K F}
/-- Private/tripod coordinates in the residual, in the original user order
of the last (23) peeling step. -/
def HasResidualNormalForm (s : InvariantTripleSplit A B C) : Prop :=
  HasPrivateTripodNormalForm s.third s.first s.second

theorem hasResidualNormalForm_of_pairwise (s : InvariantTripleSplit A B C)
    (h12 : Disjoint s.third s.first) (h13 : Disjoint s.third s.second)
    (h23 : Disjoint s.first s.second)
    (hspan : (s.third ⊔ s.first) ⊔ s.second = ⊤) : s.HasResidualNormalForm :=
  pairwise_disjoint_three_subspace_normal_form s.third s.first s.second h12 h13 h23 hspan
end InvariantTripleSplit

/-- Existence of the complete common/pair/private/tripod decomposition for
an arbitrary spanning triple. The peeling data certify the exact coefficient
subspaces in every removed factor; the residual equivalence certifies all
three final coefficient ranges. `liftResidualEquivalence` composes these
into an actual linear equivalence onto the original ambient space. -/
theorem exists_three_subspace_normal_form (A B C : Submodule K F)
    (hspan : (A ⊔ B) ⊔ C = ⊤) :
    ∃ s : ThreeSubspacePeeling A B C, s.pair23.HasResidualNormalForm := by
  obtain ⟨s⟩ := exists_three_subspace_peeling A B C
  exact ⟨s, s.pair23.hasResidualNormalForm_of_pairwise
    s.residual12 s.residual13 s.residual23 (s.spans hspan)⟩

end UploadBroadcast
