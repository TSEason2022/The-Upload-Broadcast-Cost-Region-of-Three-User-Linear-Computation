import UploadBroadcast.IntrinsicUploadInvariance
import UploadBroadcast.FiniteProductCoordinates

/-! Individual upload-rank additivity in genuine finite-product tasks. -/
namespace UploadBroadcast.IntrinsicUploadDirectSums
open Module FiniteRelayAssembly IntrinsicUploadRanks
open scoped BigOperators
variable {K I : Type*} {F : I → Type*} [Field K] [Fintype I]
  [∀ a, AddCommGroup (F a)] [∀ a, Module K (F a)]
  [∀ a, FiniteDimensional K (F a)] (T : ∀ a, Task K (F a))

omit [Fintype I] [∀ a, FiniteDimensional K (F a)] in
theorem pure_spaces :
    pure₀ (task T) = space (fun a => pure₀ (T a)) ∧
    pure₁ (task T) = space (fun a => pure₁ (T a)) ∧
    pure₂ (task T) = space (fun a => pure₂ (T a)) := by
  simp only [pure₀,pure₁,pure₂,task,←space_inf,←space_sup,and_self]

theorem commonRank_additive : commonRank (task T) = ∑ a, commonRank (T a) := by
  obtain ⟨h₀,h₁,h₂⟩ := pure_spaces T
  unfold commonRank
  rw [h₀,h₁,h₂,←space_inf,←space_inf,finrank_space]

theorem pureRank_additive : pureRank (task T) = ∑ a, pureRank (T a) := by
  obtain ⟨h₀,h₁,h₂⟩ := pure_spaces T
  unfold pureRank
  rw [h₀,h₁,h₂,←space_sup,←space_sup,finrank_space,commonRank_additive]
  unfold commonRank
  exact (Finset.sum_tsub_distrib Finset.univ fun a _ =>
    Submodule.finrank_mono (show pure₀ (T a) ⊓ pure₁ (T a) ⊓ pure₂ (T a) ≤
      pure₀ (T a) ⊔ pure₁ (T a) ⊔ pure₂ (T a) from
        le_trans (le_trans inf_le_left inf_le_left) (le_trans le_sup_left le_sup_left))).symm

theorem privateRank_additive : privateRank (task T) = ∑ a, privateRank (T a) := by
  simp only [privateRank,task,←space_sup,condRank_space,Finset.sum_add_distrib]

/-- All three chart parameters are individually additive for arbitrary legal
charts on the factors and on the genuine product task. -/
theorem chart_private_common_pure
    (c : (task T).PrivateTripodChart) (d : ∀ a, (T a).PrivateTripodChart) :
    c.privateDimension = ∑ a, (d a).privateDimension ∧
    c.commonDimension = ∑ a, (d a).commonDimension ∧
    c.pureDimension = ∑ a, (d a).pureDimension := by
  simp only [c.dimensions_eq_intrinsic.1,c.dimensions_eq_intrinsic.2.1,
    c.dimensions_eq_intrinsic.2.2,fun a => (d a).dimensions_eq_intrinsic.1,
    fun a => (d a).dimensions_eq_intrinsic.2.1,fun a => (d a).dimensions_eq_intrinsic.2.2,
    privateRank_additive,commonRank_additive,pureRank_additive,and_self]

omit [Fintype I] [∀ a, FiniteDimensional K (F a)] in
theorem commonKnown_space : (task T).commonKnown = space (fun a => (T a).commonKnown) := by
  ext x
  simp only [Task.commonKnown,task,Submodule.mem_iInf,Submodule.mem_pi,Set.mem_univ,forall_const]
  exact forall_comm

omit [Fintype I] [∀ a, FiniteDimensional K (F a)] in
theorem pairKnown_space (i : Three) : (task T).pairKnown i = space (fun a => (T a).pairKnown i) := by
  ext x
  simp only [Task.pairKnown,task,Submodule.mem_iInf,Submodule.mem_pi,Set.mem_univ,forall_const]
  constructor
  · intro h a j hj
    exact h j hj a
  · intro h j hj a
    exact h a j hj

/-- Every active-pair rank is additive in the original actual tasks, before
any complements or reductions have been selected. -/
theorem activePairRank_additive (i : Three) :
    (task T).intrinsicActivePairRank i = ∑ a, (T a).intrinsicActivePairRank i := by
  unfold Task.intrinsicActivePairRank
  rw [pairKnown_space,commonKnown_space]
  change finrank K ↥(space (fun a => (T a).U i) ⊓ _) - _ = _
  rw [←space_inf,finrank_space,finrank_space]
  exact (Finset.sum_tsub_distrib Finset.univ fun a _ =>
    Submodule.finrank_mono (le_inf
      ((T a).commonKnown_le i |>.trans ((T a).side_le_signal i))
      ((T a).commonKnown_le_pairKnown i))).symm

end UploadBroadcast.IntrinsicUploadDirectSums
