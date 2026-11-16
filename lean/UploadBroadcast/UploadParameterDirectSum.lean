import UploadBroadcast.ActualBlockGraph
import UploadBroadcast.IntrinsicUploadDirectSums

/-! Complete individual upload-parameter direct-sum endpoint. -/
namespace UploadBroadcast.UploadParameterDirectSum
open Module FiniteRelayAssembly ResidualUpload ResidualTaskAssembly
open BlockGraphDirectSum ActualBlockGraph
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K I : Type*} [Field K]
variable {P₁ P₂ P₃ D : I → Type*}
  [∀ a, AddCommGroup (P₁ a)] [∀ a, Module K (P₁ a)]
  [∀ a, AddCommGroup (P₂ a)] [∀ a, Module K (P₂ a)]
  [∀ a, AddCommGroup (P₃ a)] [∀ a, Module K (P₃ a)]
  [∀ a, AddCommGroup (D a)] [∀ a, Module K (D a)]
  (T : ∀ a, Task K (Ambient (P₁ a) (P₂ a) (P₃ a) (D a)))

theorem private₁_image (i : Three) :
    ((combinedTask T).U i).map private₁ = space (fun a => ((T a).U i).map private₁) := by
  change ((space fun a => (T a).U i).map (ambientChart (K:=K)).symm.toLinearMap).map private₁ = _
  rw [←Submodule.map_comp]
  exact blocks_image (fun a => private₁ (K:=K) (P₂:=P₂ a) (P₃:=P₃ a) (D:=D a))
    (fun a => (T a).U i)

theorem private₂_image (i : Three) :
    ((combinedTask T).U i).map private₂ = space (fun a => ((T a).U i).map private₂) := by
  change ((space fun a => (T a).U i).map (ambientChart (K:=K)).symm.toLinearMap).map private₂ = _
  rw [←Submodule.map_comp]
  exact blocks_image (fun a => private₂ (K:=K) (P₁:=P₁ a) (P₃:=P₃ a) (D:=D a))
    (fun a => (T a).U i)

theorem private₃_image (i : Three) :
    ((combinedTask T).U i).map private₃ = space (fun a => ((T a).U i).map private₃) := by
  change ((space fun a => (T a).U i).map (ambientChart (K:=K)).symm.toLinearMap).map private₃ = _
  rw [←Submodule.map_comp]
  exact blocks_image (fun a => private₃ (K:=K) (P₁:=P₁ a) (P₂:=P₂ a) (D:=D a))
    (fun a => (T a).U i)

theorem retained_private_spaces :
    used₁ (combinedTask T) = space (fun a => used₁ (T a)) ∧
    used₂ (combinedTask T) = space (fun a => used₂ (T a)) ∧
    used₃ (combinedTask T) = space (fun a => used₃ (T a)) := by
  unfold used₁ used₂ used₃
  rw [private₁_image,private₁_image,private₂_image,private₂_image,
    private₃_image,private₃_image,←space_sup,←space_sup,←space_sup]
  exact ⟨rfl,rfl,rfl⟩

/-- The literal retained-private parameter d_priv is additive for the
actual regrouped task, rather than inferred from a total-upload equality. -/
theorem private_dimension_additive [Fintype I]
    [∀ a, FiniteDimensional K (P₁ a)] [∀ a, FiniteDimensional K (P₂ a)]
    [∀ a, FiniteDimensional K (P₃ a)] :
    privateDimension (combinedTask T) = ∑ a, privateDimension (T a) := by
  obtain ⟨h₁,h₂,h₃⟩ := retained_private_spaces T
  unfold privateDimension
  rw [h₁,h₂,h₃,finrank_space,finrank_space,finrank_space]
  simp only [Finset.sum_add_distrib]

/-- In every pair-free chart of the actual regrouped task and every factor,
the individual private/common/pure counts are the corresponding sums. -/
theorem arbitrary_chart_ranks [Fintype I]
    [∀ a, FiniteDimensional K (P₁ a)] [∀ a, FiniteDimensional K (P₂ a)]
    [∀ a, FiniteDimensional K (P₃ a)] [∀ a, FiniteDimensional K (D a)]
    (c : (combinedTask T).PrivateTripodChart) (d : ∀ a, (T a).PrivateTripodChart) :
    c.privateDimension = ∑ a, (d a).privateDimension ∧
    c.commonDimension = ∑ a, (d a).commonDimension ∧
    c.pureDimension = ∑ a, (d a).pureDimension := by
  have he := IntrinsicUploadRanks.ranks_map (task T) (ambientChart (K:=K)).symm
  obtain ⟨hp,hc,hu⟩ := c.dimensions_eq_intrinsic
  change IntrinsicUploadRanks.commonRank (combinedTask T) = _ ∧
    IntrinsicUploadRanks.pureRank (combinedTask T) = _ ∧
    IntrinsicUploadRanks.privateRank (combinedTask T) = _ at he
  rw [hp,hc,hu,he.1,he.2.1,he.2.2,
    IntrinsicUploadDirectSums.commonRank_additive,
    IntrinsicUploadDirectSums.pureRank_additive,
    IntrinsicUploadDirectSums.privateRank_additive]
  simp only [fun a => (d a).dimensions_eq_intrinsic.1,
    fun a => (d a).dimensions_eq_intrinsic.2.1,
    fun a => (d a).dimensions_eq_intrinsic.2.2,and_self]

end UploadBroadcast.UploadParameterDirectSum
