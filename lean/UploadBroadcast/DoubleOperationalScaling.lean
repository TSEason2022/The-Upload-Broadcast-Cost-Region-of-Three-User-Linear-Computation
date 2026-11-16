import UploadBroadcast.OriginalUploadTheorem
import UploadBroadcast.LinearCodeSum
import UploadBroadcast.BlockFlatten

/-! Actual arbitrary-block repackaging proves upload homogeneity on two
identical tasks. No additivity of unrelated upload problems is asserted. -/
namespace UploadBroadcast
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

def sourceDoubleGroupsEquiv (L : ℕ) : Source K F (2*L) ≃ₗ[K] Source K (F × F) L :=
  ((sourceGroupsEquiv 2 L).trans (LinearEquiv.finTwoArrow K (Source K F L))).trans
    (sourceProdEquiv L).symm

def observedDoubleGroupsEquiv (L : ℕ) (A : Submodule K F) :
    Source K A (2*L) ≃ₗ[K] Source K (A.prod A) L :=
  ((sourceGroupsEquiv 2 L).trans (LinearEquiv.finTwoArrow K (Source K A L))).trans
    (observedProdEquiv L A A).symm

theorem observedDoubleGroups_observe (L : ℕ) (A : Submodule K F)
    (x : Source K F (2*L)) :
    observedDoubleGroupsEquiv L A (observe K F A x) =
      observe K (F × F) (A.prod A) (sourceDoubleGroupsEquiv L x) := by
  ext a j
  rfl

namespace Task.Code
variable {T : Task K F} {L : ℕ} {M : Three → Type*} {S : Type*}

/-- Flatten a code on two coefficient copies into twice as many original
source instances, retaining exactly the same message alphabets. -/
def flattenDouble (c : (Profile.directSum T T).Code L M S) : T.Code (2*L) M S where
  encode i a := c.encode i (observedDoubleGroupsEquiv L (T.A i) a)
  broadcast := c.broadcast
  decode i b a := (observedDoubleGroupsEquiv L (T.U i)).symm
    (c.decode i b (observedDoubleGroupsEquiv L (T.A i) a))
  zero_error x i := by
    apply (observedDoubleGroupsEquiv L (T.U i)).injective
    simp only [LinearEquiv.apply_symm_apply,observedDoubleGroups_observe]
    exact c.zero_error (sourceDoubleGroupsEquiv L x) i

theorem flattenDouble_encode_range (c : (Profile.directSum T T).Code L M S) (i : Three) :
    Set.range (c.flattenDouble.encode i) = Set.range (c.encode i) := by
  change Set.range ((c.encode i) ∘ observedDoubleGroupsEquiv L (T.A i)) = _
  rw [Set.range_comp,EquivLike.range_eq_univ (observedDoubleGroupsEquiv L (T.A i)),
    Set.image_univ]

theorem flattenDouble_transmitted (c : (Profile.directSum T T).Code L M S) :
    c.flattenDouble.transmitted = c.transmitted ∘ sourceDoubleGroupsEquiv L := by
  funext x
  simp only [transmitted,flattenDouble,observedDoubleGroups_observe,Function.comp_apply,
    Profile.directSum]

theorem flattenDouble_transmitted_range (c : (Profile.directSum T T).Code L M S) :
    Set.range c.flattenDouble.transmitted = Set.range c.transmitted := by
  rw [flattenDouble_transmitted,Set.range_comp,
    EquivLike.range_eq_univ (sourceDoubleGroupsEquiv L),Set.image_univ]

variable [Finite K] [FiniteDimensional K F]

theorem flattenDouble_costs (c : (Profile.directSum T T).Code L M S) :
    c.flattenDouble.uploadCost = c.uploadCost / 2 ∧
      c.flattenDouble.broadcastCost = c.broadcastCost / 2 := by
  constructor
  · simp only [uploadCost,flattenDouble_encode_range,Nat.cast_mul,Nat.cast_ofNat,
      div_div,mul_comm]
  · simp only [broadcastCost,flattenDouble_transmitted_range,Nat.cast_mul,Nat.cast_ofNat,
      div_div,mul_comm]
end Task.Code

namespace Task
variable [Finite K] [FiniteDimensional K F]

/-- The minimum upload is exactly homogeneous under two identical coefficient
copies, proved using arbitrary nonlinear-code flattening and actual attaining
linear uploads, rather than an unproved additivity claim. -/
theorem uploadOptimum_double (T : Task K F) :
    (Profile.directSum T T).uploadOptimum = 2*T.uploadOptimum := by
  obtain ⟨r,b,c,hn,hc⟩ := T.minimum_upload_two_instance
  have hu : (c.directSum c).toCode.uploadCost ≤ 2*T.uploadOptimum := by
    have h := (c.directSum_cost_bounds c).1
    rw [T.minimum_upload]
    simp only [Nat.cast_add,Finset.sum_add_distrib] at h
    have he : (∑ i, (r i : ℝ))/2 = T.minimumUploadFormula := by
      simpa only [Nat.cast_sum] using hn
    linarith
  apply uploadOptimum_eq_of_code (c.directSum c).toCode (by decide) (2*T.uploadOptimum) hu
  intro L m s d hL
  have h := d.flattenDouble.uploadOptimum_le (Nat.mul_pos (by decide) hL)
  rw [d.flattenDouble_costs.1] at h
  linarith

/-- Consequently the source upload formula also doubles, independently of
how its private, pair, and tripod charts were selected. -/
theorem minimumUploadFormula_double (T : Task K F) :
    (Profile.directSum T T).minimumUploadFormula = 2*T.minimumUploadFormula := by
  rw [← (Profile.directSum T T).minimum_upload,← T.minimum_upload,T.uploadOptimum_double]
end Task
end UploadBroadcast
