import UploadBroadcast.AllocationProfile
import UploadBroadcast.ScalarAchievability
import UploadBroadcast.BinaryAchievability

/-! Original-field scalar realizations of the exact fifteen-entry conditional-rank
maximum. The general q ≥ 3 statement needs only Aᵢ ≤ Uᵢ, not upload feasibility.
The binary statement makes the side-information separation hypotheses explicit. -/
namespace UploadBroadcast
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Scalar LCBC achievability at the exact fifteen-entry ceiling over any finite
field of at least three elements, without an upload-feasibility assumption. -/
theorem scalar_profile_achievability [Finite K]
    (A U : Fin 3 → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (hq : 3 ≤ Nat.card K) :
    ∃ n : ℕ, (n : ℤ) = ⌈Allocation.rawRankBound A U⌉ ∧
      Nonempty (ScalarBroadcastCode A U n) := by
  simpa only [Allocation.actualNumericLP_eq_rawRankBound] using
    scalar_lcbc_achievability A U hAU hq

/-- The actual encoder's attained-alphabet cost obeys the exact profile ceiling. -/
theorem scalar_profile_achievability_cost [Finite K]
    (A U : Fin 3 → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (hq : 3 ≤ Nat.card K) :
    ∃ (n : ℕ) (c : ScalarBroadcastCode A U n),
      (n : ℤ) = ⌈Allocation.rawRankBound A U⌉ ∧
      Real.logb (Nat.card K) (Nat.card (Set.range c.encode)) ≤ n := by
  simpa only [Allocation.actualNumericLP_eq_rawRankBound] using
    scalar_lcbc_achievability_cost A U hAU hq

/-- Task specialization, with the original Profile.rankBound definition. -/
theorem task_scalar_profile_achievability [Finite K]
    (T : Task K F) (hq : 3 ≤ Nat.card K) :
    ∃ n : ℕ, (n : ℤ) = ⌈Profile.rankBound T⌉ ∧
      Nonempty (ScalarBroadcastCode T.A T.U n) := by
  simpa only [Allocation.actualNumericLP_eq_rankBound] using
    scalar_lcbc_achievability T.A T.U T.side_le_signal hq

section Binary
variable {B : Type*} [AddCommGroup B] [Module (ZMod 2) B]
  [FiniteDimensional (ZMod 2) B]

/-- Binary scalar achievability with spanning and separated side-information
subspaces, at the ceiling of the exact fifteen-entry rank maximum. -/
theorem binary_scalar_profile_achievability
    (A U : Fin 3 → Submodule (ZMod 2) B) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥) :
    ∃ n : ℕ, (n : ℤ) = ⌈Allocation.rawRankBound A U⌉ ∧
      Nonempty (ScalarBroadcastCode A U n) := by
  simpa only [Allocation.actualNumericLP_eq_rawRankBound] using
    binary_scalar_lcbc_achievability A U hAU hspan hsep

/-- The actual binary encoder's attained-alphabet cost obeys the exact ceiling. -/
theorem binary_scalar_profile_achievability_cost
    (A U : Fin 3 → Submodule (ZMod 2) B) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥) :
    ∃ (n : ℕ) (c : ScalarBroadcastCode A U n),
      (n : ℤ) = ⌈Allocation.rawRankBound A U⌉ ∧
      Real.logb (Nat.card (ZMod 2)) (Nat.card (Set.range c.encode)) ≤ n := by
  simpa only [Allocation.actualNumericLP_eq_rawRankBound] using
    binary_scalar_lcbc_achievability_cost A U hAU hspan hsep

/-- Binary task specialization retaining precisely the structural hypotheses
used to coordinate the common, pair, and aligned blocks over F₂. -/
theorem task_binary_scalar_profile_achievability
    (T : Task (ZMod 2) B) (hspan : (⨆ i, T.A i) = ⊤)
    (hsep : T.A 0 ⊓ (T.A 1 ⊔ T.A 2) = ⊥) :
    ∃ n : ℕ, (n : ℤ) = ⌈Profile.rankBound T⌉ ∧
      Nonempty (ScalarBroadcastCode T.A T.U n) := by
  simpa only [Allocation.actualNumericLP_eq_rankBound] using
    binary_scalar_lcbc_achievability T.A T.U T.side_le_signal hspan hsep

end Binary
end UploadBroadcast
