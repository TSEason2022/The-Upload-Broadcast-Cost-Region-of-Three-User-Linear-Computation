import UploadBroadcast.CycleProfile
import UploadBroadcast.JordanResonance

/-!
# Canonical Jordan-family positive demand-cycle repair

Every statement here applies to every field and every positive component size.
The construction has the exact fifteen profile entries in `thm:endpoint`.
Its optimality as an upload cost additionally requires the manuscript's
minimum-upload theorem and active-residual additivity; those are not assumed
or asserted by the results in this file.
-/
namespace UploadBroadcast.CycleRepair
variable (K : Type*) [Field K] (n : ℕ)

abbrev canonicalTask := task K (n+1)
  (JordanResonance.automorphism K n) (JordanResonance.head K n)
abbrev canonicalRepairedTask := repairedTask K (n+1)
  (JordanResonance.automorphism K n) (JordanResonance.head K n)

theorem canonical_repair_first_increment (r : Fin 6) :
    Profile.entry (canonicalRepairedTask K n) (.inl r) -
      Profile.entry (canonicalTask K n) (.inl r) = if r = 1 then 1 else 0 := by
  rw [repaired_firstProfile K (n+1) _ _ (JordanResonance.automorphism_injective K n)
    (JordanResonance.head_surjective K n),
    full_firstProfile K (n+1) _ _ (JordanResonance.automorphism_injective K n)
    (JordanResonance.head_surjective K n)]
  fin_cases r <;> simp
  all_goals ring

theorem canonical_repair_second_preserved (i l : Fin 3) :
    Profile.entry (canonicalRepairedTask K n) (.inr (i,l)) =
      Profile.entry (canonicalTask K n) (.inr (i,l)) := by
  have hp := repaired_secondProfile K (n+1) _ _ (JordanResonance.head_surjective K n)
    (JordanResonance.fixed_head_eq_zero K n) i l
  have hf := full_secondProfile K (n+1) _ _ (JordanResonance.head_surjective K n)
    (JordanResonance.fixed_head_eq_zero K n) i l
  change 2 * Profile.entry (canonicalRepairedTask K n) (.inr (i,l)) = _ at hp
  change 2 * Profile.entry (canonicalTask K n) (.inr (i,l)) = _ at hf
  linarith

/-- The explicit canonical positive-cycle relay has the asserted dimension,
locality, feasibility, one first-family increment, and no second-family loss. -/
theorem canonical_positive_repair :
    (canonicalTask K n).LocallyGenerated (LinearMap.range (relayMap K (n+1))) ∧
    (canonicalTask K n).RelayFeasible (LinearMap.range (relayMap K (n+1))) ∧
    Module.finrank K (LinearMap.range (relayMap K (n+1))) = 3*(n+1)+4 ∧
    (∀ r : Fin 6, Profile.entry (canonicalRepairedTask K n) (.inl r) -
      Profile.entry (canonicalTask K n) (.inl r) = if r = 1 then 1 else 0) ∧
    (∀ i l : Fin 3, Profile.entry (canonicalRepairedTask K n) (.inr (i,l)) =
      Profile.entry (canonicalTask K n) (.inr (i,l))) := by
  exact ⟨task_relay_locally_generated K (n+1) _ _, task_relay_feasible K (n+1) _ _,
    relay_finrank K (n+1), canonical_repair_first_increment K n,
    canonical_repair_second_preserved K n⟩

end UploadBroadcast.CycleRepair
