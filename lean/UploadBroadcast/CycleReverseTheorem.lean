import UploadBroadcast.CycleReverseTransport
import UploadBroadcast.JordanResonance

/-! Reverse demand-cycle profile identities, transported through an explicit
ambient equivalence. No profile-preservation assumption is used. -/
namespace UploadBroadcast.CycleRepair
variable (K : Type*) [Field K] (n : ℕ)
variable (A : Vec K n ≃ₗ[K] Vec K n) (H : Vec K n →ₗ[K] K)

private theorem inverse_head_surjective (hH : Function.Surjective H) :
    Function.Surjective (H.comp A.symm.toLinearMap) :=
  hH.comp A.symm.surjective

private theorem inverse_fixed_head
    (hjoint : ∀ w : Vec K n, A w = w → H w = 0 → w = 0) :
    ∀ w : Vec K n, A.symm w = w → (H.comp A.symm.toLinearMap) w = 0 → w = 0 := by
  intro w ha hh
  apply hjoint w
  · have he := congrArg A ha
    simpa using he.symm
  · simpa [LinearMap.comp_apply, ha] using hh

/-- User transposition induces this permutation of the six ordered first entries. -/
def reverseFirstIndex : Fin 6 → Fin 6 := ![2,3,0,1,5,4]

private theorem firstEntry_reverse_transport (i j k : Fin 3) :
    Profile.firstEntry (reverseTask K n A.toLinearMap H)
      (cycleUserSwap i) (cycleUserSwap j) (cycleUserSwap k) =
    Profile.firstEntry (task K n A.symm.toLinearMap (H.comp A.symm.toLinearMap)) i j k := by
  rw [← Profile.firstEntry_reindexTask, ← cycleFlip_task, Profile.firstEntry_mapTask]

private theorem repaired_firstEntry_reverse_transport (i j k : Fin 3) :
    Profile.firstEntry (reverseRepairedTask K n A.toLinearMap H)
      (cycleUserSwap i) (cycleUserSwap j) (cycleUserSwap k) =
    Profile.firstEntry (repairedTask K n A.symm.toLinearMap (H.comp A.symm.toLinearMap)) i j k := by
  rw [← Profile.firstEntry_reindexTask, ← cycleFlip_repairedTask, Profile.firstEntry_mapTask]

theorem reverse_first_transport (r : Fin 6) :
    Profile.entry (reverseTask K n A.toLinearMap H) (.inl r) =
    Profile.entry (task K n A.symm.toLinearMap (H.comp A.symm.toLinearMap))
      (.inl (reverseFirstIndex r)) := by
  have ht := firstEntry_reverse_transport K n A H
  fin_cases r
  · simpa [Profile.entry, Profile.firstOrder, reverseFirstIndex] using ht 1 0 2
  · simpa [Profile.entry, Profile.firstOrder, reverseFirstIndex] using ht 1 2 0
  · simpa [Profile.entry, Profile.firstOrder, reverseFirstIndex] using ht 0 1 2
  · simpa [Profile.entry, Profile.firstOrder, reverseFirstIndex] using ht 0 2 1
  · simpa [Profile.entry, Profile.firstOrder, reverseFirstIndex] using ht 2 1 0
  · simpa [Profile.entry, Profile.firstOrder, reverseFirstIndex] using ht 2 0 1

theorem reverse_repaired_first_transport (r : Fin 6) :
    Profile.entry (reverseRepairedTask K n A.toLinearMap H) (.inl r) =
    Profile.entry (repairedTask K n A.symm.toLinearMap (H.comp A.symm.toLinearMap))
      (.inl (reverseFirstIndex r)) := by
  have ht := repaired_firstEntry_reverse_transport K n A H
  fin_cases r
  · simpa [Profile.entry, Profile.firstOrder, reverseFirstIndex] using ht 1 0 2
  · simpa [Profile.entry, Profile.firstOrder, reverseFirstIndex] using ht 1 2 0
  · simpa [Profile.entry, Profile.firstOrder, reverseFirstIndex] using ht 0 1 2
  · simpa [Profile.entry, Profile.firstOrder, reverseFirstIndex] using ht 0 2 1
  · simpa [Profile.entry, Profile.firstOrder, reverseFirstIndex] using ht 2 1 0
  · simpa [Profile.entry, Profile.firstOrder, reverseFirstIndex] using ht 2 0 1

/-- Full reverse first-family profile in the manuscript's six-entry order. -/
theorem reverse_full_firstProfile (hH : Function.Surjective H) (r : Fin 6) :
    Profile.entry (reverseTask K n A.toLinearMap H) (.inl r) =
      ![(n : ℝ)+1,n+2,n+2,n+1,n+1,n+2] r := by
  rw [reverse_first_transport,
    full_firstProfile K n _ _ A.symm.injective (inverse_head_surjective K n A H hH)]
  fin_cases r <;> rfl

theorem reverse_repaired_firstProfile (hH : Function.Surjective H) (r : Fin 6) :
    Profile.entry (reverseRepairedTask K n A.toLinearMap H) (.inl r) =
      ![(n : ℝ)+1,n+2,n+2,n+2,n+1,n+2] r := by
  rw [reverse_repaired_first_transport,
    repaired_firstProfile K n _ _ A.symm.injective (inverse_head_surjective K n A H hH)]
  fin_cases r <;> rfl

theorem reverse_repair_first_increment (hH : Function.Surjective H) (r : Fin 6) :
    Profile.entry (reverseRepairedTask K n A.toLinearMap H) (.inl r) -
      Profile.entry (reverseTask K n A.toLinearMap H) (.inl r) = if r = 3 then 1 else 0 := by
  rw [reverse_repaired_first_transport, reverse_first_transport,
    repaired_firstProfile K n _ _ A.symm.injective (inverse_head_surjective K n A H hH),
    full_firstProfile K n _ _ A.symm.injective (inverse_head_surjective K n A H hH)]
  fin_cases r <;> simp [reverseFirstIndex]
  ring

private theorem secondEntry_swap (T : UploadBroadcast.Task K (Ambient K n))
    (i j k l : Fin 3) : Profile.secondEntry T i j k l = Profile.secondEntry T i k j l := by
  unfold Profile.secondEntry
  rw [sup_comm (T.U i ⊓ T.U j) (T.U i ⊓ T.U k)]
  ring

private theorem second_reindex_swap (T : UploadBroadcast.Task K (Ambient K n))
    (i l : Fin 3) :
    Profile.entry (Profile.reindexTask cycleUserSwap T) (.inr (i,l)) =
      Profile.entry T (.inr (cycleUserSwap i, cycleUserSwap l)) := by
  simp only [Profile.entry, Profile.secondEntry_reindexTask]
  fin_cases i <;> fin_cases l <;> norm_num [cycleUserSwap] <;>
    apply secondEntry_swap

theorem reverse_second_transport (i l : Fin 3) :
    Profile.entry (reverseTask K n A.toLinearMap H) (.inr (cycleUserSwap i,cycleUserSwap l)) =
    Profile.entry (task K n A.symm.toLinearMap (H.comp A.symm.toLinearMap)) (.inr (i,l)) := by
  rw [← second_reindex_swap, ← cycleFlip_task, Profile.entry_mapTask]

theorem reverse_repaired_second_transport (i l : Fin 3) :
    Profile.entry (reverseRepairedTask K n A.toLinearMap H) (.inr (cycleUserSwap i,cycleUserSwap l)) =
    Profile.entry (repairedTask K n A.symm.toLinearMap (H.comp A.symm.toLinearMap)) (.inr (i,l)) := by
  rw [← second_reindex_swap, ← cycleFlip_repairedTask, Profile.entry_mapTask]

theorem reverse_full_secondProfile (hH : Function.Surjective H)
    (hjoint : ∀ w : Vec K n, A w = w → H w = 0 → w = 0) (i l : Fin 3) :
    2 * Profile.entry (reverseTask K n A.toLinearMap H) (.inr (i,l)) = 3*((n : ℝ)+1) := by
  obtain ⟨i, rfl⟩ := cycleUserSwap.surjective i
  obtain ⟨l, rfl⟩ := cycleUserSwap.surjective l
  rw [reverse_second_transport]
  exact full_secondProfile K n _ _ (inverse_head_surjective K n A H hH)
    (inverse_fixed_head K n A H hjoint) i l

theorem reverse_repaired_secondProfile (hH : Function.Surjective H)
    (hjoint : ∀ w : Vec K n, A w = w → H w = 0 → w = 0) (i l : Fin 3) :
    2 * Profile.entry (reverseRepairedTask K n A.toLinearMap H) (.inr (i,l)) = 3*((n : ℝ)+1) := by
  obtain ⟨i, rfl⟩ := cycleUserSwap.surjective i
  obtain ⟨l, rfl⟩ := cycleUserSwap.surjective l
  rw [reverse_repaired_second_transport]
  exact repaired_secondProfile K n _ _ (inverse_head_surjective K n A H hH)
    (inverse_fixed_head K n A H hjoint) i l

theorem reverse_repair_second_preserved (hH : Function.Surjective H)
    (hjoint : ∀ w : Vec K n, A w = w → H w = 0 → w = 0) (i l : Fin 3) :
    Profile.entry (reverseRepairedTask K n A.toLinearMap H) (.inr (i,l)) =
      Profile.entry (reverseTask K n A.toLinearMap H) (.inr (i,l)) := by
  obtain ⟨i, rfl⟩ := cycleUserSwap.surjective i
  obtain ⟨l, rfl⟩ := cycleUserSwap.surjective l
  rw [reverse_repaired_second_transport, reverse_second_transport]
  have hp := repaired_secondProfile K n _ _ (inverse_head_surjective K n A H hH)
    (inverse_fixed_head K n A H hjoint) i l
  have hf := full_secondProfile K n _ _ (inverse_head_surjective K n A H hH)
    (inverse_fixed_head K n A H hjoint) i l
  linarith

abbrev canonicalReverseTask := reverseTask K (n+1)
  (JordanResonance.automorphism K n) (JordanResonance.head K n)
abbrev canonicalReverseRepairedTask := reverseRepairedTask K (n+1)
  (JordanResonance.automorphism K n) (JordanResonance.head K n)

/-- The canonical reverse relay has all fifteen asserted profile entries. -/
theorem canonical_reverse_repair :
    (canonicalReverseTask K n).LocallyGenerated (LinearMap.range (reverseRelayMap K (n+1))) ∧
    (canonicalReverseTask K n).RelayFeasible (LinearMap.range (reverseRelayMap K (n+1))) ∧
    Module.finrank K (LinearMap.range (reverseRelayMap K (n+1))) = 3*(n+1)+4 ∧
    (∀ r : Fin 6, Profile.entry (canonicalReverseRepairedTask K n) (.inl r) -
      Profile.entry (canonicalReverseTask K n) (.inl r) = if r = 3 then 1 else 0) ∧
    (∀ i l : Fin 3, Profile.entry (canonicalReverseRepairedTask K n) (.inr (i,l)) =
      Profile.entry (canonicalReverseTask K n) (.inr (i,l))) := by
  refine ⟨reverse_task_relay_locally_generated K (n+1) _ _,
    reverse_task_relay_feasible K (n+1) _ _, reverse_relay_finrank K (n+1), ?_, ?_⟩
  · exact reverse_repair_first_increment K (n+1) (JordanResonance.equivalence K n)
      (JordanResonance.head K n) (JordanResonance.head_surjective K n)
  · exact reverse_repair_second_preserved K (n+1) (JordanResonance.equivalence K n)
      (JordanResonance.head K n) (JordanResonance.head_surjective K n)
      (JordanResonance.fixed_head_eq_zero K n)

end UploadBroadcast.CycleRepair
