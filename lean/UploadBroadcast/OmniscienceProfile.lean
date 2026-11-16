import UploadBroadcast.AllocationProfile
import UploadBroadcast.LinearAlgebra
import UploadBroadcast.ProfileTransport

namespace UploadBroadcast.OmniscienceProfile
open Module
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

theorem totalDemand_eq_sum_rank (T : Task K F) :
    (Profile.totalDemand T : ℝ) = ∑ i, (condRank (T.U i) (T.A i) : ℝ) := by
  unfold Profile.totalDemand
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_sub (Submodule.finrank_mono (T.side_le_signal i))]
  unfold condRank
  rw [sup_eq_right.mpr (T.side_le_signal i), Nat.cast_sub (Submodule.finrank_mono (T.side_le_signal i))]

theorem sum_reindex_three (f : Three → ℝ) (p : Equiv.Perm Three) :
    ∑ i, f i = f (p 0) + f (p 1) + f (p 2) := by
  rw [← Equiv.sum_comp p f]
  simp [Fin.sum_univ_succ,add_assoc]

/-- Exact first-family omniscience profile in every user order. -/
theorem first_entry (T : Task K F) (hU : ∀ i, T.U i = ⊤) (p : Equiv.Perm Three) :
    Profile.firstEntry T (p 0) (p 1) (p 2) = condRank ⊤ (T.A (p 0)) := by
  rw [Profile.firstEntry,totalDemand_eq_sum_rank]
  simp only [hU,inf_top_eq,sup_top_eq]
  rw [sum_reindex_three (fun i => (condRank ⊤ (T.A i) : ℝ)) p]
  ring

/-- Exact nine doubled second-family omniscience entries. -/
theorem second_entry (T : Task K F) (hU : ∀ i, T.U i = ⊤)
    (p : Equiv.Perm Three) (ell : Three) :
    2 * Profile.secondEntry T (p 0) (p 1) (p 2) ell =
      (∑ i, (condRank ⊤ (T.A i) : ℝ)) - condRank ⊤ (T.A ell) := by
  rw [Profile.secondEntry,totalDemand_eq_sum_rank]
  simp only [hU,inf_top_eq,sup_top_eq]
  rw [sum_reindex_three (fun i => (condRank ⊤ (T.A i) : ℝ)) p]
  ring

/-- A feasible relay on omniscience has the identical conditional deficits;
this is an actual rank identity, independent of a chosen coordinate basis. -/
theorem relay_deficits (T : Task K F) (hU : ∀ i, T.U i = ⊤)
    (P : Submodule K F) (hP : T.RelayFeasible P) (i : Three) :
    condRank P (T.A i ⊓ P) = condRank ⊤ (T.A i) := by
  have h := relay_condRank (T.A i) (T.U i) P (T.side_le_signal i) (hP i)
  simpa only [hU,top_inf_eq] using h

end UploadBroadcast.OmniscienceProfile
