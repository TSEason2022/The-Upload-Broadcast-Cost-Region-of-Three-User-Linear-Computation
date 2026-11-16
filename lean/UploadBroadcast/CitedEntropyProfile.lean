import UploadBroadcast.CitedEntropyCertificates
namespace UploadBroadcast.CitedEntropyCounterexample
open FiniteSubspaceCertificate

theorem conditional_rank (P : Space (K := K) (V := V)) (i : Three) (n : ℕ)
    (h : ((side i).join P).points.card = 5^(n+1)) :
    condRank P.submodule (side i).submodule = n := by
  unfold condRank
  rw [← Space.submodule_join,
    ((side i).join P).finrank_eq (n+1) (by simpa using h),
    (side i).finrank_eq 1 (by simpa using side_card i)]
  omega

theorem first_cond (t : Fin 2) (r : Fin 6) :
    condRank ((task (t.val+1)).U (Profile.firstOrder r).1 ⊓
      (task (t.val+1)).U (Profile.firstOrder r).2.1)
      ((task (t.val+1)).A (Profile.firstOrder r).2.1) = 1 := by
  change condRank ((signal _ _).submodule ⊓ (signal _ _).submodule) (side _).submodule = 1
  rw [← Space.submodule_meet]
  apply conditional_rank
  exact first_card t r

set_option maxHeartbeats 2000000 in
theorem last_cond (t : Fin 2) (r : Fin 6) :
    condRank ((task (t.val+1)).U (Profile.firstOrder r).2.2 ⊓
      ((task (t.val+1)).U (Profile.firstOrder r).1 ⊔
        (task (t.val+1)).U (Profile.firstOrder r).2.1))
      ((task (t.val+1)).A (Profile.firstOrder r).2.2) = 1 := by
  have hinf : Module.finrank K
      ↥((task (t.val+1)).U (Profile.firstOrder r).1 ⊓
        (task (t.val+1)).U (Profile.firstOrder r).2.1) = 1 := by
    change Module.finrank K ↥((signal _ _).submodule ⊓ (signal _ _).submodule) = 1
    rw [← Space.submodule_meet]
    apply Space.finrank_eq
    simpa using pair_meet_card t r
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    ((task (t.val+1)).U (Profile.firstOrder r).1)
    ((task (t.val+1)).U (Profile.firstOrder r).2.1)
  rw [hinf,signal_rank,signal_rank] at hdim
  have htop : (task (t.val+1)).U (Profile.firstOrder r).1 ⊔
      (task (t.val+1)).U (Profile.firstOrder r).2.1 = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hv : Module.finrank K V = 3 := by simp [V]
    omega
  rw [htop, inf_top_eq, condRank, sup_eq_right.mpr ((task _).side_le_signal _),
    signal_rank]
  have hs : Module.finrank K ((task (t.val+1)).A (Profile.firstOrder r).2.2) = 1 :=
    side_rank _
  rw [hs]

theorem triple_cond (t : Fin 2) (i : Three) :
    condRank ((task (t.val+1)).U 0 ⊓ (task (t.val+1)).U 1 ⊓
      (task (t.val+1)).U 2) ((task (t.val+1)).A i) = 1-t.val := by
  change condRank ((signal _ _).submodule ⊓ (signal _ _).submodule ⊓
    (signal _ _).submodule) (side _).submodule = _
  rw [← Space.submodule_meet,← Space.submodule_meet]
  apply conditional_rank
  fin_cases t
  · exact (triple_card i).1
  · exact (triple_card i).2

theorem fork_cond (t : Fin 2) (i : Three) :
    condRank (((task (t.val+1)).U i ⊓ (task (t.val+1)).U (i+1)) ⊔
      ((task (t.val+1)).U i ⊓ (task (t.val+1)).U (i+2)))
      ((task (t.val+1)).A i) = 1 := by
  change condRank (((signal _ _).submodule ⊓ (signal _ _).submodule) ⊔
    ((signal _ _).submodule ⊓ (signal _ _).submodule)) (side _).submodule = _
  rw [← Space.submodule_meet,← Space.submodule_meet,← Space.submodule_join]
  apply conditional_rank
  exact fork_card t i

theorem total_demand (t : Fin 2) : Profile.totalDemand (task (t.val+1)) = 3 := by
  unfold Profile.totalDemand
  simp only [signal_rank]
  have hs (i : Three) : Module.finrank K ((task (t.val+1)).A i) = 1 := side_rank i
  simp [hs,Three,Fin.sum_univ_succ]

theorem first_entry (t : Fin 2) (r : Fin 6) :
    Profile.entry (task (t.val+1)) (.inl r) = 1 := by
  rw [Profile.entry,Profile.firstEntry,total_demand,first_cond,last_cond]
  norm_num

theorem second_entry (t : Fin 2) (i j : Three) :
    Profile.entry (task (t.val+1)) (.inr (i,j)) = 1 + (t.val : ℝ)/2 := by
  rw [Profile.entry,Profile.secondEntry,total_demand,triple_cond,fork_cond]
  have hj : condRank ((task (t.val+1)).U (i+1) ⊓
      ((task (t.val+1)).U i ⊔ (task (t.val+1)).U (i+2)))
      ((task (t.val+1)).A (i+1)) = 1 := by
    fin_cases i
    · exact last_cond t 1
    · exact last_cond t 2
    · exact last_cond t 5
  have hk : condRank ((task (t.val+1)).U (i+2) ⊓
      ((task (t.val+1)).U i ⊔ (task (t.val+1)).U (i+1)))
      ((task (t.val+1)).A (i+2)) = 1 := by
    fin_cases i
    · exact last_cond t 0
    · exact last_cond t 3
    · exact last_cond t 4
  rw [hj,hk]
  fin_cases t <;> norm_num

theorem rankBound_eq (t : Fin 2) :
    Profile.rankBound (task (t.val+1)) = 1 + (t.val : ℝ)/2 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro r _
    cases r with
    | inl r =>
      rw [first_entry]
      have h : (0 : ℝ) ≤ (t.val : ℝ) / 2 := by positivity
      linarith
    | inr r => rw [second_entry]
  · rw [← second_entry t 0 0]
    exact Profile.entry_le_rankBound _ _

/-- Operational optima over every nonlinear finite-alphabet zero-error block code. -/
theorem broadcastOptima : broadcastOptimum (task 1).A (task 1).U = 1 ∧
    broadcastOptimum (task 2).A (task 2).U = 3/2 := by
  constructor
  · rw [task_general_broadcastOptimum_eq_rankBound]
    simpa using rankBound_eq (0 : Fin 2)
  · rw [task_general_broadcastOptimum_eq_rankBound]
    have h := rankBound_eq (1 : Fin 2)
    norm_num at h ⊢
    exact h


end UploadBroadcast.CitedEntropyCounterexample
