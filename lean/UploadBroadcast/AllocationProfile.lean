import UploadBroadcast.AllocationNat
import UploadBroadcast.Profile
set_option maxHeartbeats 500000

namespace UploadBroadcast.Allocation

noncomputable def reducedWaterValue (r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ : ℝ) : ℝ :=
  min (b₁+u₁-r) (min (b₂+u₂-r) (min (b₃+u₃-r)
    (min ((b₂+b₃+p₁-r)/2) (min ((b₁+b₃+p₂-r)/2) ((b₁+b₂+p₃-r)/2)))))

theorem waterfillValue_reduce {r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ : ℝ}
    (h : RankBounds r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃) :
    waterfillValue (u₁-r) (u₂-r) (u₃-r) (p₁-r) (p₂-r) (p₃-r) b₁ b₂ b₃ =
    reducedWaterValue r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ := by
  rcases h with ⟨_,_,_,_,h21,h31,h12,h32,h13,h23,_,_,_⟩
  apply le_antisymm
  · generalize hw : waterfillValue (u₁-r) (u₂-r) (u₃-r) (p₁-r) (p₂-r) (p₃-r) b₁ b₂ b₃ = w
    have h := le_of_eq hw.symm
    unfold waterfillValue pairLevel at h
    simp only [le_min_iff] at h
    unfold reducedWaterValue
    simp only [le_min_iff]
    rcases h with ⟨h1,h2,h3,⟨h4,h5,h6⟩,⟨h7,h8,h9⟩,h10,h11,h12⟩
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
  · generalize hw : reducedWaterValue r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ = w
    have h := le_of_eq hw.symm
    unfold reducedWaterValue at h
    simp only [le_min_iff] at h
    rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
    unfold waterfillValue pairLevel
    simp only [le_min_iff]
    refine ⟨?_,?_,?_,⟨?_,?_,?_⟩,⟨?_,?_,?_⟩,?_,?_,?_⟩ <;> linarith


theorem reduced_cost_expand (r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ m : ℝ) :
    m-r-reducedWaterValue r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ =
    max (m-b₁-u₁) (max (m-b₂-u₂) (max (m-b₃-u₃)
      (max (m-(r+p₁+b₂+b₃)/2) (max (m-(r+p₂+b₁+b₃)/2) (m-(r+p₃+b₁+b₂)/2))))) := by
  simp only [reducedWaterValue, ← max_sub_sub_left]
  ring_nf

variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

theorem task_totalDemand (T : Task K F) :
    (Profile.totalDemand T : ℝ) =
      (demandRank T.A T.U 0 : ℝ)+demandRank T.A T.U 1+demandRank T.A T.U 2 := by
  simp only [Profile.totalDemand, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Nat.cast_add, demandRank_eq_finrank_sub T.A T.U _ (T.side_le_signal _)]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring

theorem rankBound_expand (T : Task K F) :
    Profile.rankBound T = max (Profile.entry T (.inl 0)) (max (Profile.entry T (.inl 1)) (max (Profile.entry T (.inl 2)) (max (Profile.entry T (.inl 3)) (max (Profile.entry T (.inl 4)) (max (Profile.entry T (.inl 5)) (max (Profile.entry T (.inr (0,0))) (max (Profile.entry T (.inr (0,1))) (max (Profile.entry T (.inr (0,2))) (max (Profile.entry T (.inr (1,0))) (max (Profile.entry T (.inr (1,1))) (max (Profile.entry T (.inr (1,2))) (max (Profile.entry T (.inr (2,0))) (max (Profile.entry T (.inr (2,1))) (Profile.entry T (.inr (2,2)))))))))))))))) := by
  unfold Profile.rankBound
  generalize Profile.entry T = f
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    rcases i with i | ⟨i,j⟩
    · fin_cases i <;> (repeat first | exact le_refl _ | exact le_max_left _ _ | apply le_trans ?_ (le_max_right _ _))
    · fin_cases i <;> fin_cases j <;> (repeat first | exact le_refl _ | exact le_max_left _ _ | apply le_trans ?_ (le_max_right _ _))
  · simp only [max_le_iff]
    exact ⟨Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _)⟩


/-- The numerical LCBC LP is exactly the maximum of the fifteen actual
conditional-rank profile entries. No operational capacity theorem is used. -/
theorem actualNumericLP_eq_rankBound (T : Task K F) :
    actualNumericLP T.A T.U = Profile.rankBound T := by
  unfold actualNumericLP lcbcCostValue
  rw [waterfillValue_reduce (actual_rank_bounds T.A T.U), reduced_cost_expand]
  rw [rankBound_expand]
  simp only [Profile.entry,
    (show Profile.firstOrder 0 = (0,1,2) from rfl),
    (show Profile.firstOrder 1 = (0,2,1) from rfl),
    (show Profile.firstOrder 2 = (1,0,2) from rfl),
    (show Profile.firstOrder 3 = (1,2,0) from rfl),
    (show Profile.firstOrder 4 = (2,0,1) from rfl),
    (show Profile.firstOrder 5 = (2,1,0) from rfl),
    Profile.firstEntry, Profile.secondEntry,
    task_totalDemand, commonRank, pairRank, pairSumRank, enlargedRank,
    Nat.cast_min, min_add, add_min, ← min_div_div_right (show (0:ℝ) ≤ 2 by norm_num),
    ← max_sub_sub_left]
  norm_num only [Fin.reduceAdd, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ, Matrix.head_cons]
  simp only [(show (3 : Three) = 0 from rfl), (show (4 : Three) = 1 from rfl)]
  try simp only [sup_comm (T.U 1 ⊓ T.U 2) (T.U 1 ⊓ T.U 0)]
  try simp only [inf_comm (T.U 1) (T.U 0), inf_comm (T.U 2) (T.U 0),
    inf_comm (T.U 2) (T.U 1), sup_comm (T.U 1) (T.U 0),
    sup_comm (T.U 2) (T.U 0), sup_comm (T.U 2) (T.U 1)]
  generalize (demandRank T.A T.U 0 : ℝ) = d0
  generalize (demandRank T.A T.U 1 : ℝ) = d1
  generalize (demandRank T.A T.U 2 : ℝ) = d2
  generalize (condRank (T.U 0 ⊓ T.U 1) (T.A 0) : ℝ) = c010
  generalize (condRank (T.U 0 ⊓ T.U 1) (T.A 1) : ℝ) = c011
  generalize (condRank (T.U 0 ⊓ T.U 2) (T.A 0) : ℝ) = c020
  generalize (condRank (T.U 0 ⊓ T.U 2) (T.A 2) : ℝ) = c022
  generalize (condRank (T.U 1 ⊓ T.U 2) (T.A 1) : ℝ) = c121
  generalize (condRank (T.U 1 ⊓ T.U 2) (T.A 2) : ℝ) = c122
  generalize (condRank (T.U 0 ⊓ (T.U 1 ⊔ T.U 2)) (T.A 0) : ℝ) = b0
  generalize (condRank (T.U 1 ⊓ (T.U 0 ⊔ T.U 2)) (T.A 1) : ℝ) = b1
  generalize (condRank (T.U 2 ⊓ (T.U 0 ⊔ T.U 1)) (T.A 2) : ℝ) = b2
  generalize (condRank ((T.U 0 ⊓ T.U 1) ⊔ (T.U 0 ⊓ T.U 2)) (T.A 0) : ℝ) = p0
  generalize (condRank ((T.U 0 ⊓ T.U 1) ⊔ (T.U 1 ⊓ T.U 2)) (T.A 1) : ℝ) = p1
  generalize (condRank ((T.U 0 ⊓ T.U 2) ⊔ (T.U 1 ⊓ T.U 2)) (T.A 2) : ℝ) = p2
  generalize (condRank (T.U 0 ⊓ T.U 1 ⊓ T.U 2) (T.A 0) : ℝ) = r0
  generalize (condRank (T.U 0 ⊓ T.U 1 ⊓ T.U 2) (T.A 1) : ℝ) = r1
  generalize (condRank (T.U 0 ⊓ T.U 1 ⊓ T.U 2) (T.A 2) : ℝ) = r2
  ring_nf
  ac_rfl

/-- The fifteen-entry formula on raw side-information and signal subspaces.
This definition does not impose upload feasibility, or even Aᵢ ≤ Uᵢ. -/
noncomputable def rawFirstEntry (A U : Fin 3 → Submodule K F) (i j k : Three) : ℝ :=
  (demandRank A U 0 : ℝ)+demandRank A U 1+demandRank A U 2 -
    condRank (U i ⊓ U j) (A j) - condRank (U k ⊓ (U i ⊔ U j)) (A k)

noncomputable def rawSecondEntry (A U : Fin 3 → Submodule K F) (i j k ell : Three) : ℝ :=
  (demandRank A U 0 : ℝ)+demandRank A U 1+demandRank A U 2 -
    ((condRank (U 0 ⊓ U 1 ⊓ U 2) (A ell) : ℝ) +
      condRank ((U i ⊓ U j) ⊔ (U i ⊓ U k)) (A i) +
      condRank (U j ⊓ (U i ⊔ U k)) (A j) +
      condRank (U k ⊓ (U i ⊔ U j)) (A k)) / 2

noncomputable def rawEntry (A U : Fin 3 → Submodule K F) : Profile.Index → ℝ
  | .inl r => rawFirstEntry A U (Profile.firstOrder r).1 (Profile.firstOrder r).2.1
      (Profile.firstOrder r).2.2
  | .inr (i,ell) => rawSecondEntry A U i (i+1) (i+2) ell

noncomputable def rawRankBound (A U : Fin 3 → Submodule K F) : ℝ :=
  Finset.univ.sup' (by simp) (rawEntry A U)

theorem rawRankBound_expand (A U : Fin 3 → Submodule K F) :
    rawRankBound A U = max (rawEntry A U (.inl 0)) (max (rawEntry A U (.inl 1)) (max (rawEntry A U (.inl 2)) (max (rawEntry A U (.inl 3)) (max (rawEntry A U (.inl 4)) (max (rawEntry A U (.inl 5)) (max (rawEntry A U (.inr (0,0))) (max (rawEntry A U (.inr (0,1))) (max (rawEntry A U (.inr (0,2))) (max (rawEntry A U (.inr (1,0))) (max (rawEntry A U (.inr (1,1))) (max (rawEntry A U (.inr (1,2))) (max (rawEntry A U (.inr (2,0))) (max (rawEntry A U (.inr (2,1))) (rawEntry A U (.inr (2,2)))))))))))))))) := by
  unfold rawRankBound
  generalize rawEntry A U = f
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    rcases i with i | ⟨i,j⟩
    · fin_cases i <;> (repeat first | exact le_refl _ | exact le_max_left _ _ | apply le_trans ?_ (le_max_right _ _))
    · fin_cases i <;> fin_cases j <;> (repeat first | exact le_refl _ | exact le_max_left _ _ | apply le_trans ?_ (le_max_right _ _))
  · simp only [max_le_iff]
    exact ⟨Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _),Finset.le_sup' f (Finset.mem_univ _)⟩



theorem actualNumericLP_eq_rawRankBound (A U : Fin 3 → Submodule K F) :
    actualNumericLP A U = rawRankBound A U := by
  unfold actualNumericLP lcbcCostValue
  rw [waterfillValue_reduce (actual_rank_bounds A U), reduced_cost_expand]
  rw [rawRankBound_expand]
  simp only [rawEntry,
    (show Profile.firstOrder 0 = (0,1,2) from rfl),
    (show Profile.firstOrder 1 = (0,2,1) from rfl),
    (show Profile.firstOrder 2 = (1,0,2) from rfl),
    (show Profile.firstOrder 3 = (1,2,0) from rfl),
    (show Profile.firstOrder 4 = (2,0,1) from rfl),
    (show Profile.firstOrder 5 = (2,1,0) from rfl),
    rawFirstEntry, rawSecondEntry,
    commonRank, pairRank, pairSumRank, enlargedRank,
    Nat.cast_min, min_add, add_min, ← min_div_div_right (show (0:ℝ) ≤ 2 by norm_num),
    ← max_sub_sub_left]
  norm_num only [Fin.reduceAdd, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ, Matrix.head_cons]
  simp only [(show (3 : Three) = 0 from rfl), (show (4 : Three) = 1 from rfl)]
  try simp only [sup_comm (U 1 ⊓ U 2) (U 1 ⊓ U 0)]
  try simp only [inf_comm (U 1) (U 0), inf_comm (U 2) (U 0),
    inf_comm (U 2) (U 1), sup_comm (U 1) (U 0),
    sup_comm (U 2) (U 0), sup_comm (U 2) (U 1)]
  generalize (demandRank A U 0 : ℝ) = d0
  generalize (demandRank A U 1 : ℝ) = d1
  generalize (demandRank A U 2 : ℝ) = d2
  generalize (condRank (U 0 ⊓ U 1) (A 0) : ℝ) = c010
  generalize (condRank (U 0 ⊓ U 1) (A 1) : ℝ) = c011
  generalize (condRank (U 0 ⊓ U 2) (A 0) : ℝ) = c020
  generalize (condRank (U 0 ⊓ U 2) (A 2) : ℝ) = c022
  generalize (condRank (U 1 ⊓ U 2) (A 1) : ℝ) = c121
  generalize (condRank (U 1 ⊓ U 2) (A 2) : ℝ) = c122
  generalize (condRank (U 0 ⊓ (U 1 ⊔ U 2)) (A 0) : ℝ) = b0
  generalize (condRank (U 1 ⊓ (U 0 ⊔ U 2)) (A 1) : ℝ) = b1
  generalize (condRank (U 2 ⊓ (U 0 ⊔ U 1)) (A 2) : ℝ) = b2
  generalize (condRank ((U 0 ⊓ U 1) ⊔ (U 0 ⊓ U 2)) (A 0) : ℝ) = p0
  generalize (condRank ((U 0 ⊓ U 1) ⊔ (U 1 ⊓ U 2)) (A 1) : ℝ) = p1
  generalize (condRank ((U 0 ⊓ U 2) ⊔ (U 1 ⊓ U 2)) (A 2) : ℝ) = p2
  generalize (condRank (U 0 ⊓ U 1 ⊓ U 2) (A 0) : ℝ) = r0
  generalize (condRank (U 0 ⊓ U 1 ⊓ U 2) (A 1) : ℝ) = r1
  generalize (condRank (U 0 ⊓ U 1 ⊓ U 2) (A 2) : ℝ) = r2
  ring_nf
  ac_rfl


/-- Raw-subspace and task rank formulas agree on every task. -/
theorem rawRankBound_eq_rankBound (T : Task K F) :
    rawRankBound T.A T.U = Profile.rankBound T :=
  (actualNumericLP_eq_rawRankBound T.A T.U).symm.trans (actualNumericLP_eq_rankBound T)

/-- The general scalar construction can use the exact fifteen-entry ceiling,
without any upload-feasibility assumption. -/
theorem actual_nat_profile_allocation (A U : Fin 3 → Submodule K F) :
    ∃ s : ScalarAllocation A U,
      s.r = commonRank A U ∧ (s.length : ℤ) = ⌈rawRankBound A U⌉ := by
  simpa only [actualNumericLP_eq_rawRankBound] using actual_nat_lcbc_allocation A U

end UploadBroadcast.Allocation
