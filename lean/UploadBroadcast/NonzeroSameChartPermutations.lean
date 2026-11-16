import UploadBroadcast.NonzeroSameChartMenus

/-! The six actual user relabelings of every nonzero-defect menu, including
the indexed T₁ and O rows. Optimality is for the original, unreindexed task. -/
namespace UploadBroadcast.NonzeroSameChartPermutations
open Module Profile NonzeroDefectProfile NonzeroFamilyRanks NonzeroDefectRelays
open NonzeroSameChartMenus R2PermutedMenus
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
/-- The six displayed paths exhaust every permutation of the three users. -/
theorem pathPerm_exhaustive : Function.Surjective pathPerm := by decide

/-- Representatives for the three enlarged-signal T₁ rows in Table menus. -/
def indexedT1Permutation : Three → Fin 6 := ![1,3,4]
/-- Representatives for the three enlarged-side O rows in Table menus. -/
def indexedOPermutation : Three → Fin 6 := ![4,0,1]

def sourceT1Menu : Three → Three → Fin 6 → ℕ :=
  ![fun c => if c=0 then ![0,0,0,0,1,0] else ![0,0,1,0,0,0],
    fun c => if c=0 then ![0,0,0,0,0,1] else ![1,0,0,0,0,0],
    fun c => if c=0 then ![0,1,0,0,0,0] else ![0,0,0,1,0,0]]

def sourceOMenu : Three → Three → Fin 6 → ℕ :=
  ![![![1,0,0,0,0,0],![0,1,0,0,0,0],![0,0,0,1,0,1]],
    ![![0,0,0,1,0,0],![0,0,1,0,0,0],![0,1,0,0,1,0]],
    ![![0,0,0,0,0,1],![0,0,0,0,1,0],![1,0,1,0,0,0]]]

/-- The representatives really place the enlarged arm at the indicated user. -/
theorem indexed_arms (i : Three) :
    pathPerm (indexedT1Permutation i) 0 = i ∧
    pathPerm (indexedOPermutation i) 2 = i := by
  fin_cases i <;> decide

/-- Exact indexed increments from Table menus; choice order is immaterial.
The duplicated T₁ choice keeps the uniform three-choice interface. -/
theorem indexed_menu_table (i choice : Three) (r : Fin 6) :
    menuIncrement .T1 choice (inverseFirst (indexedT1Permutation i) r) = sourceT1Menu i choice r ∧
    menuIncrement .O choice (inverseFirst (indexedOPermutation i) r) = sourceOMenu i choice r := by
  fin_cases i <;> fin_cases choice <;> fin_cases r <;> decide

variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Family lower bound when the dimension table is specified in any arm order. -/
theorem family_code_lower_permuted [Finite K] {L : ℕ} {m : Three → ℕ} {s : ℕ}
    (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (p : Equiv.Perm Three) (g : Family) (n : ℕ) (hn : 1 ≤ n)
    (h : Dimensions (reindexTask p T) g n)
    (c : T.Code L (fun i => Fin (m i)) (Fin s)) (hL : 0 < L) :
    ((fullAmbient g n-codimension g : ℕ) : ℝ) ≤ c.uploadCost := by
  have hT' := TaskUserPermutation.reindex_indecomposable T p hT
  have hc := full_rankConditions (reindexTask p T) hT' g n hn h
  have hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j = ⊤ := by
    intro i j hij
    simpa only [reindexTask,p.apply_symm_apply] using
      hc.pair_span (p.symm i) (p.symm j) (p.symm.injective.ne hij)
  have hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k) = T.U i := by
    intro i j k hij hik hjk
    simpa only [reindexTask,p.apply_symm_apply] using
      hc.pair_intersections_span (p.symm i) (p.symm j) (p.symm k)
        (p.symm.injective.ne hij) (p.symm.injective.ne hik) (p.symm.injective.ne hjk)
  have hd (i j : Three) (hij : i ≠ j) : Disjoint (T.A i) (T.A j) := by
    apply disjoint_iff.mpr
    simpa only [reindexTask,p.apply_symm_apply] using
      full_side_pair_eq_bot (reindexTask p T) hT' g n hn h (p.symm i) (p.symm j)
        (p.symm.injective.ne hij)
  have hspan : T.Spanning := by
    apply top_unique
    rw [←hp 0 1 (by decide)]
    exact sup_le (T.feasible 0) (T.feasible 1)
  have ha : T.A 0 ⊔ T.A 1 ⊔ T.A 2 = ⊤ := by
    simpa only [Task.Spanning,Profile.three_iSup] using hspan
  have hj : T.U 2 ⊔ (T.U 0 ⊓ T.U 1) = ⊤ := by
    have hu : T.U 0 ≤ T.U 2 ⊔ (T.U 0 ⊓ T.U 1) := by
      calc
        T.U 0 = (T.U 0 ⊓ T.U 1) ⊔ (T.U 0 ⊓ T.U 2) := (hi 0 1 2 (by decide) (by decide) (by decide)).symm
        _ ≤ T.U 2 ⊔ (T.U 0 ⊓ T.U 1) := sup_le le_sup_right (inf_le_right.trans le_sup_left)
    apply top_unique
    rw [←hp 2 0 (by decide)]
    exact sup_le le_sup_left hu
  have hh := GeometricUploadConverse.code_lower T (hd 0 1 (by decide))
    (hd 0 2 (by decide)) (hd 1 2 (by decide)) ha hp hj c hL
  have hsum : (∑ i,finrank K (T.A i)) = ∑ i,fullSide g n i := by
    rw [←Equiv.sum_comp p (fun i => finrank K (T.A i))]
    apply Finset.sum_congr rfl
    intro i _
    exact h.side i
  have hsumR : (finrank K (T.A 0) : ℝ)+finrank K (T.A 1)+finrank K (T.A 2) =
      (fullSide g n 0 : ℝ)+fullSide g n 1+fullSide g n 2 := by
    exact_mod_cast (show finrank K (T.A 0)+finrank K (T.A 1)+finrank K (T.A 2) =
      fullSide g n 0+fullSide g n 1+fullSide g n 2 from by simpa only [Fin.sum_univ_three] using hsum)
  rw [h.ambient,hsumR,←NonzeroSameChartOptimality.family_converse_arithmetic g n hn] at hh
  exact hh

/-- Arbitrary actual arm order preserves the equality between relay rank
and U*. No operational permutation-invariance assumption is needed. -/
theorem relay_rank_eq_uploadOptimum_permuted [Finite K]
    (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (p : Equiv.Perm Three) (g : Family) (n : ℕ) (hn : 1 ≤ n)
    (h : Dimensions (reindexTask p T) g n)
    (P : Submodule K F) (hg : T.LocallyGenerated P) (hf : T.RelayFeasible P)
    (hd : finrank K P = fullAmbient g n-codimension g) :
    (finrank K P : ℝ) = T.uploadOptimum := by
  obtain ⟨owner,c,hc⟩ := ResidualOperational.finiteCode_of_local_relay T P hg hf
  letI := c.finite_upload
  letI := c.finite_broadcast
  symm
  apply Task.uploadOptimum_eq_of_code c.toCode (by decide) _ hc
  intro L m s d hL
  rw [hd]
  exact family_code_lower_permuted T hT p g n hn h d hL

/-- Source `lem:same-chart`, including every indexed-arm choice and all six
arm permutations, over the original field, with operational upload optimality. -/
theorem same_chart_all_permuted_choices [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (k : Fin 6) (g : Family) (n : ℕ) (hn : 1 ≤ n)
    (h : Dimensions (reindexTask (pathPerm k) T) g n) (choice : Three) :
    (∀ r : Fin 6, entry T (.inl r) = (fullFirst g n (inverseFirst k r) : ℝ)) ∧
    (∀ i ell : Three, 2 * entry T (.inr (i,ell)) = (doubledSecond g n : ℝ)) ∧
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P = fullAmbient g n-codimension g ∧
      (finrank K P : ℝ) = T.uploadOptimum ∧
      (∑ i, finrank K ↥(P ⊓ T.A i)) = finrank K P ∧
      (∀ r : Fin 6, entry (inducedTask T P hg) (.inl r) =
        (fullFirst g n (inverseFirst k r) : ℝ) + (menuIncrement g choice (inverseFirst k r) : ℝ)) ∧
      (∀ i ell : Three, 2 * entry (inducedTask T P hg) (.inr (i,ell)) =
        (doubledSecond g n : ℝ)) := by
  let p := pathPerm k
  have hT' := TaskUserPermutation.reindex_indecomposable T p hT
  have hfull₁ := full_first_profile (reindexTask p T) hT' g n hn h
  have hfull₂ := full_second_profile (reindexTask p T) hT' g n hn h
  obtain ⟨P,hg,hf,hd,_,hu,hfirst,hsecond⟩ := same_chart_all_menu_choices hq (reindexTask p T) hT' g n hn h choice
  have hg' : T.LocallyGenerated P := (reindex_locallyGenerated T p P).mp hg
  have hf' : T.RelayFeasible P := (reindex_relayFeasible T p P).mp hf
  have he : inducedTask (reindexTask p T) P hg = reindexTask p (inducedTask T P hg') := rfl
  refine ⟨?_,?_,P,hg',hf',hd,relay_rank_eq_uploadOptimum_permuted T hT p g n hn h P hg' hf' hd,?_,?_,?_⟩
  · intro r
    simpa only [p,firstEntry_path_reindex] using hfull₁ (inverseFirst k r)
  · intro i ell
    simpa only [p,secondEntry_path_reindex] using hfull₂ (inverseUser k i) (inverseUser k ell)
  · change (∑ i, finrank K ↥(P ⊓ T.A (p i))) = finrank K P at hu
    exact (Equiv.sum_comp p (fun i => finrank K ↥(P ⊓ T.A i))).symm.trans hu
  · intro r
    have hh := hfirst (inverseFirst k r)
    rw [he] at hh
    simpa only [p,firstEntry_path_reindex] using hh
  · intro i ell
    have hh := hsecond (inverseUser k i) (inverseUser k ell)
    rw [he] at hh
    simpa only [p,secondEntry_path_reindex] using hh

/-- The other six nonzero-defect families preserve the entire fifteen-entry
profile, in every actual arm order, at the operational upload minimum. -/
theorem other_families_profile_preserving [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (k : Fin 6) (g : Family) (hT1 : g ≠ .T1) (hO : g ≠ .O)
    (n : ℕ) (hn : 1 ≤ n) (h : Dimensions (reindexTask (pathPerm k) T) g n) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P = fullAmbient g n-codimension g ∧
      (finrank K P : ℝ) = T.uploadOptimum ∧
      ∀ r : Profile.Index, entry (inducedTask T P hg) r = entry T r := by
  obtain ⟨hfull₁,hfull₂,P,hg,hf,hd,ho,_,hfirst,hsecond⟩ :=
    same_chart_all_permuted_choices hq T hT k g n hn h 0
  refine ⟨P,hg,hf,hd,ho,?_⟩
  intro r
  cases r with
  | inl r =>
    rw [hfirst,hfull₁]
    have hz' (j : Fin 6) : menuIncrement g 0 j = 0 := by
      cases g <;> try contradiction
      all_goals fin_cases j <;> rfl
    have hz := hz' (inverseFirst k r)
    simp only [hz,Nat.cast_zero,add_zero]
  | inr r =>
    obtain ⟨i,ell⟩ := r
    have h₁ := hsecond i ell
    have h₂ := hfull₂ i ell
    linarith

end UploadBroadcast.NonzeroSameChartPermutations
