import UploadBroadcast.NonzeroHyperplaneArithmetic
import UploadBroadcast.BinaryRelayProfiles

/-! Exact original-field hyperplane profiles for all seven codimension-one families. -/
namespace UploadBroadcast.NonzeroHyperplaneProfiles
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open Module Profile NonzeroDefectProfile NonzeroFamilyRanks NonzeroRelationRestrictions
open NonzeroDefectRelays BinaryRelayProfiles

variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

omit [FiniteDimensional K F] in
/-- The remote pair and the distinguished signal span the ambient space. -/
lemma remote_pair_join (T : UploadBroadcast.Task K F)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j = ⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k) = T.U i) :
    (T.U 1 ⊓ T.U 2) ⊔ T.U 0 = ⊤ := by
  have h1 : T.U 1 ≤ (T.U 1 ⊓ T.U 2) ⊔ T.U 0 := by
    calc
      T.U 1 = (T.U 1 ⊓ T.U 2) ⊔ (T.U 1 ⊓ T.U 0) :=
        (hi 1 2 0 (by decide) (by decide) (by decide)).symm
      _ ≤ (T.U 1 ⊓ T.U 2) ⊔ T.U 0 :=
        sup_le le_sup_left (inf_le_right.trans le_sup_right)
  apply top_unique
  rw [←hp 1 0 (by decide)]
  exact sup_le h1 le_sup_right

omit [FiniteDimensional K F] in
/-- Nonzeroness on the remote pair follows from the span identities and a
nonzero form killing the distinguished signal. -/
lemma remote_pair_nonzero (T : UploadBroadcast.Task K F) (l : F →ₗ[K] K)
    (hl : l ≠ 0) (hU : T.U 0 ≤ LinearMap.ker l)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j = ⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k) = T.U i) :
    ∃ v ∈ T.U 1 ⊓ T.U 2, l v ≠ 0 := by
  by_contra h
  push_neg at h
  have hr : T.U 1 ⊓ T.U 2 ≤ LinearMap.ker l := fun x hx => h x hx
  have ht : (⊤ : Submodule K F) ≤ LinearMap.ker l := by
    rw [←remote_pair_join T hp hi]
    exact sup_le hr hU
  exact hl (LinearMap.ker_eq_top.mp (top_unique ht))

omit [FiniteDimensional K F] in
/-- All original signal and pair-intersection span identities are preserved
by any arm permutation. -/
lemma reindex_spans (T : UploadBroadcast.Task K F) (p : Equiv.Perm Three)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j = ⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k) = T.U i) :
    (∀ i j, i ≠ j → (reindexTask p T).U i ⊔ (reindexTask p T).U j = ⊤) ∧
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ((reindexTask p T).U i ⊓ (reindexTask p T).U j) ⊔
      ((reindexTask p T).U i ⊓ (reindexTask p T).U k) = (reindexTask p T).U i) :=
  ⟨fun i j hij => hp (p i) (p j) (p.injective.ne hij),
   fun i j k hij hik hjk => hi (p i) (p j) (p k)
      (p.injective.ne hij) (p.injective.ne hik) (p.injective.ne hjk)⟩

/-- General-arm pair spans and exact second-entry preservation. -/
theorem hyperplane_spans_and_seconds (T : UploadBroadcast.Task K F)
    (p : Equiv.Perm Three) (l : F →ₗ[K] K) (hl : l ≠ 0)
    (hg : T.LocallyGenerated (LinearMap.ker l)) (hf : T.RelayFeasible (LinearMap.ker l))
    (hU : T.U (p 0) ≤ LinearMap.ker l)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j = ⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k) = T.U i) :
    (∀ i j, i ≠ j → (T.U i ⊓ LinearMap.ker l) ⊔
      (T.U j ⊓ LinearMap.ker l) = LinearMap.ker l) ∧
    (∀ i j k ell, i ≠ j → i ≠ k → j ≠ k →
      secondEntry (inducedTask T (LinearMap.ker l) hg) i j k ell = secondEntry T i j k ell) := by
  obtain ⟨hp',hi'⟩ := reindex_spans T p hp hi
  have hr := remote_pair_nonzero (reindexTask p T) l hl hU hp' hi'
  have hg' := (reindex_locallyGenerated T p _).mpr hg
  have hf' := (reindex_relayFeasible T p _).mpr hf
  have hpP := hyperplane_pair_spans (reindexTask p T) l hU hp' hr
  constructor
  · intro i j hij
    simpa only [reindexTask,p.apply_symm_apply] using
      hpP (p.symm i) (p.symm j) (p.symm.injective.ne hij)
  · intro i j k ell hij hik hjk
    have he := secondEntry_hyperplane (reindexTask p T) l hg' hf' hU hp' hi' hr
      (p.symm i) (p.symm j) (p.symm k) (p.symm ell)
      (p.symm.injective.ne hij) (p.symm.injective.ne hik) (p.symm.injective.ne hjk)
    rw [inducedTask_reindex,secondEntry_reindexTask,secondEntry_reindexTask] at he
    simpa only [p.apply_symm_apply] using he

/-- Exact remote conditional ranks determine the conditional rank for every
ordered pair after cutting by the actual hyperplane. -/
theorem all_cut_pair_ranks (T : UploadBroadcast.Task K F)
    (p : Equiv.Perm Three) (l : F →ₗ[K] K) (m : Three → ℕ)
    (hU : T.U (p 0) ≤ LinearMap.ker l)
    (hr1 : condRank ((T.U (p 1) ⊓ T.U (p 2)) ⊓ LinearMap.ker l)
      (T.A (p 1) ⊓ LinearMap.ker l) = min (m (p 1))
        (finrank K ↥(T.U (p 1) ⊓ T.U (p 2))-1))
    (hr2 : condRank ((T.U (p 1) ⊓ T.U (p 2)) ⊓ LinearMap.ker l)
      (T.A (p 2) ⊓ LinearMap.ker l) = min (m (p 2))
        (finrank K ↥(T.U (p 1) ⊓ T.U (p 2))-1))
    (i j : Three) (hij : i ≠ j) :
    condRank ((T.U i ⊓ T.U j) ⊓ LinearMap.ker l) (T.A j ⊓ LinearMap.ker l) =
      if i = p 0 ∨ j = p 0 then condRank (T.U i ⊓ T.U j) (T.A j)
      else min (m j) (finrank K ↥(T.U i ⊓ T.U j)-1) := by
  by_cases hs : i = p 0 ∨ j = p 0
  · rw [if_pos hs]
    apply condRank_unchanged_of_le
    rcases hs with rfl | rfl
    · exact inf_le_left.trans hU
    · exact inf_le_right.trans hU
  · rw [if_neg hs]
    obtain ⟨i,rfl⟩ := p.surjective i
    obtain ⟨j,rfl⟩ := p.surjective j
    have hi : i ≠ 0 := fun hh => hs (Or.inl (congrArg p hh))
    have hj : j ≠ 0 := fun hh => hs (Or.inr (congrArg p hh))
    have hij' : i ≠ j := fun hh => hij (congrArg p hh)
    fin_cases i <;> fin_cases j
    all_goals first
      | exact False.elim (hi rfl)
      | exact False.elim (hj rfl)
      | exact False.elim (hij' rfl)
      | exact hr2
      | skip
    change condRank ((T.U (p 2) ⊓ T.U (p 1)) ⊓ LinearMap.ker l)
      (T.A (p 1) ⊓ LinearMap.ker l) =
        min (m (p 1)) (finrank K ↥(T.U (p 2) ⊓ T.U (p 1))-1)
    have hrank : finrank K ↥(T.U (p 2) ⊓ T.U (p 1)) =
        finrank K ↥(T.U (p 1) ⊓ T.U (p 2)) :=
      congrArg (fun S : Submodule K F => finrank K S) (inf_comm _ _)
    rw [hrank]
    simpa only [inf_comm (T.U (p 2)) (T.U (p 1))] using hr1

/-- All fifteen exact profile entries of the actual hyperplane kernel. -/
theorem full_hyperplane_profile (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (hgne : g ≠ .R2) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n)
    (p : Equiv.Perm Three) (hp : p 0 = hyperplaneArm g) (l : F →ₗ[K] K)
    (hU : T.U (p 0) ≤ LinearMap.ker l)
    (hg : T.LocallyGenerated (LinearMap.ker l)) (hf : T.RelayFeasible (LinearMap.ker l))
    (hdim : finrank K (LinearMap.ker l) + 1 = finrank K F)
    (hr1 : condRank ((T.U (p 1) ⊓ T.U (p 2)) ⊓ LinearMap.ker l)
      (T.A (p 1) ⊓ LinearMap.ker l) =
        min (fullSignal g n (p 1)-fullSide g n (p 1))
          (finrank K ↥(T.U (p 1) ⊓ T.U (p 2))-1))
    (hr2 : condRank ((T.U (p 1) ⊓ T.U (p 2)) ⊓ LinearMap.ker l)
      (T.A (p 2) ⊓ LinearMap.ker l) =
        min (fullSignal g n (p 2)-fullSide g n (p 2))
          (finrank K ↥(T.U (p 1) ⊓ T.U (p 2))-1)) :
    (∀ r : Fin 6, entry (inducedTask T (LinearMap.ker l) hg) (.inl r) =
      (fullFirst g n r : ℝ) + (firstIncrement g r : ℝ)) ∧
    (∀ i ell : Three, 2 * entry (inducedTask T (LinearMap.ker l) hg) (.inr (i,ell)) =
      (doubledSecond g n : ℝ)) := by
  have hl : l ≠ 0 := by
    intro hz
    have hk : LinearMap.ker l = ⊤ := LinearMap.ker_eq_top.mpr hz
    have hdimker : finrank K (LinearMap.ker l) = finrank K F := by rw [hk,finrank_top]
    omega
  have hc := full_rankConditions T hT g n hn h
  obtain ⟨hpP,hseconds⟩ := hyperplane_spans_and_seconds T p l hl hg hf hU
    hc.pair_span hc.pair_intersections_span
  have hcuts := all_cut_pair_ranks T p l (fun j => fullSignal g n j-fullSide g n j) hU hr1 hr2
  constructor
  · intro r
    let i := (firstOrder r).1
    let j := (firstOrder r).2.1
    let k := (firstOrder r).2.2
    have hij : i ≠ j := by fin_cases r <;> decide
    have hbase : firstEntry T i j k = (fullFirst g n r : ℝ) := full_first_profile T hT g n hn h r
    have hdiff := firstEntry_difference T (LinearMap.ker l) hg hf i j k
      (hc.pair_span i j hij) (hpP i j hij)
    have hpair := hc.pair_rank i j hij
    simp only [finrank_top,h.ambient] at hpair
    have hd := full_signal_pair_dimension T hT g n hn h i j hij
    rw [h.ambient] at hd
    have hpd : finrank K ↥(T.U i ⊓ T.U j) =
        fullSignal g n i+fullSignal g n j-fullAmbient g n := by omega
    rw [hcuts i j hij] at hdiff
    simp only [hpair,hpd,hp,hbase] at hdiff
    have hinc := incrementFormula_eq g hgne n hn r
    change (if i = hyperplaneArm g ∨ j = hyperplaneArm g then 0 else
      min (fullSignal g n j-fullSide g n j) (fullSignal g n i+fullSignal g n j-fullAmbient g n) -
      min (fullSignal g n j-fullSide g n j) (fullSignal g n i+fullSignal g n j-fullAmbient g n-1)) =
        firstIncrement g r at hinc
    change firstEntry (inducedTask T (LinearMap.ker l) hg) i j k = _
    by_cases hs : i = hyperplaneArm g ∨ j = hyperplaneArm g
    · rw [if_pos hs] at hdiff hinc
      rw [←hinc]
      simp only [Nat.cast_zero,add_zero]
      linarith
    · rw [if_neg hs] at hdiff hinc
      have hm : min (fullSignal g n j-fullSide g n j)
          (fullSignal g n i+fullSignal g n j-fullAmbient g n-1) ≤
        min (fullSignal g n j-fullSide g n j)
          (fullSignal g n i+fullSignal g n j-fullAmbient g n) :=
        min_le_min le_rfl (Nat.sub_le _ _)
      have hcast := congrArg (fun a : ℕ => (a : ℝ)) hinc
      dsimp only at hcast
      rw [Nat.cast_sub hm] at hcast
      linarith
  · intro i ell
    change 2 * secondEntry (inducedTask T (LinearMap.ker l) hg) i (i+1) (i+2) ell = _
    rw [hseconds i (i+1) (i+2) ell
      (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact full_second_profile T hT g n hn h i ell

/-- The seven hyperplane cases of `lem:same-chart`, over the original finite
field. All profile entries, local generation and feasibility are conclusions. -/
theorem exists_full_hyperplane_profile [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (hgne : g ≠ .R2) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P = fullAmbient g n-1 ∧
      (∀ r : Fin 6, entry (inducedTask T P hg) (.inl r) =
        (fullFirst g n r : ℝ) + (firstIncrement g r : ℝ)) ∧
      (∀ i ell : Three, 2 * entry (inducedTask T P hg) (.inr (i,ell)) =
        (doubledSecond g n : ℝ)) := by
  let p : Equiv.Perm Three := Equiv.swap 0 (hyperplaneArm g)
  have hp : p 0 = hyperplaneArm g := by simp [p]
  obtain ⟨l,hU,hg,hf,hdim,hr1,hr2⟩ := exists_full_hyperplane_with_remote_ranks
    hq T hT g hgne n hn h p hp
  have hprofile := full_hyperplane_profile T hT g hgne n hn h p hp l hU hg hf hdim hr1 hr2
  exact ⟨LinearMap.ker l,hg,hf,by rw [h.ambient] at hdim; omega,hprofile⟩

end UploadBroadcast.NonzeroHyperplaneProfiles
