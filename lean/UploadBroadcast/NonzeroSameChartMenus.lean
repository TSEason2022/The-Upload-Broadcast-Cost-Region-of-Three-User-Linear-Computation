import UploadBroadcast.NonzeroSameChartOptimality
import UploadBroadcast.R2PermutedMenus

/-! Every indexed-arm choice appearing in the nonzero-defect same-chart
lemma, including both T₁ and all three O choices, with exact profiles. -/
namespace UploadBroadcast.NonzeroSameChartMenus
open Module Profile NonzeroDefectProfile NonzeroFamilyRanks NonzeroDefectRelays
open NonzeroRelationRestrictions NonzeroHyperplaneProfiles BinaryRelayProfiles
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

/-- The canonical distinguished-arm choices. Repeated choices in the other
six families are harmless and keep one uniform index type. -/
def menuArm (g : Family) (choice : Three) : Three :=
  match g with
  | .T1 => if choice = 0 then 1 else 2
  | .O => choice
  | _ => hyperplaneArm g

/-- Exact increments in the manuscript's six-entry order. -/
def menuIncrement (g : Family) (choice : Three) : Fin 6 → ℕ :=
  match g with
  | .T1 => if choice = 0 then ![0,0,0,0,1,0] else ![0,0,1,0,0,0]
  | .O => ![![0,0,0,0,0,1],![0,0,0,0,1,0],![1,0,1,0,0,0]] choice
  | _ => ![0,0,0,0,0,0]

theorem menu_geometry (g : Family) (hg : g ≠ .R2) (choice : Three) (n : ℕ) (hn : 1 ≤ n) :
    fullSide g n 0+fullSide g n 1+fullSide g n 2+fullSignal g n (menuArm g choice) ≤ 2*fullAmbient g n ∧
    fullSignal g n (menuArm g choice) < fullAmbient g n := by
  by_cases hT : g = .T1
  · subst g
    fin_cases choice <;> simp [menuArm,fullSide,fullSignal,fullAmbient] <;> omega
  by_cases hO : g = .O
  · subst g
    fin_cases choice <;> simp [menuArm,fullSide,fullSignal,fullAmbient] <;> omega
  have he : menuArm g choice = hyperplaneArm g := by cases g <;> simp_all [menuArm]
  rw [he]
  exact ⟨hyperplane_euler_bound g hg n hn,hyperplane_signal_lt g hg n hn⟩

theorem menu_increment_arithmetic (g : Family) (hg : g ≠ .R2) (choice : Three)
    (n : ℕ) (hn : 1 ≤ n) (r : Fin 6) :
    let i := (firstOrder r).1
    let j := (firstOrder r).2.1
    (if i = menuArm g choice ∨ j = menuArm g choice then 0 else
      min (fullSignal g n j-fullSide g n j) (fullSignal g n i+fullSignal g n j-fullAmbient g n) -
      min (fullSignal g n j-fullSide g n j) (fullSignal g n i+fullSignal g n j-fullAmbient g n-1)) =
      menuIncrement g choice r := by
  by_cases hT : g = .T1
  · subst g
    fin_cases choice <;> fin_cases r <;>
      simp [menuArm,menuIncrement,fullSignal,fullSide,fullAmbient,firstOrder] <;> omega
  by_cases hO : g = .O
  · subst g
    fin_cases choice <;> fin_cases r <;>
      simp [menuArm,menuIncrement,fullSignal,fullSide,fullAmbient,firstOrder] <;> omega
  have he : menuArm g choice = hyperplaneArm g := by cases g <;> simp_all [menuArm]
  have hi : menuIncrement g choice r = firstIncrement g r := by
    cases g <;> simp_all [menuIncrement,firstIncrement]
  simpa only [he,hi,incrementFormula] using incrementFormula_eq g hg n hn r

variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

theorem exists_menu_hyperplane_with_remote_ranks [Fintype K]
    (hq : 3 ≤ Fintype.card K) (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (hg : g ≠ .R2) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n)
    (choice : Three) (p : Equiv.Perm Three) (hp : p 0 = menuArm g choice) :
    ∃ l : F →ₗ[K] K,
      T.U (p 0) ≤ LinearMap.ker l ∧ T.LocallyGenerated (LinearMap.ker l) ∧
      T.RelayFeasible (LinearMap.ker l) ∧ finrank K (LinearMap.ker l) + 1 = finrank K F ∧
      condRank ((T.U (p 1) ⊓ T.U (p 2)) ⊓ LinearMap.ker l)
        (T.A (p 1) ⊓ LinearMap.ker l) =
          min (fullSignal g n (p 1)-fullSide g n (p 1))
            (finrank K ↥(T.U (p 1) ⊓ T.U (p 2))-1) ∧
      condRank ((T.U (p 1) ⊓ T.U (p 2)) ⊓ LinearMap.ker l)
        (T.A (p 2) ⊓ LinearMap.ker l) =
          min (fullSignal g n (p 2)-fullSide g n (p 2))
            (finrank K ↥(T.U (p 1) ⊓ T.U (p 2))-1) := by
  have hd := full_relation_dimension T hT g n hn h
  have hdpos : 0 < finrank K (LinearMap.ker (AlignedRelation.signalSum T.A)) := by
    rw [hd]; simp [codimension,hg]
  obtain ⟨r,hr⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hdpos
  have h01 : p 0 ≠ p 1 := p.injective.ne (by decide)
  have h02 : p 0 ≠ p 2 := p.injective.ne (by decide)
  have h12 : p 1 ≠ p 2 := p.injective.ne (by decide)
  have hb := relation_projection_outside T hT (h.positive_defect T g n) (p 0) (p 1) h01
    (by rw [h.side,h.side,h.side,h.signal,h.ambient,hp]; exact (menu_geometry g hg choice n hn).1) r hr
  have hspan : (Profile.reindexTask p T).Spanning := by
    simpa only [Task.Spanning,Profile.reindexTask,Equiv.iSup_comp p] using full_spanning T hT g n hn h
  have hremote := full_remote_not_le T hT g n hn h (p 0) (p 1) (p 2) h01 h02 h12
    (by rw [hp]; exact (menu_geometry g hg choice n hn).2)
  have hd1 := full_remote_disjoint T hT g n hn h (p 0) (p 1) (p 2) (p 1) h01 h02 h12
  have hd2 := full_remote_disjoint T hT g n hn h (p 0) (p 1) (p 2) (p 2) h01 h02 h12
  have hc := full_rankConditions T hT g n hn h
  have hpairdim := full_signal_pair_dimension T hT g n hn h (p 1) (p 2) h12
  have hcr1 := hc.pair_rank (p 2) (p 1) h12.symm
  have hcr2 := hc.pair_rank (p 1) (p 2) h12
  rw [inf_comm (T.U (p 2)) (T.U (p 1))] at hcr1
  simp only [finrank_top] at hcr1 hcr2
  have he1 : fullSignal g n (p 2)+fullSignal g n (p 1)-finrank K F =
      finrank K ↥(T.U (p 1) ⊓ T.U (p 2)) := by omega
  have he2 : fullSignal g n (p 1)+fullSignal g n (p 2)-finrank K F =
      finrank K ↥(T.U (p 1) ⊓ T.U (p 2)) := by omega
  rw [he1] at hcr1
  rw [he2] at hcr2
  obtain ⟨l,hU,hgen,hfeas,hdim,hr1,hr2⟩ :=
    NonzeroDefectRelays.exists_hyperplane_relay_with_remote_ranks hq (Profile.reindexTask p T) hspan
      (r.1 (p 0) : F) (r.1 (p 1) : F) (r.1 (p 2) : F)
      (r.1 (p 0)).property (r.1 (p 1)).property (r.1 (p 2)).property
      (relation_sum_permuted T.A r p) hb hremote hd1 hd2
      (fullSignal g n (p 1)-fullSide g n (p 1))
      (fullSignal g n (p 2)-fullSide g n (p 2))
      (finrank K ↥(T.U (p 1) ⊓ T.U (p 2))) rfl hcr1 hcr2
  exact ⟨l,hU,(NonzeroDefectRelays.reindex_locallyGenerated T p _).mp hgen,
    (NonzeroDefectRelays.reindex_relayFeasible T p _).mp hfeas,hdim,hr1,hr2⟩

theorem menu_hyperplane_profile (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (hgne : g ≠ .R2) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n)
    (choice : Three) (p : Equiv.Perm Three) (hp : p 0 = menuArm g choice) (l : F →ₗ[K] K)
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
      (fullFirst g n r : ℝ) + (menuIncrement g choice r : ℝ)) ∧
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
    have hinc := menu_increment_arithmetic g hgne choice n hn r
    change (if i = menuArm g choice ∨ j = menuArm g choice then 0 else
      min (fullSignal g n j-fullSide g n j) (fullSignal g n i+fullSignal g n j-fullAmbient g n) -
      min (fullSignal g n j-fullSide g n j) (fullSignal g n i+fullSignal g n j-fullAmbient g n-1)) =
        menuIncrement g choice r at hinc
    change firstEntry (inducedTask T (LinearMap.ker l) hg) i j k = _
    by_cases hs : i = menuArm g choice ∨ j = menuArm g choice
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

/-- All three indexed choices (with repetitions where there is only one)
are realized on the same actual task and attain its operational upload minimum. -/
theorem same_chart_all_menu_choices [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) (choice : Three) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P = fullAmbient g n-codimension g ∧
      (finrank K P : ℝ) = T.uploadOptimum ∧
      (∑ i, finrank K ↥(P ⊓ T.A i)) = finrank K P ∧
      (∀ r : Fin 6, entry (inducedTask T P hg) (.inl r) =
        (fullFirst g n r : ℝ) + (menuIncrement g choice r : ℝ)) ∧
      (∀ i ell : Three, 2 * entry (inducedTask T P hg) (.inr (i,ell)) =
        (doubledSecond g n : ℝ)) := by
  by_cases hR : g = .R2
  · subst g
    obtain ⟨_,_,P,hg,hf,hd,ho,hu,hfirst,hsecond⟩ :=
      NonzeroSameChartOptimality.same_chart_full_and_optimal_relay hq T hT .R2 n hn h
    exact ⟨P,hg,hf,hd,ho,hu,by simpa only [menuIncrement,firstIncrement] using hfirst,hsecond⟩
  · let p : Equiv.Perm Three := Equiv.swap 0 (menuArm g choice)
    have hp : p 0 = menuArm g choice := by simp [p]
    obtain ⟨l,hU,hg,hf,hdim,hr1,hr2⟩ := exists_menu_hyperplane_with_remote_ranks hq T hT g hR n hn h choice p hp
    obtain ⟨hfirst,hsecond⟩ := menu_hyperplane_profile T hT g hR n hn h choice p hp l hU hg hf hdim hr1 hr2
    have hd : finrank K (LinearMap.ker l) = fullAmbient g n-codimension g := by
      rw [h.ambient] at hdim
      simp only [codimension,if_neg hR]
      omega
    have hu := NonzeroHyperplaneUpload.full_hyperplane_upload T hT g hR n hn h p l hU hf hdim
    refine ⟨LinearMap.ker l,hg,hf,hd,?_,?_,hfirst,hsecond⟩
    · exact NonzeroSameChartOptimality.relay_rank_eq_uploadOptimum T hT g n hn h _ hg hf hd
    · rw [hu,hd,codimension,if_neg hR]

end UploadBroadcast.NonzeroSameChartMenus
