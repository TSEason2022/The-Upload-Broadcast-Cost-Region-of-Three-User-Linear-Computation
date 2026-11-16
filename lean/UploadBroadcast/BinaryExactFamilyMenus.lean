import UploadBroadcast.BinaryExactMenus

namespace UploadBroadcast.BinaryExactFamilyMenus
open Module Profile NonzeroDefectRelays NonzeroDefectProfile NonzeroFamilyRanks
open NonzeroRelationRestrictions BinaryRelayProfiles R2PermutedMenus
open NonzeroBinaryMenus BinaryExactMenus
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

theorem full_hyperplane_exact_menu (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (hg : g ≠ .R2) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n)
    (k : Fin 6) (protect : Bool)
    (heuler : fullSide g n 0+fullSide g n 1+fullSide g n 2+
      fullSignal g n (pathPerm k 0) ≤ 2*fullAmbient g n)
    (hproper : fullSignal g n (pathPerm k 0)<fullAmbient g n)
    (hprotect : protect=true → fullAmbient g n<fullSide g n (pathPerm k 1)+fullSignal g n (pathPerm k 2))
    (hz2 : fullSide g n (pathPerm k 2)+fullSignal g n (pathPerm k 1) ≤ fullAmbient g n)
    (hz1 : protect=false → fullSide g n (pathPerm k 1)+fullSignal g n (pathPerm k 2) ≤ fullAmbient g n) :
    ∃ P : Submodule K F, ∃ hlocal : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P+1=finrank K F ∧
      (∀ r : Fin 6, entry (inducedTask T P hlocal) (.inl r) =
        entry T (.inl r)+(baseIncrement protect (inverseFirst k r) : ℝ)) ∧
      (∀ r : Three × Three, entry (inducedTask T P hlocal) (.inr r)=entry T (.inr r)) := by
  let p := pathPerm k
  let T' := reindexTask p T
  have hd := full_relation_dimension T hT g n hn h
  have hdpos : 0 < finrank K (LinearMap.ker (AlignedRelation.signalSum T.A)) := by
    rw [hd]; simp [codimension,hg]
  obtain ⟨r,hr⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hdpos
  have h01 : p 0 ≠ p 1 := p.injective.ne (by decide)
  have h02 : p 0 ≠ p 2 := p.injective.ne (by decide)
  have h12 : p 1 ≠ p 2 := p.injective.ne (by decide)
  have hrel := relation_sum_permuted T.A r p
  have hb := relation_projection_outside T hT (h.positive_defect T g n) (p 0) (p 1) h01
    (by rw [h.side,h.side,h.side,h.signal,h.ambient]; exact heuler) r hr
  have hspan : T'.Spanning := by
    simpa only [T',Task.Spanning,reindexTask,Equiv.iSup_comp p] using full_spanning T hT g n hn h
  have hc := full_rankConditions T hT g n hn h
  have hp' : ∀ i j, i ≠ j → T'.U i ⊔ T'.U j=⊤ :=
    fun i j hij => hc.pair_span (p i) (p j) (p.injective.ne hij)
  have hi' : ∀ i j l, i ≠ j → i ≠ l → j ≠ l →
      (T'.U i ⊓ T'.U j) ⊔ (T'.U i ⊓ T'.U l)=T'.U i :=
    fun i j l hij hil hjl => hc.pair_intersections_span _ _ _
      (p.injective.ne hij) (p.injective.ne hil) (p.injective.ne hjl)
  have zero_remote (i j : Three) (hne : i≠j)
      (hz : fullSide g n i+fullSignal g n j ≤ fullAmbient g n) :
      T.A i ⊓ T.U j=⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have hd := full_side_signal_dimension T hT g n hn h j i hne.symm
    rw [h.ambient] at hd
    omega
  have hzero2 : T'.A 2 ⊓ (T'.U 1 ⊓ T'.U 2)=⊥ := by
    apply bot_unique
    exact (inf_le_inf_left _ inf_le_left).trans_eq (zero_remote (p 2) (p 1) h12.symm hz2)
  have hzero1 (hf : protect=false) : T'.A 1 ⊓ (T'.U 1 ⊓ T'.U 2)=⊥ := by
    apply bot_unique
    exact (inf_le_inf_left _ inf_le_right).trans_eq (zero_remote (p 1) (p 2) h12 (hz1 hf))
  have hex : ∃ P : Submodule K F, ∃ hg' : T'.LocallyGenerated P,
      T'.RelayFeasible P ∧ finrank K P+1=finrank K F ∧
      (∀ r : Fin 6, entry (inducedTask T' P hg') (.inl r) = entry T' (.inl r)+(baseIncrement protect r : ℝ)) ∧
      (∀ r : Three × Three, entry (inducedTask T' P hg') (.inr r)=entry T' (.inr r)) := by
    cases protect
    · have hremote := full_remote_not_le T hT g n hn h (p 0) (p 1) (p 2) h01 h02 h12 hproper
      obtain ⟨P,hg',hf,hd,hfirst,hsecond⟩ := exists_double_binary_profile_exact T' hspan
        (r.1 (p 0) : F) (r.1 (p 1) : F) (r.1 (p 2) : F)
        (r.1 (p 0)).property (r.1 (p 1)).property (r.1 (p 2)).property hrel hb hp' hi' hremote
        (by intro j hj; rcases hj with rfl | rfl; exact hzero1 rfl; exact hzero2)
      exact ⟨P,hg',hf,hd,by simpa [baseIncrement] using hfirst,hsecond⟩
    · have hdis := full_remote_disjoint T hT g n hn h (p 0) (p 1) (p 2) (p 1) h01 h02 h12
      have he : T.A (p 1) ⊓ (T.U (p 1) ⊓ T.U (p 2))=T.A (p 1) ⊓ T.U (p 2) := by
        ext x
        exact ⟨fun hx => ⟨hx.1,hx.2.2⟩,fun hx => ⟨hx.1,T.side_le_signal _ hx.1,hx.2⟩⟩
      have hCn : T'.A 1 ⊓ (T'.U 1 ⊓ T'.U 2) ≠ ⊥ := by
        change T.A (p 1) ⊓ (T.U (p 1) ⊓ T.U (p 2)) ≠ ⊥
        rw [he]
        intro hz
        have hdim := full_side_signal_dimension T hT g n hn h (p 2) (p 1) h12.symm
        rw [hz,finrank_bot,zero_add,h.ambient] at hdim
        have hh := hprotect rfl
        dsimp [p] at hdim
        omega
      obtain ⟨P,hg',hf,hd,hfirst,hsecond⟩ := exists_protected_binary_profile_exact T' hspan
        (r.1 (p 0) : F) (r.1 (p 1) : F) (r.1 (p 2) : F)
        (r.1 (p 0)).property (r.1 (p 1)).property (r.1 (p 2)).property hrel hb hp' hi' hdis hCn hzero2
      exact ⟨P,hg',hf,hd,by simpa [baseIncrement] using hfirst,hsecond⟩
  obtain ⟨P,hg',hf,hd,hfirst,hsecond⟩ := hex
  have hlocal : T.LocallyGenerated P := (reindex_locallyGenerated T p P).mp hg'
  have hfeas : T.RelayFeasible P := (reindex_relayFeasible T p P).mp hf
  have he : inducedTask T' P hg'=reindexTask p (inducedTask T P hlocal) := rfl
  refine ⟨P,hlocal,hfeas,hd,?_,?_⟩
  · intro r
    have hh := hfirst (inverseFirst k r)
    rw [he] at hh
    change entry (reindexTask (pathPerm k) (inducedTask T P hlocal)) (.inl (inverseFirst k r)) =
      entry (reindexTask (pathPerm k) T) (.inl (inverseFirst k r))+_ at hh
    simpa only [firstEntry_path_reindex] using hh
  · rintro ⟨i,ell⟩
    have hh := hsecond (inverseUser k i,inverseUser k ell)
    rw [he] at hh
    change entry (reindexTask (pathPerm k) (inducedTask T P hlocal))
      (.inr (inverseUser k i,inverseUser k ell))=
      entry (reindexTask (pathPerm k) T) (.inr (inverseUser k i,inverseUser k ell)) at hh
    simpa only [secondEntry_path_reindex] using hh


/-- The original T1/O choices have zero unprotected remote intersections. -/
theorem original_menu_zero_arithmetic (g : Kind) (hg : g=.T1 ∨ g=.O)
    (k : Fin 6) (n : ℕ) (_hn : 1 ≤ n) :
    let f := family g
    let p := pathPerm (choice g k).1
    fullSide f n (p 2)+fullSignal f n (p 1) ≤ fullAmbient f n ∧
      ((choice g k).2=false → fullSide f n (p 1)+fullSignal f n (p 2) ≤ fullAmbient f n) := by
  rcases hg with rfl | rfl <;> fin_cases k <;>
    dsimp [family,choice,pathPerm,fullSide,fullSignal,fullAmbient]
  all_goals norm_num [Equiv.swap_apply_def]
  all_goals try dsimp
  all_goals omega

/-- Every original T1/O menu member is realized with exact increments over
any field, in particular over the original binary field. -/
theorem full_original_binary_exact_menu (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Kind) (hg : g=.T1 ∨ g=.O) (n : ℕ) (hn : 1 ≤ n)
    (h : Dimensions T (family g) n) (k : Fin 6) :
    ∃ P : Submodule K F, ∃ hlocal : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P=fullAmbient (family g) n-1 ∧
      (∀ r : Fin 6, entry (inducedTask T P hlocal) (.inl r) = entry T (.inl r)+(menu g k r : ℝ)) ∧
      (∀ r : Three × Three, entry (inducedTask T P hlocal) (.inr r)=entry T (.inr r)) := by
  have hh := menu_geometry_arithmetic g k n hn
  have hz := original_menu_zero_arithmetic g hg k n hn
  obtain ⟨P,hlocal,hfeas,hd,hfirst,hsecond⟩ := full_hyperplane_exact_menu T hT (family g)
    (by cases g <;> decide) n hn h (choice g k).1 (choice g k).2 hh.1 hh.2.1 hh.2.2 hz.1 hz.2
  refine ⟨P,hlocal,hfeas,?_,?_,hsecond⟩
  · rw [h.ambient] at hd
    omega
  · intro r
    simpa only [menu_is_reindexed_bound] using hfirst r

end UploadBroadcast.BinaryExactFamilyMenus
