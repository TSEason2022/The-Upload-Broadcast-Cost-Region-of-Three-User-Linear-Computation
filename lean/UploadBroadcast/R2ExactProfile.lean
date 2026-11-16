import UploadBroadcast.NonzeroR2Wedge

/-! Profile-preserving R₂ relay over every original finite field of size at
least three, with all geometric hypotheses discharged by actual family ranks. -/
namespace UploadBroadcast.R2ExactProfile
open Module Profile NonzeroDefectRelays NonzeroFamilyRanks NonzeroDefectProfile
open NonzeroR2Wedge BinaryRelayProfiles BinaryCodimTwoProfiles
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Protection of a side/pair intersection gives exact rank after two cuts
when the other form already vanishes on the pair. -/
theorem protected_codimTwo_condRank (A B : Submodule K F) (l₁ l₂ : F →ₗ[K] K)
    (hB : B ≤ LinearMap.ker l₁) (hv : ∃ v ∈ A ⊓ B, l₂ v ≠ 0) :
    condRank (B ⊓ (LinearMap.ker l₁ ⊓ LinearMap.ker l₂))
      (A ⊓ (LinearMap.ker l₁ ⊓ LinearMap.ker l₂))=condRank B A := by
  rw [codimTwo_condRank_reduction A B l₁ l₂ hB]
  exact protected_condRank A B l₂ hv

/-- Exact all-fifteen R₂ same-chart construction. The source task is supplied
only through indecomposability and its original seven-entry dimension vector. -/
theorem full_R2_profile_and_upload [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T .R2 n) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P=3*n-1 ∧
      (∑ i, finrank K ↥(P ⊓ T.A i))=finrank K P ∧
      ∀ r : Profile.Index, entry (inducedTask T P hg) r=entry T r := by
  obtain ⟨r,w,hw⟩ := full_relationWedge_nonzero T hT n hn h
  obtain ⟨v₀,hv₀,hv₀U⟩ := full_remote_witness T hT n hn h 0 1 2 (by decide) (by decide) (by decide)
  obtain ⟨v₁,hv₁,hv₁U⟩ := full_remote_witness T hT n hn h 0 2 1 (by decide) (by decide) (by decide)
  obtain ⟨z₀,hz₀,hz₀U⟩ := full_remote_witness T hT n hn h 1 0 2 (by decide) (by decide) (by decide)
  obtain ⟨z₁,hz₁,hz₁U⟩ := full_remote_witness T hT n hn h 1 2 0 (by decide) (by decide) (by decide)
  have hs := full_spanning T hT .R2 n hn h
  obtain ⟨f₁,f₂,hlv₀,hlv₁,hlz₀,hlz₁,hwedge⟩ :=
    exists_bilinear_nonzero_with_two_constraints (K := K)
      (X := (T.U 0).dualAnnihilator) (Y := (T.U 1).dualAnnihilator)
      hq (relationWedge T r w) hw
      (annihilatorEvaluation (T.U 0) v₀) (annihilatorEvaluation (T.U 0) v₁)
      (annihilatorEvaluation (T.U 1) z₀) (annihilatorEvaluation (T.U 1) z₁)
      (annihilatorEvaluation_ne_zero _ _ hv₀U) (annihilatorEvaluation_ne_zero _ _ hv₁U)
      (annihilatorEvaluation_ne_zero _ _ hz₀U) (annihilatorEvaluation_ne_zero _ _ hz₁U)
  let l₁ := f₁.1
  let l₂ := f₂.1
  have h₁ : T.U 0 ≤ LinearMap.ker l₁ := by
    intro x hx; exact (Submodule.mem_dualAnnihilator f₁.1).mp f₁.property x hx
  have h₂ : T.U 1 ≤ LinearMap.ker l₂ := by
    intro x hx; exact (Submodule.mem_dualAnnihilator f₂.1).mp f₂.property x hx
  have hsurj : Function.Surjective (relationEvaluation T.A l₁ l₂) :=
    surjective_of_wedge (relationEvaluation T.A l₁ l₂) r w hwedge
  have hg := codimTwo_locally_generated T l₁ l₂ hs h₁ h₂ hsurj
  have hf := codimTwo_feasible T l₁ l₂ h₁ h₂ hsurj
  have hd := codimTwo_finrank T l₁ l₂ h₁ h₂ hsurj
  have hexcess : (∑ i, finrank K (T.A i))=finrank K F+2 := by
    simp only [Fin.sum_univ_three,h.side,h.ambient]
    change (n+1)+(n+1)+(n+1)=(3*n+1)+2
    omega
  have hupload := codimTwo_upload_dimension T l₁ l₂ h₁ h₂ hsurj hexcess
  let P := LinearMap.ker l₁ ⊓ LinearMap.ker l₂
  have hc := full_rankConditions T hT .R2 n hn h
  obtain ⟨hp',hi'⟩ := codimTwo_spans T l₁ l₂ h₁ h₂ hc.pair_span hc.pair_intersections_span
    v₀ z₁ ⟨T.side_le_signal 1 hv₀.1,hv₀.2⟩ ⟨hz₁.2,T.side_le_signal 2 hz₁.1⟩ hlv₀ hlz₁
  have ht : T.U 0 ⊓ T.U 1 ⊓ T.U 2 ≤ P :=
    le_inf (inf_le_left.trans (inf_le_left.trans h₁)) (inf_le_left.trans (inf_le_right.trans h₂))
  have hrank (i j : Three) (hij : i ≠ j) :
      condRank ((T.U i ⊓ T.U j) ⊓ P) (T.A j ⊓ P)=condRank (T.U i ⊓ T.U j) (T.A j) := by
    fin_cases i <;> fin_cases j <;> try contradiction
    · exact condRank_unchanged_of_le _ _ _ (le_inf (inf_le_left.trans h₁) (inf_le_right.trans h₂))
    · exact protected_codimTwo_condRank _ _ _ _ (inf_le_left.trans h₁)
        ⟨z₁,⟨hz₁.1,hz₁.2,T.side_le_signal 2 hz₁.1⟩,hlz₁⟩
    · exact condRank_unchanged_of_le _ _ _ (le_inf (inf_le_right.trans h₁) (inf_le_left.trans h₂))
    · simpa only [P,inf_comm (LinearMap.ker l₂) (LinearMap.ker l₁)] using
        protected_codimTwo_condRank (T.A 2) (T.U 1 ⊓ T.U 2) l₂ l₁ (inf_le_left.trans h₂)
          ⟨v₁,⟨hv₁.1,hv₁.2,T.side_le_signal 2 hv₁.1⟩,hlv₁⟩
    · exact protected_codimTwo_condRank _ _ _ _ (inf_le_right.trans h₁)
        ⟨z₀,⟨hz₀.1,hz₀.2,T.side_le_signal 0 hz₀.1⟩,hlz₀⟩
    · simpa only [P,inf_comm (LinearMap.ker l₂) (LinearMap.ker l₁)] using
        protected_codimTwo_condRank (T.A 1) (T.U 2 ⊓ T.U 1) l₂ l₁ (inf_le_right.trans h₂)
          ⟨v₀,⟨hv₀.1,hv₀.2,T.side_le_signal 1 hv₀.1⟩,hlv₀⟩
  refine ⟨P,hg,hf,?_,hupload,?_⟩
  · rw [h.ambient] at hd
    simp only [fullAmbient] at hd
    change finrank K ↥(LinearMap.ker l₁ ⊓ LinearMap.ker l₂)=3*n-1
    omega
  · intro r
    rcases r with r | ⟨i,ell⟩
    · have hij : (firstOrder r).1 ≠ (firstOrder r).2.1 := by fin_cases r <;> decide
      have he := firstEntry_difference T P hg hf (firstOrder r).1 (firstOrder r).2.1
        (firstOrder r).2.2 (hc.pair_span _ _ hij) (hp' _ _ hij)
      rw [hrank _ _ hij] at he
      change firstEntry (inducedTask T P hg) _ _ _=firstEntry T _ _ _
      linarith only [he]
    · exact secondEntry_preserved T P hg hf hc.pair_span hc.pair_intersections_span hp' hi' ht
        i (i+1) (i+2) ell (by fin_cases i <;> decide)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)

/-- Profile-only projection of the exact local-upload construction. -/
theorem full_R2_profile_preserving [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T .R2 n) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P=3*n-1 ∧
      ∀ r : Profile.Index, entry (inducedTask T P hg) r=entry T r := by
  obtain ⟨P,hg,hf,hd,_,hprofile⟩ := full_R2_profile_and_upload hq T hT n hn h
  exact ⟨P,hg,hf,hd,hprofile⟩

end UploadBroadcast.R2ExactProfile
