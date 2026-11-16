import UploadBroadcast.BinaryRelayMenus
import UploadBroadcast.ScalarPaperEndpoints

/-! Small zero-margin relay constructions. All relay and broadcast subspaces
are constructed in the original coefficient space. The hypotheses are the
original common-demand and local-side geometry, never output profile bounds. -/
namespace UploadBroadcast.BinaryExceptionalRelays
open Module Profile NonzeroDefectRelays BinaryRelayMenus
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- The sum of two genuinely local subspaces is locally generated. -/
theorem local_sup_locallyGenerated (T : Task K F) (A B : Submodule K F)
    (i j : Three) (hA : A ≤ T.A i) (hB : B ≤ T.A j) :
    T.LocallyGenerated (A ⊔ B) := by
  apply le_antisymm
  · apply sup_le
    · exact (le_inf le_sup_left hA).trans (le_iSup (fun k => (A ⊔ B) ⊓ T.A k) i)
    · exact (le_inf le_sup_right hB).trans (le_iSup (fun k => (A ⊔ B) ⊓ T.A k) j)
  · exact iSup_le (fun _ => inf_le_left)

section Finite
variable [FiniteDimensional K F]

omit [FiniteDimensional K F] in
/-- Upload the two local components of a generator of the common demand
line. Both components are nonzero and independent, so the relay has dimension
exactly two. This covers H+δ and R₂+δ after their original-space identities. -/
theorem two_local_components_relay (T : Task K F) (i j : Three)
    (hdis : Disjoint (T.A i) (T.A j)) (hsum : T.A i ⊔ T.A j=⊤)
    (t : F) (hti : t ∉ T.A i) (htj : t ∉ T.A j)
    (hU : ∀ k, T.U k ≤ T.A k ⊔ Submodule.span K {t}) :
    ∃ P : Submodule K F, T.LocallyGenerated P ∧ T.RelayFeasible P ∧
      finrank K P=2 ∧ Submodule.span K {t} ≤ P := by
  have ht : t ∈ T.A i ⊔ T.A j := by rw [hsum]; trivial
  obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp ht
  have ha0 : a ≠ 0 := by
    intro h; apply htj; rw [h,zero_add] at hab; exact hab ▸ hb
  have hb0 : b ≠ 0 := by
    intro h; apply hti; rw [h,add_zero] at hab; exact hab ▸ ha
  let A := Submodule.span K {a}
  let B := Submodule.span K {b}
  have hA : A ≤ T.A i := Submodule.span_le.mpr (by simpa using ha)
  have hB : B ≤ T.A j := Submodule.span_le.mpr (by simpa using hb)
  have htP : Submodule.span K {t} ≤ A ⊔ B := by
    apply Submodule.span_le.mpr
    simp only [Set.singleton_subset_iff]
    rw [← hab]
    exact Submodule.add_mem_sup (Submodule.mem_span_singleton_self a)
      (Submodule.mem_span_singleton_self b)
  have hd : finrank K ↥(A ⊔ B)=2 := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [(hdis.mono hA hB).eq_bot,finrank_bot,
      show finrank K A=1 from finrank_span_singleton ha0,
      show finrank K B=1 from finrank_span_singleton hb0] at hdim
    omega
  exact ⟨A ⊔ B,local_sup_locallyGenerated T A B i j hA hB,
    fun k => (hU k).trans (sup_le_sup_left htP _),hd,htP⟩

/-- A signal hyperplane with a transverse relation projection is itself
locally generated and feasible. This is the four-upload T₃+δ construction. -/
theorem signal_hyperplane_relay (T : Task K F) (hspan : T.Spanning)
    (a b c : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a+b+c=0) (hbU : b ∉ T.U 0)
    (hdim : finrank K (T.U 0)+1=finrank K F) :
    T.LocallyGenerated (T.U 0) ∧ T.RelayFeasible (T.U 0) := by
  obtain ⟨l,hU,_,_,hg,hf,hd⟩ :=
    exists_binary_hyperplane_relay T hspan a b c b ha hb hc hrel hbU hbU
  have he : T.U 0=LinearMap.ker l :=
    Submodule.eq_of_le_of_finrank_eq hU (by omega)
  simpa only [← he] using And.intro hg hf

/-- Transversality of the common triple to a nonzero relation projection
forces one of the signal hyperplanes to be a locally generated relay. -/
theorem exists_signal_hyperplane_relay (T : Task K F) (hspan : T.Spanning)
    (a b c : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a+b+c=0) (hb0 : b ≠ 0)
    (hdis : Disjoint (T.U 0 ⊓ T.U 1 ⊓ T.U 2) (T.A 1))
    (hdim : ∀ i, finrank K (T.U i)+1=finrank K F) :
    ∃ s : Three, T.LocallyGenerated (T.U s) ∧ T.RelayFeasible (T.U s) := by
  by_cases hbU : b ∈ T.U 0
  · have hbU' : b ∉ T.U 2 := by
      intro hh
      exact hb0 ((Submodule.disjoint_def.mp hdis) b
        ⟨⟨hbU,T.side_le_signal 1 hb⟩,hh⟩ hb)
    let p : Equiv.Perm Three := Equiv.swap 0 2
    have hspan' : (Profile.reindexTask p T).Spanning := by
      simpa only [Task.Spanning,Profile.reindexTask,Equiv.iSup_comp p] using hspan
    have hh := signal_hyperplane_relay (Profile.reindexTask p T) hspan' c b a
      (by simpa [Profile.reindexTask,p] using hc)
      (by simpa [Profile.reindexTask,p] using hb)
      (by simpa [Profile.reindexTask,p] using ha)
      (by
        calc
          c+b+a=a+b+c := by abel
          _=0 := hrel)
      (by simpa [Profile.reindexTask,p] using hbU')
      (by simpa [Profile.reindexTask,p] using hdim 2)
    have hgen := (reindex_locallyGenerated T p ((Profile.reindexTask p T).U 0)).mp hh.1
    have hfeas := (reindex_relayFeasible T p ((Profile.reindexTask p T).U 0)).mp hh.2
    exact ⟨2,by simpa [Profile.reindexTask,p] using And.intro hgen hfeas⟩
  · exact ⟨0,signal_hyperplane_relay T hspan a b c ha hb hc hrel hbU (hdim 0)⟩

omit [FiniteDimensional K F] in
/-- A common coefficient subspace contained in the relay still solves the
induced demands, with their actually restricted side information. -/
theorem common_subspace_induced_feasible (T : Task K F) (P S : Submodule K F)
    (hS : S ≤ P) (hU : ∀ i, T.U i ≤ T.A i ⊔ S) :
    ∀ i, T.U i ⊓ P ≤ (T.A i ⊓ P) ⊔ S := by
  intro i
  have hm := sup_inf_assoc_of_le (T.A i) hS
  rw [sup_comm S (T.A i),sup_comm S] at hm
  exact (inf_le_inf (hU i) le_rfl).trans_eq hm

/-- Broadcasting the common subspace provides an actual scalar code and
bounds all fifteen induced profile entries by its dimension. -/
theorem common_subspace_profile_bound [Finite K]
    (T : Task K F) (P S : Submodule K F) (hg : T.LocallyGenerated P)
    (hS : S ≤ P) (hU : ∀ i, T.U i ≤ T.A i ⊔ S) :
    Nonempty (ScalarBroadcastCode (inducedTask T P hg).A
      (inducedTask T P hg).U (finrank K S)) ∧
      ∀ r : Profile.Index, Profile.entry (inducedTask T P hg) r ≤ (finrank K S : ℝ) := by
  obtain ⟨c⟩ := scalarBroadcastCode_of_subspace (inducedTask T P hg).A
    (inducedTask T P hg).U S (common_subspace_induced_feasible T P S hS hU)
  refine ⟨⟨c⟩,fun r => ?_⟩
  have hl := c.toBlockOne.rankBound_le_cost (inducedTask T P hg).side_le_signal (by decide : 0<1)
  rw [Allocation.rawRankBound_eq_rankBound,c.toBlockOne_cost] at hl
  exact (Finset.le_sup' (Profile.entry (inducedTask T P hg)) (Finset.mem_univ r)).trans
    (hl.trans (scalarBroadcastCode_cost_le c))

/-- The two-upload/one-broadcast small exceptions, including all fifteen
induced-entry bounds, proved directly from their local/common-line geometry. -/
theorem two_upload_one_broadcast [Finite K] (T : Task K F) (i j : Three)
    (hdis : Disjoint (T.A i) (T.A j)) (hsum : T.A i ⊔ T.A j=⊤)
    (t : F) (hti : t ∉ T.A i) (htj : t ∉ T.A j)
    (hU : ∀ k, T.U k ≤ T.A k ⊔ Submodule.span K {t}) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P=2 ∧
      Nonempty (ScalarBroadcastCode (inducedTask T P hg).A (inducedTask T P hg).U 1) ∧
      ∀ r : Profile.Index, Profile.entry (inducedTask T P hg) r ≤ 1 := by
  obtain ⟨P,hg,hf,hd,hS⟩ := two_local_components_relay T i j hdis hsum t hti htj hU
  have ht0 : t ≠ 0 := by intro h; exact hti (h ▸ (T.A i).zero_mem)
  have hdim : finrank K (Submodule.span K {t})=1 := finrank_span_singleton ht0
  have hh := common_subspace_profile_bound T P (Submodule.span K {t}) hg hS hU
  rw [hdim,Nat.cast_one] at hh
  exact ⟨P,hg,hf,hd,hh⟩

/-- The four-upload/two-broadcast small exception. The chosen arm is
constructed from triple transversality, rather than supplied as an output. -/
theorem four_upload_two_broadcast [Finite K] (T : Task K F) (hspan : T.Spanning)
    (a b c : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a+b+c=0) (hb0 : b ≠ 0)
    (hdis : Disjoint (T.U 0 ⊓ T.U 1 ⊓ T.U 2) (T.A 1))
    (hdim : finrank K F=5) (hUi : ∀ i, finrank K (T.U i)=4)
    (S : Submodule K F) (hS : finrank K S=2)
    (hSU : ∀ i, S ≤ T.U i) (hU : ∀ i, T.U i ≤ T.A i ⊔ S) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P=4 ∧
      Nonempty (ScalarBroadcastCode (inducedTask T P hg).A (inducedTask T P hg).U 2) ∧
      ∀ r : Profile.Index, Profile.entry (inducedTask T P hg) r ≤ 2 := by
  obtain ⟨s,hg,hf⟩ := exists_signal_hyperplane_relay T hspan a b c ha hb hc hrel hb0 hdis
    (by intro i; rw [hdim,hUi i])
  have hh := common_subspace_profile_bound T (T.U s) S hg (hSU s) hU
  rw [hS,Nat.cast_ofNat] at hh
  exact ⟨T.U s,hg,hf,hUi s,hh⟩

/-- The original n=1 profiles of the zero-margin exceptional families are
constant; this uses only the pre-existing original-space rank conditions. -/
theorem exceptional_full_profile (T : Task K F) (V : Submodule K F)
    (g : NonzeroDefectProfile.Family) (hg : g=.H ∨ g=.R2 ∨ g=.T3)
    (hd : finrank K V=NonzeroDefectProfile.fullAmbient g 1)
    (h : NonzeroDefectProfile.RankConditions T V
      (NonzeroDefectProfile.fullSide g 1) (NonzeroDefectProfile.fullSignal g 1))
    (r : Profile.Index) : Profile.entry T r=(if g=.T3 then 2 else 1) := by
  rcases r with r | ⟨i,ell⟩
  · rw [NonzeroDefectProfile.full_first_entries T V g 1 (by decide) hd h r]
    rcases hg with rfl | rfl | rfl <;> fin_cases r <;>
      norm_num [NonzeroDefectProfile.fullFirst,
        show NonzeroDefectProfile.Family.H ≠ .T3 from by decide,
        show NonzeroDefectProfile.Family.R2 ≠ .T3 from by decide]
  · have hh := NonzeroDefectProfile.full_second_entries T V g 1 (by decide) hd h i ell
    rcases hg with rfl | rfl | rfl <;>
      norm_num [NonzeroDefectProfile.doubledSecond,
        show NonzeroDefectProfile.Family.H ≠ .T3 from by decide,
        show NonzeroDefectProfile.Family.R2 ≠ .T3 from by decide] at hh ⊢ <;> linarith

/-- The constructed two-upload exceptional relay never increases an entry
when the full H+δ or R₂+δ geometry is supplied. -/
theorem small_exception_profile_preserving [Finite K]
    (T : Task K F) (V : Submodule K F) (g : NonzeroDefectProfile.Family)
    (hg : g=.H ∨ g=.R2)
    (hd : finrank K V=NonzeroDefectProfile.fullAmbient g 1)
    (h : NonzeroDefectProfile.RankConditions T V
      (NonzeroDefectProfile.fullSide g 1) (NonzeroDefectProfile.fullSignal g 1))
    (i j : Three) (hdis : Disjoint (T.A i) (T.A j)) (hsum : T.A i ⊔ T.A j=⊤)
    (t : F) (hti : t ∉ T.A i) (htj : t ∉ T.A j)
    (hU : ∀ k, T.U k ≤ T.A k ⊔ Submodule.span K {t}) :
    ∃ P : Submodule K F, ∃ hlocal : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P=2 ∧
      ∀ r : Profile.Index, Profile.entry (inducedTask T P hlocal) r ≤ Profile.entry T r := by
  obtain ⟨P,hlocal,hfeas,hP,_,hbound⟩ := two_upload_one_broadcast T i j hdis hsum t hti htj hU
  refine ⟨P,hlocal,hfeas,hP,fun r => ?_⟩
  have hfull := exceptional_full_profile T V g
    (hg.elim Or.inl (fun he => Or.inr (Or.inl he))) hd h r
  have hn : g ≠ .T3 := by rcases hg with rfl | rfl <;> decide
  rw [hfull,if_neg hn]
  exact hbound r

/-- The constructed T₃+δ four-upload relay likewise preserves or reduces
all entries once its original geometric rank conditions are supplied. -/
theorem tripod_exception_profile_preserving [Finite K]
    (T : Task K F) (hspan : T.Spanning)
    (h : NonzeroDefectProfile.RankConditions T ⊤
      (NonzeroDefectProfile.fullSide .T3 1) (NonzeroDefectProfile.fullSignal .T3 1))
    (a b c : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a+b+c=0) (hb0 : b ≠ 0)
    (hdis : Disjoint (T.U 0 ⊓ T.U 1 ⊓ T.U 2) (T.A 1))
    (hdim : finrank K F=5) (S : Submodule K F) (hS : finrank K S=2)
    (hSU : ∀ i, S ≤ T.U i) (hU : ∀ i, T.U i ≤ T.A i ⊔ S) :
    ∃ P : Submodule K F, ∃ hlocal : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P=4 ∧
      ∀ r : Profile.Index, Profile.entry (inducedTask T P hlocal) r ≤ Profile.entry T r := by
  have hUi : ∀ i, finrank K (T.U i)=4 := by
    intro i; have hh := h.signal_dimension i
    fin_cases i <;> simpa [NonzeroDefectProfile.fullSignal] using hh
  obtain ⟨P,hlocal,hfeas,hP,_,hbound⟩ := four_upload_two_broadcast T hspan a b c ha hb hc
    hrel hb0 hdis hdim hUi S hS hSU hU
  refine ⟨P,hlocal,hfeas,hP,fun r => ?_⟩
  have hfull := exceptional_full_profile T ⊤ .T3 (Or.inr (Or.inr rfl))
    (by simpa [NonzeroDefectProfile.fullAmbient] using hdim) h r
  rw [hfull,if_pos rfl]
  exact hbound r

end Finite
end UploadBroadcast.BinaryExceptionalRelays
