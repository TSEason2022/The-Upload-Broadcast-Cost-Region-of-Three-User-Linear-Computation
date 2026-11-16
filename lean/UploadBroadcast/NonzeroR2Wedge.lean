import UploadBroadcast.BinaryCodimTwoProfiles
import UploadBroadcast.NonzeroFamilyRanks
import UploadBroadcast.NonzeroRelationRestrictions
import UploadBroadcast.TwoDimensionalWedge

/-! Actual relation-annihilator maps for the R₂ family. -/
namespace UploadBroadcast.NonzeroR2Wedge
open Module NonzeroDefectRelays NonzeroFamilyRanks NonzeroDefectProfile
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

abbrev Relation (T : Task K F) := LinearMap.ker (AlignedRelation.signalSum T.A)

/-- A relation arm read in the original ambient coefficient space. -/
def projection (T : Task K F) (i : Three) : Relation T →ₗ[K] F :=
  ((T.A i).subtype.comp (LinearMap.proj i)).comp (Relation T).subtype

/-- The first restriction family in the relation wedge. -/
def leftForm (T : Task K F) (l : (T.U 0).dualAnnihilator) : Relation T →ₗ[K] K :=
  l.1.comp (projection T 1)

/-- The second restriction family in the relation wedge. -/
def rightForm (T : Task K F) (l : (T.U 1).dualAnnihilator) : Relation T →ₗ[K] K :=
  l.1.comp (projection T 0)

/-- A two-dimensional injective relation projection cannot fit in the
one-dimensional remote side/signal intersection. -/
theorem exists_projection_outside (T : Task K F) (s j : Three)
    (hd : 2 ≤ finrank K (Relation T)) (hinj : Function.Injective (projection T j))
    (hc : finrank K ↥(T.A j ⊓ T.U s) < 2) :
    ∃ r : Relation T, (r.1 j : F) ∉ T.U s := by
  by_contra hh
  push_neg at hh
  let f : Relation T →ₗ[K] ↥(T.A j ⊓ T.U s) :=
    (projection T j).codRestrict (T.A j ⊓ T.U s) (fun r => ⟨(r.1 j).property,hh r⟩)
  have hf : Function.Injective f := by
    intro r w he
    apply hinj
    exact congrArg (fun x : ↥(T.A j ⊓ T.U s) => (x : F)) he
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  omega

/-- A transverse projected relation provides a genuinely nonzero annihilator
restriction, without an extension of the base field. -/
theorem exists_leftForm_nonzero (T : Task K F)
    (hr : ∃ r : Relation T, (r.1 1 : F) ∉ T.U 0) :
    ∃ l : (T.U 0).dualAnnihilator, leftForm T l ≠ 0 := by
  obtain ⟨r,hr⟩ := hr
  obtain ⟨l,hU,hl,_⟩ := BinaryRelayMenus.exists_annihilating_form_two (T.U 0)
    (r.1 1 : F) (r.1 1 : F) hr hr
  have hlann : l ∈ (T.U 0).dualAnnihilator :=
    (Submodule.mem_dualAnnihilator l).mpr (fun x hx => hU hx)
  refine ⟨⟨l,hlann⟩,fun hz => ?_⟩
  exact hl (LinearMap.congr_fun hz r)

theorem exists_rightForm_nonzero (T : Task K F)
    (hr : ∃ r : Relation T, (r.1 0 : F) ∉ T.U 1) :
    ∃ l : (T.U 1).dualAnnihilator, rightForm T l ≠ 0 := by
  obtain ⟨r,hr⟩ := hr
  obtain ⟨l,hU,hl,_⟩ := BinaryRelayMenus.exists_annihilating_form_two (T.U 1)
    (r.1 0 : F) (r.1 0 : F) hr hr
  have hlann : l ∈ (T.U 1).dualAnnihilator :=
    (Submodule.mem_dualAnnihilator l).mpr (fun x hx => hU hx)
  refine ⟨⟨l,hlann⟩,fun hz => ?_⟩
  exact hl (LinearMap.congr_fun hz r)

omit [FiniteDimensional K F] in
/-- Joint separation of the two annihilator restriction families follows
from the original pairwise side and triple/side disjointness. -/
theorem forms_jointly_separate (T : Task K F)
    (hpair : T.A 0 ⊓ T.A 1=⊥)
    (htriple : (T.U 0 ⊓ T.U 1 ⊓ T.U 2) ⊓ T.A 2=⊥)
    (r : Relation T) (hl : ∀ l, leftForm T l r=0) (hr : ∀ l, rightForm T l r=0) :
    r=0 := by
  have h1 : (r.1 1 : F) ∈ T.U 0 :=
    (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (T.U 0) (r.1 1 : F)).mp
      (fun l h => hl ⟨l,h⟩)
  have h0 : (r.1 0 : F) ∈ T.U 1 :=
    (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (T.U 1) (r.1 0 : F)).mp
      (fun l h => hr ⟨l,h⟩)
  have hrel := relation_sum_eq_zero T.A r
  have he2 : (r.1 2 : F) = -((r.1 0 : F)+(r.1 1 : F)) := eq_neg_of_add_eq_zero_right hrel
  have h20 : (r.1 2 : F) ∈ T.U 0 := by
    rw [he2]; exact (T.U 0).neg_mem ((T.U 0).add_mem (T.side_le_signal 0 (r.1 0).property) h1)
  have h21 : (r.1 2 : F) ∈ T.U 1 := by
    rw [he2]; exact (T.U 1).neg_mem ((T.U 1).add_mem h0 (T.side_le_signal 1 (r.1 1).property))
  have hz2 : (r.1 2 : F)=0 := by
    have hm : (r.1 2 : F) ∈ (T.U 0 ⊓ T.U 1 ⊓ T.U 2) ⊓ T.A 2 :=
      ⟨⟨⟨h20,h21⟩,T.side_le_signal 2 (r.1 2).property⟩,(r.1 2).property⟩
    simpa only [htriple,Submodule.mem_bot] using hm
  have he0 : (r.1 0 : F)= -(r.1 1 : F) := by
    rw [hz2,add_zero] at hrel
    exact eq_neg_of_add_eq_zero_left hrel
  have hz0 : (r.1 0 : F)=0 := by
    have hm : (r.1 0 : F) ∈ T.A 0 ⊓ T.A 1 :=
      ⟨(r.1 0).property,by rw [he0]; exact (T.A 1).neg_mem (r.1 1).property⟩
    simpa only [hpair,Submodule.mem_bot] using hm
  have hz1 : (r.1 1 : F)=0 := by simpa only [hz0,hz2,zero_add,add_zero] using hrel
  apply Subtype.ext
  funext i
  apply Subtype.ext
  fin_cases i <;> assumption

omit [FiniteDimensional K F] in
/-- The abstract cross determinant is exactly the concrete relation wedge. -/
theorem relationWedge_apply (T : Task K F) (r w : Relation T)
    (l₁ : (T.U 0).dualAnnihilator) (l₂ : (T.U 1).dualAnnihilator) :
    relationWedge T r w l₁ l₂ =
      rightForm T l₂ r * leftForm T l₁ w - rightForm T l₂ w * leftForm T l₁ r := rfl

/-- Every R₂ remote side/signal intersection is a transverse line.
The witness is extracted from the actual original-field indecomposable. -/
theorem full_remote_witness (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T .R2 n)
    (s j k : Three) (hsj : s ≠ j) (hsk : s ≠ k) (hjk : j ≠ k) :
    ∃ v ∈ T.A j ⊓ T.U k, v ∉ T.U s := by
  have hh := full_side_signal_dimension T hT .R2 n hn h k j hjk.symm
  have ha (i : Three) : fullSide .R2 n i=n+1 := by fin_cases i <;> rfl
  have hu (i : Three) : fullSignal .R2 n i=2*n+1 := by fin_cases i <;> rfl
  rw [ha,hu,h.ambient] at hh
  simp only [fullAmbient] at hh
  have hdim : finrank K ↥(T.A j ⊓ T.U k)=1 := by omega
  have hbot : (T.U 0 ⊓ T.U 1 ⊓ T.U 2) ⊓ T.A j=⊥ :=
    Submodule.finrank_eq_zero.mp (full_side_triple_dimension T hT .R2 n hn h j)
  have hdis : Disjoint (T.A j ⊓ T.U k) (T.U s) := by
    apply Submodule.disjoint_def.mpr
    intro v hv hvs
    have ht : v ∈ (T.U s ⊓ T.U j) ⊓ T.U k :=
      ⟨⟨hvs,T.side_le_signal j hv.1⟩,hv.2⟩
    rw [triple_inf_eq T s j k hsj hsk hjk] at ht
    have hz : v ∈ (T.U 0 ⊓ T.U 1 ⊓ T.U 2) ⊓ T.A j := ⟨ht,hv.1⟩
    simpa only [hbot,Submodule.mem_bot] using hz
  have hnC : T.A j ⊓ T.U k ≠ ⊥ := by
    intro hz
    have hc0 : finrank K ↥(T.A j ⊓ T.U k)=0 := by rw [hz]; exact finrank_bot K F
    omega
  exact SetLike.not_le_iff_exists.mp (fun hle => hnC (hdis.eq_bot_of_le hle))

/-- The relation determinant is genuinely nonzero for every original-field
R₂ indecomposable, derived from its defining dimensions and actual Hom ranks. -/
theorem full_relationWedge_nonzero (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T .R2 n) :
    ∃ r w : Relation T, relationWedge T r w ≠ 0 := by
  have hd : finrank K (Relation T)=2 := by
    simpa [Relation,codimension] using
      NonzeroRelationRestrictions.full_relation_dimension T hT .R2 n hn h
  have hinj (i : Three) : Function.Injective (projection T i) := by
    intro r w he
    apply NonzeroRelationRestrictions.full_relation_projection_injective T hT .R2 n hn h i
    exact Subtype.ext he
  have hC₁ := full_side_signal_dimension T hT .R2 n hn h 0 1 (by decide)
  have hC₀ := full_side_signal_dimension T hT .R2 n hn h 1 0 (by decide)
  rw [h.ambient] at hC₁ hC₀
  norm_num [fullAmbient,fullSide,fullSignal] at hC₁ hC₀
  have hl := exists_leftForm_nonzero T (exists_projection_outside T 0 1
    (by omega) (hinj 1) (by omega))
  have hr := exists_rightForm_nonzero T (exists_projection_outside T 1 0
    (by omega) (hinj 0) (by omega))
  have hpair := full_side_pair_eq_bot T hT .R2 n hn h 0 1 (by decide)
  have htriple : (T.U 0 ⊓ T.U 1 ⊓ T.U 2) ⊓ T.A 2=⊥ :=
    Submodule.finrank_eq_zero.mp (full_side_triple_dimension T hT .R2 n hn h 2)
  obtain ⟨l₁,l₂,r,w,hw⟩ := TwoDimensionalWedge.exists_cross_wedge (leftForm T) (rightForm T)
    hl hr (forms_jointly_separate T hpair htriple) (by omega)
  refine ⟨r,w,fun hz => hw ?_⟩
  have he := LinearMap.congr_fun (LinearMap.congr_fun hz l₁) l₂
  exact he

/-- Actual scalar binary R₂ relay with the manuscript's e₄+e₅ bound.
The only input is indecomposability and the seven original family dimensions. -/
theorem full_binary_R2_profile (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T .R2 n) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P=3*n-1 ∧
      (∀ r : Fin 6, Profile.entry (inducedTask T P hg) (.inl r) ≤
        Profile.entry T (.inl r)+(if r=3 ∨ r=4 then 1 else 0)) ∧
      (∀ r : Three × Three, Profile.entry (inducedTask T P hg) (.inr r)=Profile.entry T (.inr r)) := by
  obtain ⟨r,w,hw⟩ := full_relationWedge_nonzero T hT n hn h
  obtain ⟨v,hv,hvU⟩ := full_remote_witness T hT n hn h 0 1 2 (by decide) (by decide) (by decide)
  obtain ⟨z,hz,hzU⟩ := full_remote_witness T hT n hn h 1 2 0 (by decide) (by decide) (by decide)
  have hc := full_rankConditions T hT .R2 n hn h
  obtain ⟨P,hg,hf,hd,hfirst,hsecond⟩ := BinaryCodimTwoProfiles.exists_codimTwo_binary_profile
    T (full_spanning T hT .R2 n hn h) r w hw hc.pair_span hc.pair_intersections_span v z hv hz hvU hzU
  refine ⟨P,hg,hf,?_,hfirst,hsecond⟩
  rw [h.ambient] at hd
  simp only [fullAmbient] at hd
  omega

end UploadBroadcast.NonzeroR2Wedge
