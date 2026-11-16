import UploadBroadcast.BinaryExceptionalRelays
import UploadBroadcast.NonzeroRelationRestrictions

/-! Close the three zero-margin scalar exceptions from actual
indecomposability and their seven defining dimensions. -/
namespace UploadBroadcast.NonzeroExceptionalRelays
open Module Profile NonzeroDefectRelays NonzeroDefectProfile NonzeroFamilyRanks
open NonzeroRelationRestrictions BinaryExceptionalRelays
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

def commonDimension : Family → ℕ
  | .T3 => 2
  | _ => 1

/-- The common demand complement of each zero-margin exception is derived
from actual intersection ranks, not supplied as a relay hypothesis. -/
theorem full_common_signal (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (hg : g=.H ∨ g=.R2 ∨ g=.T3) (h : Dimensions T g 1) :
    let S := T.U 0 ⊓ T.U 1 ⊓ T.U 2
    finrank K S=commonDimension g ∧
      (∀ i, Disjoint S (T.A i)) ∧ (∀ i, S ≤ T.U i) ∧
      (∀ i, T.U i=T.A i ⊔ S) := by
  let S := T.U 0 ⊓ T.U 1 ⊓ T.U 2
  have hd := full_signal_triple_dimension T hT g 1 (by decide) h
  rw [h.ambient] at hd
  have hdim : finrank K S=commonDimension g := by
    rcases hg with rfl | rfl | rfl
    · change finrank K S+6=7 at hd
      change finrank K S=1
      omega
    · change finrank K S+8=9 at hd
      change finrank K S=1
      omega
    · change finrank K S+10=12 at hd
      change finrank K S=2
      omega
  have hdis (i : Three) : Disjoint S (T.A i) := by
    exact disjoint_iff.mpr (Submodule.finrank_eq_zero.mp
      (full_side_triple_dimension T hT g 1 (by decide) h i))
  have hSU (i : Three) : S ≤ T.U i := by
    fin_cases i
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
  refine ⟨hdim,hdis,hSU,fun i => ?_⟩
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq (sup_le (T.side_le_signal i) (hSU i))
  have hdims := Submodule.finrank_sup_add_finrank_inf_eq (T.A i) S
  rw [(hdis i).symm.eq_bot,finrank_bot,add_zero,hdim,h.side] at hdims
  rw [h.signal,hdims]
  rcases hg with rfl | rfl | rfl <;> fin_cases i <;> rfl

/-- Every actual H+δ or R₂+δ task has a two-upload scalar relay that
preserves or reduces all fifteen profile entries. -/
theorem full_small_exception_profile [Finite K] (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (hg : g=.H ∨ g=.R2) (h : Dimensions T g 1) :
    ∃ P : Submodule K F, ∃ hlocal : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P=2 ∧
      ∀ r : Profile.Index, entry (inducedTask T P hlocal) r ≤ entry T r := by
  let S := T.U 0 ⊓ T.U 1 ⊓ T.U 2
  obtain ⟨hdim,hdis,hSU,hU⟩ := full_common_signal T hT g
    (hg.elim Or.inl (fun hh => Or.inr (Or.inl hh))) h
  have hd : finrank K S=1 := by
    rcases hg with rfl | rfl <;> exact hdim
  have hnS : S ≠ ⊥ := by intro hz; rw [hz,finrank_bot] at hd; omega
  obtain ⟨t,ht,ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnS
  have hSt : Submodule.span K {t}=S := by
    apply Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (by simpa using ht))
    rw [finrank_span_singleton ht0,hd]
  have htA (i : Three) : t ∉ T.A i := by
    intro hti
    exact ht0 (Submodule.disjoint_def.mp (hdis i) t ht hti)
  let j : Three := if g=.H then 2 else 1
  have hj : (0 : Three) ≠ j := by
    dsimp [j]
    split_ifs <;> decide
  have hpair : Disjoint (T.A 0) (T.A j) :=
    disjoint_iff.mpr (full_side_pair_eq_bot T hT g 1 (by decide) h 0 j hj)
  have hsum : T.A 0 ⊔ T.A j=⊤ := by
    apply Submodule.eq_of_le_of_finrank_eq le_top
    have he := Submodule.finrank_sup_add_finrank_inf_eq (T.A 0) (T.A j)
    rw [hpair.eq_bot,finrank_bot,add_zero,h.side,h.side] at he
    rw [finrank_top,h.ambient,he]
    rcases hg with rfl | rfl
    · norm_num [j,fullSide,fullAmbient]; rfl
    · norm_num [j,fullSide,fullAmbient,show Family.R2 ≠ .H from by decide]
  exact small_exception_profile_preserving T ⊤ g hg
    (by simpa using h.ambient) (full_rankConditions T hT g 1 (by decide) h)
    0 j hpair hsum t (htA 0) (htA j) (by
      intro i
      rw [hSt]
      exact le_of_eq (hU i))

/-- Every actual T₃+δ task has its four-upload scalar relay with no
increased profile entry; the common plane and transverse arm are derived. -/
theorem full_tripod_exception_profile [Finite K] (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (h : Dimensions T .T3 1) :
    ∃ P : Submodule K F, ∃ hlocal : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P=4 ∧
      ∀ r : Profile.Index, entry (inducedTask T P hlocal) r ≤ entry T r := by
  obtain ⟨hdim,hdis,hSU,hU⟩ := full_common_signal T hT .T3 (Or.inr (Or.inr rfl)) h
  let R := LinearMap.ker (AlignedRelation.signalSum T.A)
  have hrank : finrank K R=1 := by
    simpa [R,codimension,show Family.T3 ≠ .R2 from by decide] using
      full_relation_dimension T hT .T3 1 (by decide) h
  haveI : Nontrivial R := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank K R)
  obtain ⟨r,hr⟩ := exists_ne (0 : R)
  have hb : (r.1 1 : F) ≠ 0 := by
    intro hb
    apply hr
    apply full_relation_projection_injective T hT .T3 1 (by decide) h 1
    apply Subtype.ext
    exact hb
  exact tripod_exception_profile_preserving T (full_spanning T hT .T3 1 (by decide) h)
    (full_rankConditions T hT .T3 1 (by decide) h)
    (r.1 0 : F) (r.1 1 : F) (r.1 2 : F) (r.1 0).property (r.1 1).property (r.1 2).property
    (relation_sum_eq_zero T.A r) hb (hdis 1)
    (by simpa [fullAmbient] using h.ambient) _ hdim hSU (fun i => le_of_eq (hU i))

end UploadBroadcast.NonzeroExceptionalRelays
