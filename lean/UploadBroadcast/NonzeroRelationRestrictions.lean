import UploadBroadcast.NonzeroFamilyRanks
import UploadBroadcast.TripodSubobjectExclusion
import UploadBroadcast.NonzeroDefectRelays

/-! Actual relation-space transversality for the nonzero-defect families. -/
namespace UploadBroadcast.NonzeroRelationRestrictions
open Module NonzeroFamilyRanks NonzeroDefectProfile QuiverRepresentation
open TripodSubobjectExclusion E6Reflection

variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

lemma euler_tripodEnlargement (d : E6Vertex → ℤ) (i : Three) :
    eulerForm inwardE6 (encode (ResonantTripodTransversality.tripodEnlargementAt i)) d =
      d (.outer 0) + d (.outer 1) + d (.outer 2) + d (.middle i) - 2 * d .center := by
  simp only [eulerForm,NonzeroFamilyRanks.sum_vertices,E6Reflection.sum_edges]
  fin_cases i <;>
    simp [encode,ResonantTripodTransversality.tripodEnlargementAt,inwardE6] <;> ring

/-- An actual enlarged-tripod map vanishes whenever its checked Euler pairing
is nonpositive. -/
theorem tripod_vectors_zero (T : TaskDecomposition.Task K F)
    (hT : TaskDecomposition.Indecomposable T.spaces ⊤)
    (hd : 0 < ReflectionReduction.defect T.dimensionVector) (i : Three)
    (hrank : finrank K (T.A 0) + finrank K (T.A 1) + finrank K (T.A 2) +
      finrank K (T.U i) ≤ 2 * finrank K F)
    (v r : F) (hv : v ∈ T.A 0) (hr : r ∈ T.A 1) (hc : r-v ∈ T.A 2)
    (huv : v ∈ T.U i) (hur : r ∈ T.U i) : v=0 ∧ r=0 := by
  have hh := hom_finrank_eq_max_euler_of_positive_defect (enlargement K i).toRep T.toRep
    ((enlargement K i).rep_indec_of_indec (enlargement_indecomposable K i))
    (T.rep_indec_of_indec hT) hd
  rw [enlargement_rep_dimension,euler_tripodEnlargement] at hh
  change (finrank K (Hom (enlargement K i).toRep T.toRep) : ℤ) =
    max 0 ((finrank K (T.A 0) : ℤ) + finrank K (T.A 1) + finrank K (T.A 2) +
      finrank K (T.U i) - 2 * finrank K F) at hh
  have hzero : finrank K (Hom (enlargement K i).toRep T.toRep) = 0 := by omega
  haveI : Subsingleton (Hom (enlargement K i).toRep T.toRep) := Module.finrank_zero_iff.mp hzero
  let f := (enlargement K i).homOfPreserves T (planeMap K v r)
    (planeMap_preserves K T i v r hv hr hc huv hur)
  have hz : f = Hom.zero _ _ := Subsingleton.elim _ _
  have hcenter := congrArg (fun a : Hom (enlargement K i).toRep T.toRep => a.map .center) hz
  constructor
  · have he := LinearMap.congr_fun hcenter (1,0)
    change (1:K) • v+(0:K) • r=0 at he
    simpa using he
  · have he := LinearMap.congr_fun hcenter (0,1)
    change (0:K) • v+(1:K) • r=0 at he
    simpa using he

omit [FiniteDimensional K F] in
/-- Two members of a three-term relation force the third into the same space. -/
lemma relation_all_mem (U : Submodule K F) (r : Three → F)
    (hrel : r 0 + r 1 + r 2 = 0) (s j : Three) (hsj : s ≠ j)
    (hs : r s ∈ U) (hj : r j ∈ U) : ∀ i, r i ∈ U := by
  have h0 : r 0 = -(r 1+r 2) := eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using hrel)
  have h1 : r 1 = -(r 0+r 2) := eq_neg_of_add_eq_zero_left (by
    calc r 1 + (r 0+r 2) = r 0+r 1+r 2 := by abel
         _ = 0 := hrel)
  have h2 : r 2 = -(r 0+r 1) := eq_neg_of_add_eq_zero_right hrel
  have h0' : r 1 ∈ U → r 2 ∈ U → r 0 ∈ U := by
    intro h1 h2; rw [h0]; exact U.neg_mem (U.add_mem h1 h2)
  have h1' : r 0 ∈ U → r 2 ∈ U → r 1 ∈ U := by
    intro h0 h2; rw [h1]; exact U.neg_mem (U.add_mem h0 h2)
  have h2' : r 0 ∈ U → r 1 ∈ U → r 2 ∈ U := by
    intro h0 h1; rw [h2]; exact U.neg_mem (U.add_mem h0 h1)
  clear h0 h1 h2 hrel
  intro i
  fin_cases s <;> fin_cases j <;> fin_cases i <;>
    simp_all only [ne_eq, not_true_eq_false] <;> tauto

/-- No nonzero relation has a remote projection in the distinguished signal
space when the enlarged-tripod Euler bound holds. -/
theorem relation_projection_outside (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (hd : 0 < ReflectionReduction.defect (EdgeExtraction.configuration T).dimensionVector)
    (s j : Three) (hsj : s ≠ j)
    (hrank : finrank K (T.A 0) + finrank K (T.A 1) + finrank K (T.A 2) +
      finrank K (T.U s) ≤ 2 * finrank K F)
    (r : LinearMap.ker (AlignedRelation.signalSum T.A)) (hr : r ≠ 0) :
    (r.1 j : F) ∉ T.U s := by
  intro hj
  have hrel := NonzeroDefectRelays.relation_sum_eq_zero T.A r
  have hall := relation_all_mem (T.U s) (fun i => (r.1 i : F)) hrel s j hsj
    (T.side_le_signal s (r.1 s).property) hj
  have hc : -(r.1 1 : F) - (r.1 0 : F) = (r.1 2 : F) := by
    calc _ = -((r.1 0 : F)+(r.1 1 : F)) := by abel
         _ = (r.1 2 : F) := (eq_neg_of_add_eq_zero_right hrel).symm
  have hz := tripod_vectors_zero (EdgeExtraction.configuration T) hT hd s hrank
    (r.1 0 : F) (-(r.1 1 : F)) (r.1 0).property
    ((T.A 1).neg_mem (r.1 1).property) (by rw [hc]; exact (r.1 2).property)
    (hall 0) ((T.U s).neg_mem (hall 1))
  have h0 : (r.1 0 : F) = 0 := hz.1
  have h1 : (r.1 1 : F) = 0 := neg_eq_zero.mp hz.2
  have h2 : (r.1 2 : F) = 0 := by simpa [h0,h1] using hrel
  apply hr
  apply Subtype.ext
  funext i
  apply Subtype.ext
  fin_cases i <;> assumption

/-- Distinguished arms used for the displayed hyperplane family menus. -/
def hyperplaneArm : Family → Three
  | .T1 | .T3 | .O => 1
  | .T2 => 2
  | .R0 | .R1 | .R2 | .H => 0

lemma hyperplane_euler_bound (g : Family) (hg : g ≠ .R2) (n : ℕ) (hn : 1 ≤ n) :
    fullSide g n 0 + fullSide g n 1 + fullSide g n 2 +
      fullSignal g n (hyperplaneArm g) ≤ 2 * fullAmbient g n := by
  cases g <;> simp_all [hyperplaneArm,fullSide,fullSignal,fullAmbient] <;> omega

/-- The required relation restriction is nonzero on the actual original-field
configuration of every codimension-one family. -/
theorem full_relation_projection_outside (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (hg : g ≠ .R2) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n)
    (j : Three) (hj : hyperplaneArm g ≠ j)
    (r : LinearMap.ker (AlignedRelation.signalSum T.A)) (hr : r ≠ 0) :
    (r.1 j : F) ∉ T.U (hyperplaneArm g) := by
  apply relation_projection_outside T hT (h.positive_defect T g n) _ j hj _ r hr
  rw [h.side,h.side,h.side,h.signal,h.ambient]
  exact hyperplane_euler_bound g hg n hn

omit [FiniteDimensional K F] in
/-- The sum map has the actual side-space span as its image. -/
theorem relation_sum_range (A : Three → Submodule K F) :
    LinearMap.range (AlignedRelation.signalSum A) = ⨆ i, A i := by
  classical
  apply le_antisymm
  · rintro x ⟨r,rfl⟩
    change (∑ i, (r i : F)) ∈ ⨆ i, A i
    exact Submodule.sum_mem _ (fun i _ => (le_iSup A i) (r i).property)
  · apply iSup_le
    intro i x hx
    refine ⟨Pi.single i ⟨x,hx⟩,?_⟩
    simp only [AlignedRelation.signalSum, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.subtype_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp

/-- Relation-space dimension is exactly the family excess, one or two. -/
theorem full_relation_dimension (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) :
    finrank K (LinearMap.ker (AlignedRelation.signalSum T.A)) = codimension g := by
  have hh := (AlignedRelation.signalSum T.A).finrank_range_add_finrank_ker
  rw [relation_sum_range,full_spanning T hT g n hn h,finrank_top,Module.finrank_pi_fintype] at hh
  simp only [Fin.sum_univ_succ, Fin.val_zero,Fin.val_succ,Fin.mk_one,Fin.mk_zero,
    Fin.sum_univ_zero, add_zero] at hh
  rw [h.side,h.side,h.side,h.ambient] at hh
  cases g <;> simp_all [fullSide,fullAmbient,codimension] <;> omega

/-- Coordinate projection on the genuine relation kernel. -/
def relationProjection (A : Three → Submodule K F) (i : Three) :
    LinearMap.ker (AlignedRelation.signalSum A) →ₗ[K] A i :=
  (LinearMap.proj i).comp (LinearMap.ker (AlignedRelation.signalSum A)).subtype

omit [FiniteDimensional K F] in
/-- Pairwise disjoint side spaces make every relation projection injective. -/
theorem relation_projection_injective (A : Three → Submodule K F)
    (hA : ∀ i j, i ≠ j → A i ⊓ A j = ⊥) (i : Three) :
    Function.Injective (relationProjection A i) := by
  have hzero (r : LinearMap.ker (AlignedRelation.signalSum A))
      (hr : relationProjection A i r = 0) : r = 0 := by
    have hp : (r.1 i : F) = 0 := congrArg Subtype.val hr
    have hrel := NonzeroDefectRelays.relation_sum_eq_zero A r
    have hz : (r.1 0 : F)=0 ∧ (r.1 1 : F)=0 ∧ (r.1 2 : F)=0 := by
      fin_cases i
      · change (r.1 0 : F) = 0 at hp
        have he : (r.1 1 : F) = -(r.1 2 : F) := by
          simpa [hp] using eq_neg_of_add_eq_zero_left (by simpa [hp] using hrel)
        have hb : (r.1 1 : F) ∈ A 1 ⊓ A 2 :=
          ⟨(r.1 1).property,by rw [he]; exact (A 2).neg_mem (r.1 2).property⟩
        rw [hA 1 2 (by decide)] at hb
        change (r.1 1 : F) = 0 at hb
        have hc : (r.1 2 : F)=0 := by simpa [hp,hb] using hrel
        exact ⟨hp,hb,hc⟩
      · change (r.1 1 : F) = 0 at hp
        have he : (r.1 0 : F) = -(r.1 2 : F) := by
          simpa [hp] using eq_neg_of_add_eq_zero_left (by simpa [hp] using hrel)
        have ha : (r.1 0 : F) ∈ A 0 ⊓ A 2 :=
          ⟨(r.1 0).property,by rw [he]; exact (A 2).neg_mem (r.1 2).property⟩
        rw [hA 0 2 (by decide)] at ha
        change (r.1 0 : F) = 0 at ha
        have hc : (r.1 2 : F)=0 := by simpa [hp,ha] using hrel
        exact ⟨ha,hp,hc⟩
      · change (r.1 2 : F) = 0 at hp
        have he : (r.1 0 : F) = -(r.1 1 : F) := by
          simpa [hp] using eq_neg_of_add_eq_zero_left (by simpa [hp] using hrel)
        have ha : (r.1 0 : F) ∈ A 0 ⊓ A 1 :=
          ⟨(r.1 0).property,by rw [he]; exact (A 1).neg_mem (r.1 1).property⟩
        rw [hA 0 1 (by decide)] at ha
        change (r.1 0 : F) = 0 at ha
        have hb : (r.1 1 : F)=0 := by simpa [hp,ha] using hrel
        exact ⟨ha,hb,hp⟩
    apply Subtype.ext
    funext j
    apply Subtype.ext
    fin_cases j
    · exact hz.1
    · exact hz.2.1
    · exact hz.2.2
  intro r w he
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub,he,sub_self]

theorem full_relation_projection_injective (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) (i : Three) :
    Function.Injective (relationProjection T.A i) :=
  relation_projection_injective T.A (full_side_pair_eq_bot T hT g n hn h) i

theorem full_side_triple_eq_bot (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) (i : Three) :
    (T.U 0 ⊓ T.U 1 ⊓ T.U 2) ⊓ T.A i = ⊥ :=
  Submodule.finrank_eq_zero.mp (full_side_triple_dimension T hT g n hn h i)

/-- Every remote side-pair intersection is transverse to the distinguished
signal, since its further intersection lies in the common triple space. -/
theorem full_remote_disjoint (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n)
    (s i j ell : Three) (hsi : s ≠ i) (hsj : s ≠ j) (hij : i ≠ j) :
    Disjoint (T.A ell ⊓ (T.U i ⊓ T.U j)) (T.U s) := by
  apply disjoint_iff.mpr
  apply bot_unique
  intro x hx
  have hm : x ∈ ((T.U s ⊓ T.U i) ⊓ T.U j) ⊓ T.A ell :=
    ⟨⟨⟨hx.2,hx.1.2.1⟩,hx.1.2.2⟩,hx.1.1⟩
  rw [triple_inf_eq T s i j hsi hsj hij,full_side_triple_eq_bot T hT g n hn h ell] at hm
  exact hm

/-- A proper distinguished signal cannot contain the remote pair intersection. -/
theorem full_remote_not_le (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n)
    (s i j : Three) (hsi : s ≠ i) (hsj : s ≠ j) (hij : i ≠ j)
    (hproper : fullSignal g n s < fullAmbient g n) :
    ¬ T.U i ⊓ T.U j ≤ T.U s := by
  intro hle
  have he := congrArg (fun S : Submodule K F => finrank K S) (inf_eq_left.mpr hle)
  rw [triple_inf_eq T i j s hij hsi.symm hsj.symm] at he
  dsimp only at he
  have hp := full_signal_pair_dimension T hT g n hn h i j hij
  have ht := full_signal_triple_dimension T hT g n hn h
  have hs : fullSignal g n 0 + fullSignal g n 1 + fullSignal g n 2 =
      fullSignal g n i + fullSignal g n j + fullSignal g n s := by
    simpa [Fin.sum_univ_succ, add_assoc] using
      sum_three_perm (fullSignal g n) i j s hij hsi.symm hsj.symm
  rw [h.ambient] at hp ht
  omega

lemma hyperplane_signal_lt (g : Family) (hg : g ≠ .R2) (n : ℕ) (hn : 1 ≤ n) :
    fullSignal g n (hyperplaneArm g) < fullAmbient g n := by
  cases g <;> simp_all [hyperplaneArm,fullSignal,fullAmbient] <;> omega

omit [FiniteDimensional K F] in
lemma relation_sum_permuted (A : Three → Submodule K F)
    (r : LinearMap.ker (AlignedRelation.signalSum A)) (p : Equiv.Perm Three) :
    (r.1 (p 0) : F) + (r.1 (p 1) : F) + (r.1 (p 2) : F) = 0 := by
  have he := Equiv.sum_comp p (fun i => (r.1 i : F))
  have hr := NonzeroDefectRelays.relation_sum_eq_zero A r
  simpa [Fin.sum_univ_succ, add_assoc] using he.trans (by simpa [Fin.sum_univ_succ,add_assoc] using hr)

/-- Finite-field hyperplane relay existence, with both remote conditional
ranks selected simultaneously on the actual classified family. -/
theorem exists_full_hyperplane_with_remote_ranks [Fintype K]
    (hq : 3 ≤ Fintype.card K) (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (hg : g ≠ .R2) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n)
    (p : Equiv.Perm Three) (hp : p 0 = hyperplaneArm g) :
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
  have hb := full_relation_projection_outside T hT g hg n hn h (p 1) (by rwa [←hp]) r hr
  rw [←hp] at hb
  have hspan : (Profile.reindexTask p T).Spanning := by
    simpa only [Task.Spanning,Profile.reindexTask,Equiv.iSup_comp p] using full_spanning T hT g n hn h
  have hremote := full_remote_not_le T hT g n hn h (p 0) (p 1) (p 2) h01 h02 h12
    (by rw [hp]; exact hyperplane_signal_lt g hg n hn)
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

end UploadBroadcast.NonzeroRelationRestrictions
