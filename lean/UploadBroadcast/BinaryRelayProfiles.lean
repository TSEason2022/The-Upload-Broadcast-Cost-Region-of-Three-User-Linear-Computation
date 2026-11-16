import UploadBroadcast.BinaryRelayMenus

/-! Exact profile transport for binary hyperplane relays. The bounds come
from ranks of actual restrictions, not from a hypothesized output menu. -/
namespace UploadBroadcast.BinaryRelayProfiles
open Module Profile NonzeroDefectRelays BinaryRelayMenus
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Cutting commutes with a join when one summand is already in the cut. -/
theorem restrict_sup_of_le (A B P : Submodule K F) (hA : A ≤ P) :
    (A ⊓ P) ⊔ (B ⊓ P) = (A ⊔ B) ⊓ P := by
  rw [inf_eq_left.mpr hA,sup_inf_assoc_of_le B hA]

/-- Cutting commutes with a join if the form is nonzero on its intersection.
The proof explicitly corrects the two summands by their common direction. -/
theorem hyperplane_restrict_sup (A B : Submodule K F) (l : F →ₗ[K] K)
    (h : ∃ v ∈ A ⊓ B, l v ≠ 0) :
    (A ⊓ LinearMap.ker l) ⊔ (B ⊓ LinearMap.ker l) =
      (A ⊔ B) ⊓ LinearMap.ker l := by
  obtain ⟨v,hv,hlv⟩ := h
  apply le_antisymm
  · exact sup_le (inf_le_inf le_sup_left le_rfl) (inf_le_inf le_sup_right le_rfl)
  · intro x hx
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hx.1
    have hx0 : l x=0 := hx.2
    have hab0 : l a+l b=0 := by rw [← map_add,hab,hx0]
    let t := l a/l v
    have ht : t*l v=l a := div_mul_cancel₀ _ hlv
    refine Submodule.mem_sup.mpr ⟨a-t • v,⟨A.sub_mem ha (A.smul_mem _ hv.1),?_⟩,
      b+t • v,⟨B.add_mem hb (B.smul_mem _ hv.2),?_⟩,?_⟩
    · change l (a-t • v)=0
      simp [ht]
    · change l (b+t • v)=0
      simp only [map_add,map_smul,smul_eq_mul,ht]
      linear_combination hab0
    · simpa only [sub_add_add_cancel] using hab

/-- The full pair-spanning property survives the actual hyperplane cut. -/
theorem hyperplane_pair_spans (T : Task K F) (l : F →ₗ[K] K)
    (hU : T.U 0 ≤ LinearMap.ker l)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j = ⊤)
    (hr : ∃ v ∈ T.U 1 ⊓ T.U 2, l v ≠ 0) :
    ∀ i j, i ≠ j → (T.U i ⊓ LinearMap.ker l) ⊔
      (T.U j ⊓ LinearMap.ker l) = LinearMap.ker l := by
  intro i j hij
  have he : (T.U i ⊓ LinearMap.ker l) ⊔ (T.U j ⊓ LinearMap.ker l) =
      (T.U i ⊔ T.U j) ⊓ LinearMap.ker l := by
    fin_cases i <;> fin_cases j <;> try contradiction
    · exact restrict_sup_of_le _ _ _ hU
    · exact restrict_sup_of_le _ _ _ hU
    · simpa only [sup_comm (T.U 0 ⊓ LinearMap.ker l) (T.U 1 ⊓ LinearMap.ker l), sup_comm (T.U 0) (T.U 1)] using restrict_sup_of_le (T.U 0) (T.U 1) _ hU
    · exact hyperplane_restrict_sup _ _ _ hr
    · simpa only [sup_comm (T.U 0 ⊓ LinearMap.ker l) (T.U 2 ⊓ LinearMap.ker l), sup_comm (T.U 0) (T.U 2)] using restrict_sup_of_le (T.U 0) (T.U 2) _ hU
    · simpa only [sup_comm (T.U 1 ⊓ LinearMap.ker l) (T.U 2 ⊓ LinearMap.ker l), sup_comm (T.U 1) (T.U 2)] using hyperplane_restrict_sup _ _ _ hr
  rw [he,hp i j hij,top_inf_eq]

theorem restrict_inf (A B P : Submodule K F) :
    (A ⊓ P) ⊓ (B ⊓ P) = (A ⊓ B) ⊓ P := by
  rw [inf_inf_inf_comm,inf_idem]

/-- The pair-intersection spanning identities also survive restriction:
at least one summand is contained in the distinguished signal space. -/
theorem hyperplane_pair_intersections_span (T : Task K F) (P : Submodule K F)
    (hU : T.U 0 ≤ P)
    (hp : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)=T.U i) :
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ((T.U i ⊓ P) ⊓ (T.U j ⊓ P)) ⊔ ((T.U i ⊓ P) ⊓ (T.U k ⊓ P))=T.U i ⊓ P := by
  intro i j k hij hik hjk
  have hle : T.U i ⊓ T.U j ≤ P ∨ T.U i ⊓ T.U k ≤ P := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
    all_goals first
      | exact Or.inl (inf_le_left.trans hU)
      | exact Or.inl (inf_le_right.trans hU)
      | exact Or.inr (inf_le_left.trans hU)
      | exact Or.inr (inf_le_right.trans hU)
  simp only [restrict_inf]
  rcases hle with hle | hle
  · rw [restrict_sup_of_le _ _ _ hle,hp i j k hij hik hjk]
  · rw [sup_comm,restrict_sup_of_le _ _ _ hle,sup_comm (T.U i ⊓ T.U k),
      hp i j k hij hik hjk]

section Finite
variable [FiniteDimensional K F]

theorem totalDemand_induced (T : Task K F) (P : Submodule K F)
    (hg : T.LocallyGenerated P) (hf : T.RelayFeasible P) :
    totalDemand (inducedTask T P hg)=totalDemand T := by
  unfold totalDemand
  exact Finset.sum_congr rfl (fun i _ => relay_signal_dimension T P hf i)

/-- Under pair spanning, the first-entry change is exactly the conditional
rank lost by its ordered pair. -/
theorem firstEntry_difference (T : Task K F) (P : Submodule K F)
    (hg : T.LocallyGenerated P) (hf : T.RelayFeasible P)
    (i j k : Three) (hp : T.U i ⊔ T.U j=⊤)
    (hp' : (T.U i ⊓ P) ⊔ (T.U j ⊓ P)=P) :
    firstEntry (inducedTask T P hg) i j k - firstEntry T i j k =
      (condRank (T.U i ⊓ T.U j) (T.A j) : ℝ) -
        condRank ((T.U i ⊓ T.U j) ⊓ P) (T.A j ⊓ P) := by
  have hs := relay_condRank (T.A k) (T.U k) P (T.side_le_signal k) (hf k)
  simp only [firstEntry]
  rw [totalDemand_induced T P hg hf]
  simp only [inducedTask,hp,hp',inf_top_eq,inf_right_idem,restrict_inf]
  rw [hs]
  ring

/-- A hyperplane can add at most one to each affected first entry. -/
theorem firstEntry_hyperplane_le (T : Task K F) (l : F →ₗ[K] K)
    (hg : T.LocallyGenerated (LinearMap.ker l)) (hf : T.RelayFeasible (LinearMap.ker l))
    (i j k : Three) (hp : T.U i ⊔ T.U j=⊤)
    (hp' : (T.U i ⊓ LinearMap.ker l) ⊔ (T.U j ⊓ LinearMap.ker l)=LinearMap.ker l) :
    firstEntry (inducedTask T (LinearMap.ker l) hg) i j k ≤ firstEntry T i j k+1 := by
  have hd := firstEntry_difference T (LinearMap.ker l) hg hf i j k hp hp'
  have hr := hyperplane_condRank_loss_le_one (T.A j) (T.U i ⊓ T.U j) l
  have hr' : (condRank (T.U i ⊓ T.U j) (T.A j) : ℝ) ≤
      condRank ((T.U i ⊓ T.U j) ⊓ LinearMap.ker l) (T.A j ⊓ LinearMap.ker l)+1 := by
    exact_mod_cast hr
  linarith

/-- If the pair lies in the relay, its first entry is exactly preserved. -/
theorem firstEntry_unchanged_of_pair_le (T : Task K F) (P : Submodule K F)
    (hg : T.LocallyGenerated P) (hf : T.RelayFeasible P)
    (i j k : Three) (hp : T.U i ⊔ T.U j=⊤)
    (hp' : (T.U i ⊓ P) ⊔ (T.U j ⊓ P)=P) (hle : T.U i ⊓ T.U j ≤ P) :
    firstEntry (inducedTask T P hg) i j k=firstEntry T i j k := by
  have hd := firstEntry_difference T P hg hf i j k hp hp'
  rw [condRank_unchanged_of_le _ _ _ hle] at hd
  linarith

/-- Protecting the side/pair intersection preserves its conditional rank,
so the corresponding first entry cannot increase. -/
theorem firstEntry_unchanged_of_protected_intersection (T : Task K F) (l : F →ₗ[K] K)
    (hg : T.LocallyGenerated (LinearMap.ker l)) (hf : T.RelayFeasible (LinearMap.ker l))
    (i j k : Three) (hp : T.U i ⊔ T.U j=⊤)
    (hp' : (T.U i ⊓ LinearMap.ker l) ⊔ (T.U j ⊓ LinearMap.ker l)=LinearMap.ker l)
    (hC : ∃ v ∈ T.A j ⊓ (T.U i ⊓ T.U j), l v ≠ 0) :
    firstEntry (inducedTask T (LinearMap.ker l) hg) i j k=firstEntry T i j k := by
  have hd := firstEntry_difference T (LinearMap.ker l) hg hf i j k hp hp'
  have h₁ := hyperplane_intersection_finrank (T.U i ⊓ T.U j) l
    (by obtain ⟨v,hv,hlv⟩ := hC; exact ⟨v,hv.2,hlv⟩)
  have h₂ := hyperplane_intersection_finrank (T.A j ⊓ (T.U i ⊓ T.U j)) l hC
  have h₃ := condRank_add_intersection (T.U i ⊓ T.U j) (T.A j)
  have h₄ := condRank_add_intersection ((T.U i ⊓ T.U j) ⊓ LinearMap.ker l)
    (T.A j ⊓ LinearMap.ker l)
  rw [inf_inf_inf_comm,inf_idem] at h₄
  have he : condRank ((T.U i ⊓ T.U j) ⊓ LinearMap.ker l)
      (T.A j ⊓ LinearMap.ker l)=condRank (T.U i ⊓ T.U j) (T.A j) := by omega
  rw [he] at hd
  linarith

/-- All nine second entries are preserved by the binary hyperplane
construction once the original pair and pair-intersection spans hold. -/
theorem secondEntry_hyperplane (T : Task K F) (l : F →ₗ[K] K)
    (hg : T.LocallyGenerated (LinearMap.ker l)) (hf : T.RelayFeasible (LinearMap.ker l))
    (hU : T.U 0 ≤ LinearMap.ker l)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j=⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)=T.U i)
    (hr : ∃ v ∈ T.U 1 ⊓ T.U 2, l v ≠ 0)
    (i j k ell : Three) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    secondEntry (inducedTask T (LinearMap.ker l) hg) i j k ell=secondEntry T i j k ell := by
  have hp' := hyperplane_pair_spans T l hU hp hr
  have hi' := hyperplane_pair_intersections_span T (LinearMap.ker l) hU hi
  have ht : T.U 0 ⊓ T.U 1 ⊓ T.U 2 ≤ LinearMap.ker l :=
    inf_le_left.trans (inf_le_left.trans hU)
  have htr := condRank_unchanged_of_le (T.A ell) _ _ ht
  have hsi := relay_condRank (T.A i) (T.U i) _ (T.side_le_signal i) (hf i)
  have hsj := relay_condRank (T.A j) (T.U j) _ (T.side_le_signal j) (hf j)
  have hsk := relay_condRank (T.A k) (T.U k) _ (T.side_le_signal k) (hf k)
  simp only [secondEntry]
  rw [totalDemand_induced T _ hg hf]
  simp only [inducedTask]
  rw [hi' i j k hij hik hjk,hi i j k hij hik hjk,
    hp' i k hik,hp' i j hij,hp i k hik,hp i j hij]
  simp only [inf_top_eq,inf_right_idem,restrict_inf,htr,hsi,hsj,hsk]

/-- The canonical protected-line binary hyperplane changes at most F₂₃₁,
with every other first entry fixed and all nine second entries fixed. -/
theorem protected_hyperplane_profile_bound (T : Task K F) (l : F →ₗ[K] K)
    (hg : T.LocallyGenerated (LinearMap.ker l)) (hf : T.RelayFeasible (LinearMap.ker l))
    (hU : T.U 0 ≤ LinearMap.ker l)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j=⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)=T.U i)
    (hC : ∃ v ∈ T.A 1 ⊓ (T.U 1 ⊓ T.U 2), l v ≠ 0) :
    (∀ r : Fin 6, entry (inducedTask T (LinearMap.ker l) hg) (.inl r) ≤
      entry T (.inl r)+(if r=3 then 1 else 0)) ∧
    (∀ r : Three × Three, entry (inducedTask T (LinearMap.ker l) hg) (.inr r)=entry T (.inr r)) := by
  have hr : ∃ v ∈ T.U 1 ⊓ T.U 2, l v ≠ 0 := by
    obtain ⟨v,hv,hlv⟩ := hC; exact ⟨v,hv.2,hlv⟩
  have hp' := hyperplane_pair_spans T l hU hp hr
  have hfix (i j k : Three) (hij : i ≠ j) (hle : T.U i ⊓ T.U j ≤ LinearMap.ker l) :=
    firstEntry_unchanged_of_pair_le T _ hg hf i j k (hp i j hij) (hp' i j hij) hle
  have h01 := hfix 0 1 2 (by decide) (inf_le_left.trans hU)
  have h02 := hfix 0 2 1 (by decide) (inf_le_left.trans hU)
  have h10 := hfix 1 0 2 (by decide) (inf_le_right.trans hU)
  have h20 := hfix 2 0 1 (by decide) (inf_le_right.trans hU)
  have h12 := firstEntry_hyperplane_le T l hg hf 1 2 0 (hp 1 2 (by decide)) (hp' 1 2 (by decide))
  have h21 := firstEntry_unchanged_of_protected_intersection T l hg hf 2 1 0
    (hp 2 1 (by decide)) (hp' 2 1 (by decide)) (by simpa only [inf_comm (T.U 1) (T.U 2)] using hC)
  constructor
  · intro r
    fin_cases r <;> simp [entry,firstOrder,h01,h02,h10,h20,h21,h12]
  · rintro ⟨i,ell⟩
    exact secondEntry_hyperplane T l hg hf hU hp hi hr i (i+1) (i+2) ell
      (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)

/-- A transverse nonzero protected remote intersection supplies the actual
scalar e₄ relay, including local generation, dimension, and all fifteen bounds. -/
theorem exists_protected_binary_profile (T : Task K F) (hspan : T.Spanning)
    (a b c : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a+b+c=0) (hbU : b ∉ T.U 0)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j=⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)=T.U i)
    (hC : Disjoint (T.A 1 ⊓ (T.U 1 ⊓ T.U 2)) (T.U 0))
    (hCn : T.A 1 ⊓ (T.U 1 ⊓ T.U 2) ≠ ⊥) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P+1=finrank K F ∧
      (∀ r : Fin 6, entry (inducedTask T P hg) (.inl r) ≤ entry T (.inl r)+(if r=3 then 1 else 0)) ∧
      (∀ r : Three × Three, entry (inducedTask T P hg) (.inr r)=entry T (.inr r)) := by
  have hn : ¬ T.A 1 ⊓ (T.U 1 ⊓ T.U 2) ≤ T.U 0 := fun h => hCn (hC.eq_bot_of_le h)
  obtain ⟨v,hv,hvU⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨l,hU,_,hlv,hg,hf,hd⟩ := exists_binary_hyperplane_relay
    T hspan a b c v ha hb hc hrel hbU hvU
  exact ⟨LinearMap.ker l,hg,hf,hd,protected_hyperplane_profile_bound T l hg hf hU hp hi ⟨v,hv,hlv⟩⟩

/-- With no remote side restriction protected, precisely the two remote
first entries can increase, each by at most one. -/
theorem double_hyperplane_profile_bound (T : Task K F) (l : F →ₗ[K] K)
    (hg : T.LocallyGenerated (LinearMap.ker l)) (hf : T.RelayFeasible (LinearMap.ker l))
    (hU : T.U 0 ≤ LinearMap.ker l)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j=⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)=T.U i)
    (hr : ∃ v ∈ T.U 1 ⊓ T.U 2, l v ≠ 0) :
    (∀ r : Fin 6, entry (inducedTask T (LinearMap.ker l) hg) (.inl r) ≤
      entry T (.inl r)+(if r=3 ∨ r=5 then 1 else 0)) ∧
    (∀ r : Three × Three, entry (inducedTask T (LinearMap.ker l) hg) (.inr r)=entry T (.inr r)) := by
  have hp' := hyperplane_pair_spans T l hU hp hr
  have hfix (i j k : Three) (hij : i ≠ j) (hle : T.U i ⊓ T.U j ≤ LinearMap.ker l) :=
    firstEntry_unchanged_of_pair_le T _ hg hf i j k (hp i j hij) (hp' i j hij) hle
  have h01 := hfix 0 1 2 (by decide) (inf_le_left.trans hU)
  have h02 := hfix 0 2 1 (by decide) (inf_le_left.trans hU)
  have h10 := hfix 1 0 2 (by decide) (inf_le_right.trans hU)
  have h20 := hfix 2 0 1 (by decide) (inf_le_right.trans hU)
  have h12 := firstEntry_hyperplane_le T l hg hf 1 2 0 (hp 1 2 (by decide)) (hp' 1 2 (by decide))
  have h21 := firstEntry_hyperplane_le T l hg hf 2 1 0 (hp 2 1 (by decide)) (hp' 2 1 (by decide))
  constructor
  · intro r
    fin_cases r <;> simp [entry,firstOrder,h01,h02,h10,h20,h21,h12]
  · rintro ⟨i,ell⟩
    exact secondEntry_hyperplane T l hg hf hU hp hi hr i (i+1) (i+2) ell
      (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)

/-- Actual two-coordinate hyperplane menu construction, covering the double
choices of R₀ and O after user relabeling. -/
theorem exists_double_binary_profile (T : Task K F) (hspan : T.Spanning)
    (a b c : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a+b+c=0) (hbU : b ∉ T.U 0)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j=⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)=T.U i)
    (hr : ¬ T.U 1 ⊓ T.U 2 ≤ T.U 0) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P+1=finrank K F ∧
      (∀ r : Fin 6, entry (inducedTask T P hg) (.inl r) ≤ entry T (.inl r)+(if r=3 ∨ r=5 then 1 else 0)) ∧
      (∀ r : Three × Three, entry (inducedTask T P hg) (.inr r)=entry T (.inr r)) := by
  obtain ⟨v,hv,hvU⟩ := SetLike.not_le_iff_exists.mp hr
  obtain ⟨l,hU,_,hlv,hg,hf,hd⟩ := exists_binary_hyperplane_relay
    T hspan a b c v ha hb hc hrel hbU hvU
  exact ⟨LinearMap.ker l,hg,hf,hd,double_hyperplane_profile_bound T l hg hf hU hp hi ⟨v,hv,hlv⟩⟩

omit [FiniteDimensional K F] in
/-- Reindexing the actual induced task commutes with restricting to a relay. -/
theorem inducedTask_reindex (T : Task K F) (p : Equiv.Perm Three)
    (P : Submodule K F) (hg : T.LocallyGenerated P) :
    inducedTask (reindexTask p T) P ((reindex_locallyGenerated T p P).mpr hg) =
      reindexTask p (inducedTask T P hg) := rfl

/-- Exact first-entry user-permutation transport for the constructed relay. -/
theorem firstEntry_induced_reindex (T : Task K F) (p : Equiv.Perm Three)
    (P : Submodule K F) (hg : T.LocallyGenerated P) (i j k : Three) :
    firstEntry (inducedTask (reindexTask p T) P ((reindex_locallyGenerated T p P).mpr hg)) i j k =
      firstEntry (inducedTask T P hg) (p i) (p j) (p k) := by
  rw [inducedTask_reindex,firstEntry_reindexTask]

end Finite
end UploadBroadcast.BinaryRelayProfiles
