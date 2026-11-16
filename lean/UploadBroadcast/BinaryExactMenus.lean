import UploadBroadcast.NonzeroBinaryMenus

/-! Exact original binary menu increments, stronger than coordinatewise bounds. -/
namespace UploadBroadcast.BinaryExactMenus
open Module Profile NonzeroDefectRelays BinaryRelayMenus BinaryRelayProfiles
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

theorem firstEntry_hyperplane_eq_add_one (T : Task K F) (l : F →ₗ[K] K)
    (hg : T.LocallyGenerated (LinearMap.ker l)) (hf : T.RelayFeasible (LinearMap.ker l))
    (i j k : Three) (hp : T.U i ⊔ T.U j=⊤)
    (hp' : (T.U i ⊓ LinearMap.ker l) ⊔ (T.U j ⊓ LinearMap.ker l)=LinearMap.ker l)
    (hz : T.A j ⊓ (T.U i ⊓ T.U j)=⊥)
    (hr : ∃ v ∈ T.U i ⊓ T.U j, l v ≠ 0) :
    firstEntry (inducedTask T (LinearMap.ker l) hg) i j k=firstEntry T i j k+1 := by
  have hd := firstEntry_difference T (LinearMap.ker l) hg hf i j k hp hp'
  have h₁ := hyperplane_intersection_finrank (T.U i ⊓ T.U j) l hr
  have h₂ := condRank_add_intersection (T.U i ⊓ T.U j) (T.A j)
  have h₃ := condRank_add_intersection ((T.U i ⊓ T.U j) ⊓ LinearMap.ker l)
    (T.A j ⊓ LinearMap.ker l)
  rw [hz,finrank_bot,add_zero] at h₂
  rw [inf_inf_inf_comm,inf_idem,hz,bot_inf_eq,finrank_bot,add_zero] at h₃
  have hnat : condRank ((T.U i ⊓ T.U j) ⊓ LinearMap.ker l)
      (T.A j ⊓ LinearMap.ker l)+1=condRank (T.U i ⊓ T.U j) (T.A j) := by omega
  have hreal : (condRank ((T.U i ⊓ T.U j) ⊓ LinearMap.ker l)
      (T.A j ⊓ LinearMap.ker l):ℝ)+1=condRank (T.U i ⊓ T.U j) (T.A j) := by exact_mod_cast hnat
  linarith

theorem protected_hyperplane_profile_exact (T : Task K F) (l : F →ₗ[K] K)
    (hg : T.LocallyGenerated (LinearMap.ker l)) (hf : T.RelayFeasible (LinearMap.ker l))
    (hU : T.U 0 ≤ LinearMap.ker l)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j=⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)=T.U i)
    (hC : ∃ v ∈ T.A 1 ⊓ (T.U 1 ⊓ T.U 2), l v ≠ 0)
    (hz : T.A 2 ⊓ (T.U 1 ⊓ T.U 2)=⊥) :
    (∀ r : Fin 6, entry (inducedTask T (LinearMap.ker l) hg) (.inl r) =
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
  have h12 := firstEntry_hyperplane_eq_add_one T l hg hf 1 2 0 (hp 1 2 (by decide)) (hp' 1 2 (by decide)) hz hr
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
theorem exists_protected_binary_profile_exact (T : Task K F) (hspan : T.Spanning)
    (a b c : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a+b+c=0) (hbU : b ∉ T.U 0)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j=⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)=T.U i)
    (hC : Disjoint (T.A 1 ⊓ (T.U 1 ⊓ T.U 2)) (T.U 0))
    (hCn : T.A 1 ⊓ (T.U 1 ⊓ T.U 2) ≠ ⊥)
    (hz : T.A 2 ⊓ (T.U 1 ⊓ T.U 2)=⊥) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P+1=finrank K F ∧
      (∀ r : Fin 6, entry (inducedTask T P hg) (.inl r) = entry T (.inl r)+(if r=3 then 1 else 0)) ∧
      (∀ r : Three × Three, entry (inducedTask T P hg) (.inr r)=entry T (.inr r)) := by
  have hn : ¬ T.A 1 ⊓ (T.U 1 ⊓ T.U 2) ≤ T.U 0 := fun h => hCn (hC.eq_bot_of_le h)
  obtain ⟨v,hv,hvU⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨l,hU,_,hlv,hg,hf,hd⟩ := exists_binary_hyperplane_relay
    T hspan a b c v ha hb hc hrel hbU hvU
  exact ⟨LinearMap.ker l,hg,hf,hd,protected_hyperplane_profile_exact T l hg hf hU hp hi ⟨v,hv,hlv⟩ hz⟩

/-- With no remote side restriction protected, precisely the two remote
first entries can increase, each by at most one. -/
theorem double_hyperplane_profile_exact (T : Task K F) (l : F →ₗ[K] K)
    (hg : T.LocallyGenerated (LinearMap.ker l)) (hf : T.RelayFeasible (LinearMap.ker l))
    (hU : T.U 0 ≤ LinearMap.ker l)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j=⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)=T.U i)
    (hr : ∃ v ∈ T.U 1 ⊓ T.U 2, l v ≠ 0)
    (hz : ∀ j : Three, j=1 ∨ j=2 → T.A j ⊓ (T.U 1 ⊓ T.U 2)=⊥) :
    (∀ r : Fin 6, entry (inducedTask T (LinearMap.ker l) hg) (.inl r) =
      entry T (.inl r)+(if r=3 ∨ r=5 then 1 else 0)) ∧
    (∀ r : Three × Three, entry (inducedTask T (LinearMap.ker l) hg) (.inr r)=entry T (.inr r)) := by
  have hp' := hyperplane_pair_spans T l hU hp hr
  have hfix (i j k : Three) (hij : i ≠ j) (hle : T.U i ⊓ T.U j ≤ LinearMap.ker l) :=
    firstEntry_unchanged_of_pair_le T _ hg hf i j k (hp i j hij) (hp' i j hij) hle
  have h01 := hfix 0 1 2 (by decide) (inf_le_left.trans hU)
  have h02 := hfix 0 2 1 (by decide) (inf_le_left.trans hU)
  have h10 := hfix 1 0 2 (by decide) (inf_le_right.trans hU)
  have h20 := hfix 2 0 1 (by decide) (inf_le_right.trans hU)
  have h12 := firstEntry_hyperplane_eq_add_one T l hg hf 1 2 0 (hp 1 2 (by decide)) (hp' 1 2 (by decide)) (hz 2 (Or.inr rfl)) hr
  have h21 := firstEntry_hyperplane_eq_add_one T l hg hf 2 1 0 (hp 2 1 (by decide)) (hp' 2 1 (by decide))
    (by simpa only [inf_comm (T.U 1) (T.U 2)] using hz 1 (Or.inl rfl))
    (by simpa only [inf_comm (T.U 1) (T.U 2)] using hr)
  constructor
  · intro r
    fin_cases r <;> simp [entry,firstOrder,h01,h02,h10,h20,h21,h12]
  · rintro ⟨i,ell⟩
    exact secondEntry_hyperplane T l hg hf hU hp hi hr i (i+1) (i+2) ell
      (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)

/-- Actual two-coordinate hyperplane menu construction, covering the double
choices of R₀ and O after user relabeling. -/
theorem exists_double_binary_profile_exact (T : Task K F) (hspan : T.Spanning)
    (a b c : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a+b+c=0) (hbU : b ∉ T.U 0)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j=⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)=T.U i)
    (hr : ¬ T.U 1 ⊓ T.U 2 ≤ T.U 0)
    (hz : ∀ j : Three, j=1 ∨ j=2 → T.A j ⊓ (T.U 1 ⊓ T.U 2)=⊥) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P+1=finrank K F ∧
      (∀ r : Fin 6, entry (inducedTask T P hg) (.inl r) = entry T (.inl r)+(if r=3 ∨ r=5 then 1 else 0)) ∧
      (∀ r : Three × Three, entry (inducedTask T P hg) (.inr r)=entry T (.inr r)) := by
  obtain ⟨v,hv,hvU⟩ := SetLike.not_le_iff_exists.mp hr
  obtain ⟨l,hU,_,hlv,hg,hf,hd⟩ := exists_binary_hyperplane_relay
    T hspan a b c v ha hb hc hrel hbU hvU
  exact ⟨LinearMap.ker l,hg,hf,hd,double_hyperplane_profile_exact T l hg hf hU hp hi ⟨v,hv,hlv⟩ hz⟩


end UploadBroadcast.BinaryExactMenus
