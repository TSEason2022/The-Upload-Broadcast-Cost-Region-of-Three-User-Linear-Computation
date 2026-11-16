import UploadBroadcast.BinaryRelayProfiles

/-! The actual e₄+e₅ profile bound for the binary codimension-two relay.
The only source-specific hypotheses are the original signal spans, the
nonzero relation wedge, and the two protected transverse remote directions. -/
namespace UploadBroadcast.BinaryCodimTwoProfiles
open Module Profile NonzeroDefectRelays BinaryRelayMenus BinaryRelayProfiles
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

theorem cut_pair_spans (U : Three → Submodule K F) (V : Submodule K F)
    (s : Three) (l : F →ₗ[K] K) (hU : U s ≤ LinearMap.ker l)
    (hp : ∀ i j, i ≠ j → U i ⊔ U j=V)
    (hr : ∀ i j, i ≠ j → i ≠ s → j ≠ s → ∃ v ∈ U i ⊓ U j, l v ≠ 0) :
    ∀ i j, i ≠ j → (U i ⊓ LinearMap.ker l) ⊔ (U j ⊓ LinearMap.ker l)=V ⊓ LinearMap.ker l := by
  intro i j hij
  have he : (U i ⊓ LinearMap.ker l) ⊔ (U j ⊓ LinearMap.ker l)=
      (U i ⊔ U j) ⊓ LinearMap.ker l := by
    by_cases his : i=s
    · subst i; exact restrict_sup_of_le _ _ _ hU
    · by_cases hjs : j=s
      · subst j
        simpa only [sup_comm (U s ⊓ LinearMap.ker l) (U i ⊓ LinearMap.ker l),
          sup_comm (U s) (U i)] using restrict_sup_of_le (U s) (U i) _ hU
      · exact hyperplane_restrict_sup _ _ _ (hr i j hij his hjs)
  rw [he,hp i j hij]

theorem cut_pair_intersections_span (U : Three → Submodule K F) (P : Submodule K F)
    (s : Three) (hU : U s ≤ P)
    (hp : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → (U i ⊓ U j) ⊔ (U i ⊓ U k)=U i) :
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ((U i ⊓ P) ⊓ (U j ⊓ P)) ⊔ ((U i ⊓ P) ⊓ (U k ⊓ P))=U i ⊓ P := by
  intro i j k hij hik hjk
  have hs : i=s ∨ j=s ∨ k=s := by
    simp only [Ne,Fin.ext_iff] at hij hik hjk ⊢
    omega
  have hle : U i ⊓ U j ≤ P ∨ U i ⊓ U k ≤ P := by
    rcases hs with rfl | rfl | rfl
    · exact Or.inl (inf_le_left.trans hU)
    · exact Or.inl (inf_le_right.trans hU)
    · exact Or.inr (inf_le_right.trans hU)
  simp only [restrict_inf]
  rcases hle with hle | hle
  · rw [restrict_sup_of_le _ _ _ hle,hp i j k hij hik hjk]
  · rw [sup_comm,restrict_sup_of_le _ _ _ hle,sup_comm (U i ⊓ U k),hp i j k hij hik hjk]

/-- Original pair and pair-intersection spans survive both actual cuts.
The protected directions make the two remote restrictions nonzero. -/
theorem codimTwo_spans (T : Task K F) (l₁ l₂ : F →ₗ[K] K)
    (h₁ : T.U 0 ≤ LinearMap.ker l₁) (h₂ : T.U 1 ≤ LinearMap.ker l₂)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j=⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)=T.U i)
    (v z : F) (hv : v ∈ T.U 1 ⊓ T.U 2) (hz : z ∈ T.U 0 ⊓ T.U 2)
    (hlv : l₁ v ≠ 0) (hlz : l₂ z ≠ 0) :
    let P := LinearMap.ker l₁ ⊓ LinearMap.ker l₂
    (∀ i j, i ≠ j → (T.U i ⊓ P) ⊔ (T.U j ⊓ P)=P) ∧
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ((T.U i ⊓ P) ⊓ (T.U j ⊓ P)) ⊔ ((T.U i ⊓ P) ⊓ (T.U k ⊓ P))=T.U i ⊓ P) := by
  have hp₁ := hyperplane_pair_spans T l₁ h₁ hp ⟨v,hv,hlv⟩
  have hi₁ := cut_pair_intersections_span T.U (LinearMap.ker l₁) 0 h₁ hi
  have hp₂ := cut_pair_spans (fun i => T.U i ⊓ LinearMap.ker l₁)
    (LinearMap.ker l₁) 1 l₂ (inf_le_left.trans h₂) hp₁ (by
      intro i j hij hi0 hj0
      have hzker : z ∈ LinearMap.ker l₁ := h₁ hz.1
      fin_cases i <;> fin_cases j <;> try contradiction
      · exact ⟨z,⟨⟨hz.1,hzker⟩,⟨hz.2,hzker⟩⟩,hlz⟩
      · exact ⟨z,⟨⟨hz.2,hzker⟩,⟨hz.1,hzker⟩⟩,hlz⟩)
  have hi₂ := cut_pair_intersections_span (fun i => T.U i ⊓ LinearMap.ker l₁)
    (LinearMap.ker l₂) 1 (inf_le_left.trans h₂) hi₁
  simpa only [inf_assoc] using And.intro hp₂ hi₂

section Finite
variable [FiniteDimensional K F]

/-- Abstract rank calculation for a feasible relay that preserves the
geometric pair spans and contains the common triple. -/
theorem secondEntry_preserved (T : Task K F) (P : Submodule K F)
    (hg : T.LocallyGenerated P) (hf : T.RelayFeasible P)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j=⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)=T.U i)
    (hp' : ∀ i j, i ≠ j → (T.U i ⊓ P) ⊔ (T.U j ⊓ P)=P)
    (hi' : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ((T.U i ⊓ P) ⊓ (T.U j ⊓ P)) ⊔ ((T.U i ⊓ P) ⊓ (T.U k ⊓ P))=T.U i ⊓ P)
    (ht : T.U 0 ⊓ T.U 1 ⊓ T.U 2 ≤ P)
    (i j k ell : Three) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    secondEntry (inducedTask T P hg) i j k ell=secondEntry T i j k ell := by
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

/-- A protected nonzero side/pair restriction has zero conditional-rank
loss under the actual hyperplane. -/
theorem protected_condRank (A B : Submodule K F) (l : F →ₗ[K] K)
    (hC : ∃ v ∈ A ⊓ B, l v ≠ 0) :
    condRank (B ⊓ LinearMap.ker l) (A ⊓ LinearMap.ker l)=condRank B A := by
  have h₁ := hyperplane_intersection_finrank B l
    (by obtain ⟨v,hv,hlv⟩ := hC; exact ⟨v,hv.2,hlv⟩)
  have h₂ := hyperplane_intersection_finrank (A ⊓ B) l hC
  have h₃ := condRank_add_intersection B A
  have h₄ := condRank_add_intersection (B ⊓ LinearMap.ker l) (A ⊓ LinearMap.ker l)
  rw [restrict_inf] at h₄
  omega

/-- The e₄+e₅ bound, with unchanged other first entries and all second
entries, for an actual codimension-two relay with its two protected lines. -/
theorem codimTwo_profile_bound (T : Task K F) (l₁ l₂ : F →ₗ[K] K)
    (h₁ : T.U 0 ≤ LinearMap.ker l₁) (h₂ : T.U 1 ≤ LinearMap.ker l₂)
    (hg : T.LocallyGenerated (LinearMap.ker l₁ ⊓ LinearMap.ker l₂))
    (hf : T.RelayFeasible (LinearMap.ker l₁ ⊓ LinearMap.ker l₂))
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j=⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)=T.U i)
    (v z : F) (hv : v ∈ T.A 1 ⊓ T.U 2) (hz : z ∈ T.A 2 ⊓ T.U 0)
    (hlv : l₁ v ≠ 0) (hlz : l₂ z ≠ 0) :
    let R := inducedTask T (LinearMap.ker l₁ ⊓ LinearMap.ker l₂) hg
    (∀ r : Fin 6, entry R (.inl r) ≤ entry T (.inl r)+(if r=3 ∨ r=4 then 1 else 0)) ∧
    (∀ r : Three × Three, entry R (.inr r)=entry T (.inr r)) := by
  let P := LinearMap.ker l₁ ⊓ LinearMap.ker l₂
  have hv' : v ∈ T.U 1 ⊓ T.U 2 := ⟨T.side_le_signal 1 hv.1,hv.2⟩
  have hz' : z ∈ T.U 0 ⊓ T.U 2 := ⟨hz.2,T.side_le_signal 2 hz.1⟩
  obtain ⟨hp',hi'⟩ := codimTwo_spans T l₁ l₂ h₁ h₂ hp hi v z hv' hz' hlv hlz
  have ht : T.U 0 ⊓ T.U 1 ⊓ T.U 2 ≤ P :=
    le_inf (inf_le_left.trans (inf_le_left.trans h₁)) (inf_le_left.trans (inf_le_right.trans h₂))
  have hd (i j k : Three) (hij : i ≠ j) := firstEntry_difference T P hg hf i j k (hp i j hij) (hp' i j hij)
  have h01 := firstEntry_unchanged_of_pair_le T P hg hf 0 1 2 (hp 0 1 (by decide))
    (hp' 0 1 (by decide)) (le_inf (inf_le_left.trans h₁) (inf_le_right.trans h₂))
  have h10 := firstEntry_unchanged_of_pair_le T P hg hf 1 0 2 (hp 1 0 (by decide))
    (hp' 1 0 (by decide)) (le_inf (inf_le_right.trans h₁) (inf_le_left.trans h₂))
  have red02 (A : Submodule K F) := codimTwo_condRank_reduction A (T.U 0 ⊓ T.U 2) l₁ l₂ (inf_le_left.trans h₁)
  have red12 (A : Submodule K F) : condRank ((T.U 1 ⊓ T.U 2) ⊓ P) (A ⊓ P)=
      condRank ((T.U 1 ⊓ T.U 2) ⊓ LinearMap.ker l₁) (A ⊓ LinearMap.ker l₁) := by
    simpa only [P,inf_comm (LinearMap.ker l₂) (LinearMap.ker l₁)] using
      codimTwo_condRank_reduction A (T.U 1 ⊓ T.U 2) l₂ l₁ (inf_le_left.trans h₂)
  have h02rank := protected_condRank (T.A 2) (T.U 0 ⊓ T.U 2) l₂ ⟨z,⟨hz.1,hz'⟩,hlz⟩
  have h21rank := protected_condRank (T.A 1) (T.U 1 ⊓ T.U 2) l₁ ⟨v,⟨hv.1,hv'⟩,hlv⟩
  have h02 := hd 0 2 1 (by decide)
  rw [red02,h02rank] at h02
  have h21 := hd 2 1 0 (by decide)
  rw [inf_comm (T.U 2) (T.U 1),red12,h21rank] at h21
  have h12 := hd 1 2 0 (by decide)
  rw [red12] at h12
  have h20 := hd 2 0 1 (by decide)
  rw [inf_comm (T.U 2) (T.U 0),red02] at h20
  have hb12 := hyperplane_condRank_loss_le_one (T.A 2) (T.U 1 ⊓ T.U 2) l₁
  have hb20 := hyperplane_condRank_loss_le_one (T.A 0) (T.U 0 ⊓ T.U 2) l₂
  have hb12' : (condRank (T.U 1 ⊓ T.U 2) (T.A 2) : ℝ) ≤
      condRank ((T.U 1 ⊓ T.U 2) ⊓ LinearMap.ker l₁) (T.A 2 ⊓ LinearMap.ker l₁)+1 := by exact_mod_cast hb12
  have hb20' : (condRank (T.U 0 ⊓ T.U 2) (T.A 0) : ℝ) ≤
      condRank ((T.U 0 ⊓ T.U 2) ⊓ LinearMap.ker l₂) (T.A 0 ⊓ LinearMap.ker l₂)+1 := by exact_mod_cast hb20
  constructor
  · intro r
    fin_cases r
    · change firstEntry (inducedTask T P hg) 0 1 2 ≤ firstEntry T 0 1 2+0
      simpa using le_of_eq h01
    · change firstEntry (inducedTask T P hg) 0 2 1 ≤ firstEntry T 0 2 1+0
      linarith only [h02]
    · change firstEntry (inducedTask T P hg) 1 0 2 ≤ firstEntry T 1 0 2+0
      simpa using le_of_eq h10
    · change firstEntry (inducedTask T P hg) 1 2 0 ≤ firstEntry T 1 2 0+1
      linarith only [h12,hb12']
    · change firstEntry (inducedTask T P hg) 2 0 1 ≤ firstEntry T 2 0 1+1
      linarith only [h20,hb20']
    · change firstEntry (inducedTask T P hg) 2 1 0 ≤ firstEntry T 2 1 0+0
      linarith only [h21]
  · rintro ⟨i,ell⟩
    exact secondEntry_preserved T P hg hf hp hi hp' hi' ht i (i+1) (i+2) ell
      (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)

/-- Select both binary forms and obtain the actual complete e₄+e₅ relay
profile in one theorem. No target profile or maximal induced rank is assumed. -/
theorem exists_codimTwo_binary_profile (T : Task K F) (hspan : T.Spanning)
    (r w : LinearMap.ker (AlignedRelation.signalSum T.A))
    (hB : relationWedge T r w ≠ 0)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j=⊤)
    (hi : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)=T.U i)
    (v z : F) (hv : v ∈ T.A 1 ⊓ T.U 2) (hz : z ∈ T.A 2 ⊓ T.U 0)
    (hvU : v ∉ T.U 0) (hzU : z ∉ T.U 1) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P+2=finrank K F ∧
      (∀ r : Fin 6, entry (inducedTask T P hg) (.inl r) ≤ entry T (.inl r)+(if r=3 ∨ r=4 then 1 else 0)) ∧
      (∀ r : Three × Three, entry (inducedTask T P hg) (.inr r)=entry T (.inr r)) := by
  obtain ⟨l₁,l₂,h₁,h₂,hlv,hlz,hg,hf,hd⟩ :=
    exists_binary_codimTwo_relay T hspan r w hB v z hvU hzU
  exact ⟨LinearMap.ker l₁ ⊓ LinearMap.ker l₂,hg,hf,hd,
    codimTwo_profile_bound T l₁ l₂ h₁ h₂ hg hf hp hi v z hv hz hlv hlz⟩

end Finite
end UploadBroadcast.BinaryCodimTwoProfiles
