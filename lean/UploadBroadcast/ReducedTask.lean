import UploadBroadcast.ActiveTaskAssembly

/-!
# Active-pair correction selected from actual signal spaces

The helper lemmas start with pair-block charts, but the final construction
`Task.pairReduction` starts with an arbitrary feasible task, constructs its
common quotient, intrinsic pair blocks, charts, graph corrections, simultaneous
shear, and deletion of all passive pair blocks. Its fixed-block and regularized
regions are proved equal to the original ones for arbitrary nonlinear codes.
The original intersection ranks are identified with the constructed active
factors. This file does not yet assemble the subsequent unused-private and
empty-tripod-row reductions into the final upload formula.
-/
namespace UploadBroadcast
variable {K F V : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup V] [Module K V]

/-- Select one active-pair correction from an actual task in pair-block
coordinates. The other two users know the whole pair block. -/
theorem task_active_pair_correction (T : Task K (F × V)) (i : Three)
    (hi : ∀ x ∈ T.A i, x.1 = 0)
    (hj : ∀ j, j ≠ i → ∀ x : F, (x, 0) ∈ T.A j) :
    ∃ (P : Submodule K F) (ψ : V →ₗ[K] F),
      IsCompl P ((T.U i).comap (LinearMap.inl K F V)) ∧
      LinearMap.range ψ ≤ P ∧
      (∀ x ∈ T.A i, ψ x.2 = 0) ∧
      (∀ j, (T.A j).map (pairShear ψ).toLinearMap = T.A j) ∧
      (T.U i).map (pairShear ψ).toLinearMap =
        ((T.U i).comap (LinearMap.inl K F V)).prod
          ((T.U i).map (LinearMap.snd K F V)) := by
  let A := (T.U i).comap (LinearMap.inl K F V)
  obtain ⟨P, hP⟩ := A.exists_isCompl
  obtain ⟨ψ, hψ, hm⟩ := active_pair_graph (T.U i) A P rfl hP.symm
  have hz : ∀ x ∈ T.A i, ψ x.2 = 0 := by
    intro x hx
    have hd := (hm x.1 x.2).mp (T.side_le_signal i hx)
    rw [hi x hx, zero_sub] at hd
    have ha : ψ x.2 ∈ A := A.neg_mem_iff.mp hd.1
    exact Submodule.disjoint_def.mp hP.disjoint (ψ x.2) ha (hψ ⟨x.2, rfl⟩)
  have ha : ∀ j x, x ∈ T.A j → (ψ x.2, 0) ∈ T.A j := by
    intro j x hx
    by_cases he : j = i
    · subst j
      rw [hz x hx]
      exact (T.A i).zero_mem
    · exact hj j he _
  have hside : ∀ j, (T.A j).map (pairShear ψ).toLinearMap = T.A j := by
    intro j
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [pairShear, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Prod.sub_def, sub_zero] using (T.A j).sub_mem hy (ha j y hy)
    · intro hx
      refine ⟨(x.1 + ψ x.2, x.2), ?_, ?_⟩
      · simpa only [Prod.add_def, add_zero] using (T.A j).add_mem hx (ha j x hx)
      · ext <;> simp [pairShear]
  refine ⟨P, ψ, hP.symm, hψ, hz, hside, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hm y.1 y.2).mp hy
  · intro hx
    refine ⟨(x.1 + ψ x.2, x.2), ?_, ?_⟩
    · apply (hm _ _).mpr
      simpa using hx
    · ext <;> simp [pairShear]

/-- A graph correction in an arbitrary ambient pair-block chart. -/
def pairChartCorrection {W : Type*} [AddCommGroup W] [Module K W]
    (e : (F × V) ≃ₗ[K] W) (ψ : V →ₗ[K] F) : W →ₗ[K] W :=
  e.toLinearMap.comp ((LinearMap.inl K F V).comp
    (ψ.comp ((LinearMap.snd K F V).comp e.symm.toLinearMap)))

@[simp] theorem pairChartCorrection_apply {W : Type*} [AddCommGroup W] [Module K W]
    (e : (F × V) ≃ₗ[K] W) (ψ : V →ₗ[K] F) (x : W) :
    pairChartCorrection e ψ x = e (ψ (e.symm x).2, 0) := rfl

theorem pairChartCorrection_square_zero {W : Type*} [AddCommGroup W] [Module K W]
    (e : (F × V) ≃ₗ[K] W) (ψ : V →ₗ[K] F) :
    (pairChartCorrection e ψ).comp (pairChartCorrection e ψ) = 0 := by
  ext x
  simp

/-- Conjugating the ambient shear recovers the exact pair-chart shear. -/
theorem pairChartCorrection_map {W : Type*} [AddCommGroup W] [Module K W]
    (e : (F × V) ≃ₗ[K] W) (ψ : V →ₗ[K] F) (U : Submodule K W) :
    (U.map (squareZeroShear (pairChartCorrection e ψ)
      (pairChartCorrection_square_zero e ψ)).toLinearMap).map e.symm.toLinearMap =
      (U.map e.symm.toLinearMap).map (pairShear ψ).toLinearMap := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  · simp [squareZeroShear, pairShear]
  · simp [squareZeroShear, pairShear]

/-- Selection in a genuine ambient chart, including the incidence properties
needed by the simultaneous-shear theorems. -/
theorem task_active_pair_chart {W : Type*} [AddCommGroup W] [Module K W]
    (T : Task K W) (i : Three) (e : (F × V) ≃ₗ[K] W)
    (hi : ∀ x ∈ T.A i, (e.symm x).1 = 0)
    (hj : ∀ j, j ≠ i → ∀ x : F, e (x, 0) ∈ T.A j) :
    ∃ (P : Submodule K F) (ψ : V →ₗ[K] F),
      IsCompl P (((T.U i).map e.symm.toLinearMap).comap (LinearMap.inl K F V)) ∧
      LinearMap.range ψ ≤ P ∧
      (∀ x ∈ T.A i, pairChartCorrection e ψ x = 0) ∧
      (∀ j, j ≠ i → LinearMap.range (pairChartCorrection e ψ) ≤ T.A j) ∧
      ((T.U i).map e.symm.toLinearMap).map (pairShear ψ).toLinearMap =
        (((T.U i).map e.symm.toLinearMap).comap (LinearMap.inl K F V)).prod
        (((T.U i).map e.symm.toLinearMap).map (LinearMap.snd K F V)) := by
  let S := Profile.mapTask e.symm T
  have hsi : ∀ x ∈ S.A i, x.1 = 0 := by
    rintro x ⟨y, hy, rfl⟩
    exact hi y hy
  have hsj : ∀ j, j ≠ i → ∀ x : F, (x, 0) ∈ S.A j := by
    intro j hji x
    exact ⟨e (x, 0), hj j hji x, e.symm_apply_apply (x, 0)⟩
  obtain ⟨P, ψ, hP, hψ, hz, _, hU⟩ := task_active_pair_correction S i hsi hsj
  refine ⟨P, ψ, hP, hψ, ?_, ?_, hU⟩
  · intro x hx
    have h := hz (e.symm x) ⟨x, hx, rfl⟩
    simp only [pairChartCorrection_apply, h]
    exact e.map_zero
  · intro j hji x hx
    obtain ⟨y, rfl⟩ := hx
    exact hj j hji _

/-- Corrections selected independently for each missing user annihilate
one another. Off-diagonal annihilation follows from the known-pair incidence,
not an extra mixed-product assumption. -/
theorem task_pair_corrections_annihilate (T : Task K F)
    (N : Three → F →ₗ[K] F)
    (hsq : ∀ i, (N i).comp (N i) = 0)
    (hz : ∀ i x, x ∈ T.A i → N i x = 0)
    (hr : ∀ i j, i ≠ j → LinearMap.range (N i) ≤ T.A j) :
    ∀ i j, (N i).comp (N j) = 0 := by
  intro i j
  by_cases h : i = j
  · subst j
    exact hsq i
  · ext x
    exact hz i _ (hr j i (Ne.symm h) ⟨x, rfl⟩)

/-- The total correction preserves every side-information space. -/
theorem task_simultaneous_pair_shear (T : Task K F)
    (N : Three → F →ₗ[K] F)
    (hsq : ∀ i, (N i).comp (N i) = 0)
    (hz : ∀ i x, x ∈ T.A i → N i x = 0)
    (hr : ∀ i j, i ≠ j → LinearMap.range (N i) ≤ T.A j) :
    ∀ j, (T.A j).map
      (squareZeroShear (∑ i, N i)
        (sum_square_zero N (task_pair_corrections_annihilate T N hsq hz hr))).toLinearMap = T.A j := by
  intro j
  apply simultaneous_shear_preserves N (task_pair_corrections_annihilate T N hsq hz hr)
  intro i x hx
  by_cases h : i = j
  · subst i
    rw [hz j x hx]
    exact (T.A j).zero_mem
  · exact hr i j h ⟨x, rfl⟩

/-- Adding a square-zero correction whose image is already in the signal
space does not alter the separated signal space. This is the compatibility
step permitting independently selected pair corrections to run together. -/
theorem shear_map_eq_of_extra_range (U : Submodule K F)
    (N M : F →ₗ[K] F) (hNN : N.comp N = 0) (hMM : M.comp M = 0)
    (hNM : N.comp M = 0) (hMN : M.comp N = 0)
    (hM : LinearMap.range M ≤ U) :
    U.map (squareZeroShear (N + M) (by
      ext x
      have h1 := LinearMap.congr_fun hNN x
      have h2 := LinearMap.congr_fun hMM x
      have h3 := LinearMap.congr_fun hNM x
      have h4 := LinearMap.congr_fun hMN x
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1 h2 h3 h4
      simp [h1, h2, h3, h4])).toLinearMap =
      U.map (squareZeroShear N hNN).toLinearMap := by
  have hnm (x : F) : N (M x) = 0 := LinearMap.congr_fun hNM x
  have hmm (x : F) : M (M x) = 0 := LinearMap.congr_fun hMM x
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x - M x, U.sub_mem hx (hM ⟨x, rfl⟩), ?_⟩
    change (x - M x) - N (x - M x) = x - (N x + M x)
    rw [map_sub, hnm, sub_zero]
    abel
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x + M x, U.add_mem hx (hM ⟨x, rfl⟩), ?_⟩
    change (x + M x) - (N (x + M x) + M (x + M x)) = x - N x
    rw [map_add, map_add, hnm, hmm, add_zero, add_zero]
    abel

/-- A simultaneous shear has exactly the effect of the selected own-pair
shear on each user's signal space. All other corrections are locally known. -/
theorem task_simultaneous_pair_signal (T : Task K F)
    (N : Three → F →ₗ[K] F)
    (hsq : ∀ i, (N i).comp (N i) = 0)
    (hz : ∀ i x, x ∈ T.A i → N i x = 0)
    (hr : ∀ i j, i ≠ j → LinearMap.range (N i) ≤ T.A j) (i : Three) :
    (T.U i).map (squareZeroShear (∑ j, N j)
      (sum_square_zero N (task_pair_corrections_annihilate T N hsq hz hr))).toLinearMap =
    (T.U i).map (squareZeroShear (N i) (hsq i)).toLinearMap := by
  classical
  let M := ∑ j ∈ Finset.univ.erase i, N j
  have hh := task_pair_corrections_annihilate T N hsq hz hr
  have hNM : (N i).comp M = 0 := by
    ext x
    simp only [M, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    simp only [show ∀ j, N i (N j x) = 0 from fun j => LinearMap.congr_fun (hh i j) x,
      Finset.sum_const_zero, LinearMap.zero_apply]
  have hMN : M.comp (N i) = 0 := by
    ext x
    simp only [M, LinearMap.comp_apply, LinearMap.sum_apply]
    simp only [show ∀ j, N j (N i x) = 0 from fun j => LinearMap.congr_fun (hh j i) x,
      Finset.sum_const_zero, LinearMap.zero_apply]
  have hMM : M.comp M = 0 := by
    ext x
    simp only [M, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    simp only [show ∀ j k, N j (N k x) = 0 from fun j k => LinearMap.congr_fun (hh j k) x,
      Finset.sum_const_zero, LinearMap.zero_apply]
  have hsum : (∑ j, N j) = N i + M := by
    exact (Finset.add_sum_erase Finset.univ N (Finset.mem_univ i)).symm
  have hM : LinearMap.range M ≤ T.U i := by
    rintro x ⟨y, rfl⟩
    apply T.side_le_signal i
    simp only [M, LinearMap.sum_apply]
    apply (T.A i).sum_mem
    intro j hj
    exact hr j i (Finset.ne_of_mem_erase hj) ⟨y, rfl⟩
  simpa only [squareZeroShear, hsum] using
    shear_map_eq_of_extra_range (T.U i) (N i) M (hsq i) hMM hNM hMN hM

/-- All three graph corrections can be chosen simultaneously from the actual
signals. The assumptions describe only side-space pair-block charts; the
active/passive complements and every separated signal are constructed. -/
theorem exists_simultaneous_active_pair_corrections (T : Task K F)
    (B X : Three → Submodule K F)
    (e : ∀ i, (B i × X i) ≃ₗ[K] F)
    (hi : ∀ i x, x ∈ T.A i → ((e i).symm x).1 = 0)
    (hj : ∀ i j, j ≠ i → ∀ x : B i, e i (x, 0) ∈ T.A j) :
    ∃ ψ : ∀ i, X i →ₗ[K] B i,
      (∀ i, ∃ P : Submodule K (B i),
        IsCompl P (((T.U i).map (e i).symm.toLinearMap).comap
          (LinearMap.inl K (B i) (X i))) ∧ LinearMap.range (ψ i) ≤ P) ∧
      (∀ i x, x ∈ T.A i → pairChartCorrection (e i) (ψ i) x = 0) ∧
      (∀ i j, i ≠ j → LinearMap.range (pairChartCorrection (e i) (ψ i)) ≤ T.A j) ∧
      (∀ i, ((T.U i).map (e i).symm.toLinearMap).map (pairShear (ψ i)).toLinearMap =
        (((T.U i).map (e i).symm.toLinearMap).comap
          (LinearMap.inl K (B i) (X i))).prod
        (((T.U i).map (e i).symm.toLinearMap).map (LinearMap.snd K (B i) (X i)))) := by
  classical
  have h (i : Three) := task_active_pair_chart T i (e i) (hi i) (hj i)
  choose P ψ hP hψ hz hr hU using h
  exact ⟨ψ, fun i => ⟨P i, hP i, hψ i⟩, hz, fun i j h => hr i j h.symm, hU⟩

/-- Exact graph description of residual demands. The pure space is the
intersection with the tripod summand, and private projection is a separate
membership condition; no projected tripod space is substituted for purity. -/
theorem pureDemandGraph_characterization (Q : Submodule K (F × V)) :
    ∃ φ : F →ₗ[K] (V ⧸ Q.comap (LinearMap.inr K F V)),
      ∀ p t, (p, t) ∈ Q ↔
        p ∈ Q.map (LinearMap.fst K F V) ∧
        φ p = (Q.comap (LinearMap.inr K F V)).mkQ t := by
  obtain ⟨φ, hφ⟩ := graph_data_map Q
  refine ⟨φ, ?_⟩
  intro p t
  constructor
  · intro hpt
    exact ⟨⟨(p, t), hpt, rfl⟩, hφ p t hpt⟩
  · rintro ⟨⟨w, hw, hwp⟩, ht⟩
    change w.1 = p at hwp
    have hw' : (p, w.2) ∈ Q := by simpa only [← hwp] using hw
    have hd : t - w.2 ∈ Q.comap (LinearMap.inr K F V) := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change (Q.comap (LinearMap.inr K F V)).mkQ (t - w.2) = 0
      rw [map_sub, ← ht, ← hφ p w.2 hw', sub_self]
    have h := Q.add_mem hw' hd
    convert h using 1; simp

namespace Task
/-- The pair-known block missing user i, defined without coordinate choices. -/
def pairKnown (T : Task K F) (i : Three) : Submodule K F :=
  ⨅ j, ⨅ (_ : j ≠ i), T.A j

theorem pairKnown_le (T : Task K F) (i j : Three) (h : j ≠ i) :
    T.pairKnown i ≤ T.A j := (iInf_le _ j).trans (iInf_le _ h)

/-- Identification with the two other side spaces for any enumeration of
three distinct user labels. -/
theorem pairKnown_eq_pair (T : Task K F) (i j k : Three)
    (hji : j ≠ i) (hki : k ≠ i) (hcover : ∀ l : Three, l = i ∨ l = j ∨ l = k) :
    T.pairKnown i = T.A j ⊓ T.A k := by
  apply le_antisymm
  · exact le_inf (T.pairKnown_le i j hji) (T.pairKnown_le i k hki)
  · intro x hx
    apply (Submodule.mem_iInf _).mpr
    intro l
    apply (Submodule.mem_iInf _).mpr
    intro hli
    rcases hcover l with h | h | h
    · exact False.elim (hli h)
    · simpa only [h] using hx.1
    · simpa only [h] using hx.2

theorem commonKnown_le_pairKnown (T : Task K F) (i : Three) :
    T.commonKnown ≤ T.pairKnown i :=
  le_iInf fun j => le_iInf fun _ => T.commonKnown_le j

private theorem mem_quotient_image_iff (C X : Submodule K F) (hCX : C ≤ X) (x : F) :
    C.mkQ x ∈ X.map C.mkQ ↔ x ∈ X := by
  constructor
  · rintro ⟨y, hy, he⟩
    have hd : x - y ∈ C := by
      apply (Submodule.Quotient.mk_eq_zero C).mp
      change C.mkQ (x - y) = 0
      rw [map_sub, he, sub_self]
    simpa using X.add_mem (hCX hd) hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem quotient_pairKnown (T : Task K F) (i : Three) :
    (T.pairKnown i).map T.commonKnown.mkQ =
      (T.quotientTask T.commonKnown).pairKnown i := by
  ext q
  obtain ⟨x, rfl⟩ := T.commonKnown.mkQ_surjective q
  rw [mem_quotient_image_iff _ _ (T.commonKnown_le_pairKnown i)]
  change (x ∈ ⨅ j, ⨅ (_ : j ≠ i), T.A j) ↔
    (T.commonKnown.mkQ x ∈ ⨅ j, ⨅ (_ : j ≠ i), (T.A j).map T.commonKnown.mkQ)
  simp only [Submodule.mem_iInf]
  constructor
  · intro hx j hji
    exact (mem_quotient_image_iff _ _ (T.commonKnown_le j) x).mpr (hx j hji)
  · intro hx j hji
    exact (mem_quotient_image_iff _ _ (T.commonKnown_le j) x).mp (hx j hji)

/-- Actual original-space dimension of the active pair missing user i. -/
noncomputable def intrinsicActivePairRank [FiniteDimensional K F]
    (T : Task K F) (i : Three) : ℕ :=
  Module.finrank K ↥(T.U i ⊓ T.pairKnown i) - Module.finrank K T.commonKnown

theorem intrinsicActivePairRank_quotient [FiniteDimensional K F]
    (T : Task K F) (i : Three) :
    T.intrinsicActivePairRank i = Module.finrank K
      ↥((T.quotientTask T.commonKnown).U i ⊓ (T.quotientTask T.commonKnown).pairKnown i) := by
  rw [← T.quotient_pairKnown]
  change _ = Module.finrank K ↥((T.U i).map T.commonKnown.mkQ ⊓
    (T.pairKnown i).map T.commonKnown.mkQ)
  rw [← quotient_map_inf _ _ _ (T.commonKnown_le_pairKnown i),
    ← condRank_eq_finrank_quotient_image]
  unfold intrinsicActivePairRank condRank
  rw [sup_eq_right.mpr (le_inf ((T.commonKnown_le i).trans (T.side_le_signal i))
    (T.commonKnown_le_pairKnown i))]

theorem pairKnown_disjoint (T : Task K F) (hT : T.commonKnown = ⊥) (i : Three) :
    Disjoint (T.pairKnown i) (T.A i) := by
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  intro x hx
  have hc : x ∈ T.commonKnown := by
    apply (Submodule.mem_iInf _).mpr
    intro j
    by_cases h : j = i
    · simpa only [h] using hx.2
    · exact T.pairKnown_le i j h hx.1
  simpa only [hT] using hc

/-- Actual intrinsic pair blocks have compatible charts whenever common
information has been quotiented out. No side-normal-form hypothesis is needed. -/
theorem exists_pairKnown_charts (T : Task K F) (hT : T.commonKnown = ⊥) :
    ∃ (X : Three → Submodule K F)
      (e : ∀ i, (T.pairKnown i × X i) ≃ₗ[K] F),
      (∀ i x, x ∈ T.A i → ((e i).symm x).1 = 0) ∧
      (∀ i j, j ≠ i → ∀ x : T.pairKnown i, e i (x, 0) ∈ T.A j) ∧
      (∀ i (x : T.pairKnown i), e i (x, 0) = x) := by
  classical
  have h (i : Three) := exists_complement_containing (T.pairKnown i) (T.A i)
    (T.pairKnown_disjoint hT i)
  choose X hX hA using h
  refine ⟨X, fun i => Submodule.prodEquivOfIsCompl _ _ (hX i), ?_, ?_, ?_⟩
  · intro i x hx
    exact (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero _ _ (hX i)).mpr (hA i hx)
  · intro i j hji x
    simpa only [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_zero, add_zero] using
      T.pairKnown_le i j hji x.property
  · intro i x
    simp

/-- Constructed simultaneous active-pair data for an actual task. -/
structure ActivePairSelection (T : Task K F) where
  residual : Three → Submodule K F
  chart : ∀ i, (T.pairKnown i × residual i) ≃ₗ[K] F
  chart_own : ∀ i x, x ∈ T.A i → ((chart i).symm x).1 = 0
  chart_pair : ∀ i (x : T.pairKnown i), chart i (x, 0) = x
  correction : ∀ i, residual i →ₗ[K] T.pairKnown i
  passive : ∀ i, Submodule K (T.pairKnown i)
  complementary : ∀ i, IsCompl (passive i)
    (((T.U i).map (chart i).symm.toLinearMap).comap
      (LinearMap.inl K (T.pairKnown i) (residual i)))
  correction_passive : ∀ i, LinearMap.range (correction i) ≤ passive i
  own_zero : ∀ i x, x ∈ T.A i → pairChartCorrection (chart i) (correction i) x = 0
  known_range : ∀ i j, i ≠ j →
    LinearMap.range (pairChartCorrection (chart i) (correction i)) ≤ T.A j
  separation : ∀ i,
    ((T.U i).map (chart i).symm.toLinearMap).map (pairShear (correction i)).toLinearMap =
      (((T.U i).map (chart i).symm.toLinearMap).comap
        (LinearMap.inl K (T.pairKnown i) (residual i))).prod
      (((T.U i).map (chart i).symm.toLinearMap).map
        (LinearMap.snd K (T.pairKnown i) (residual i)))

/-- Unconditional simultaneous active-pair selection after common quotienting. -/
theorem exists_activePairSelection_of_commonKnown_eq_bot (T : Task K F)
    (hT : T.commonKnown = ⊥) : Nonempty T.ActivePairSelection := by
  classical
  obtain ⟨X, e, hi, hj, he⟩ := T.exists_pairKnown_charts hT
  obtain ⟨ψ, hP, hz, hr, hU⟩ := exists_simultaneous_active_pair_corrections T T.pairKnown X e hi hj
  choose P hPc hPr using hP
  exact ⟨⟨X, e, hi, he, ψ, P, hPc, hPr, hz, hr, hU⟩⟩

theorem exists_commonQuotient_activePairSelection (T : Task K F) :
    Nonempty (T.quotientTask T.commonKnown).ActivePairSelection :=
  (T.quotientTask T.commonKnown).exists_activePairSelection_of_commonKnown_eq_bot
    T.quotientTask_commonKnown_eq_bot

namespace ActivePairSelection
variable {T : Task K F} (s : T.ActivePairSelection)
def corrections (i : Three) : F →ₗ[K] F := pairChartCorrection (s.chart i) (s.correction i)

theorem square_zero (i : Three) : (s.corrections i).comp (s.corrections i) = 0 :=
  pairChartCorrection_square_zero _ _

theorem mixed_zero : ∀ i j, (s.corrections i).comp (s.corrections j) = 0 :=
  task_pair_corrections_annihilate T s.corrections s.square_zero s.own_zero s.known_range

def simultaneous : F ≃ₗ[K] F :=
  squareZeroShear (∑ i, s.corrections i) (sum_square_zero s.corrections s.mixed_zero)

theorem simultaneous_side (i : Three) :
    (T.A i).map s.simultaneous.toLinearMap = T.A i :=
  task_simultaneous_pair_shear T s.corrections s.square_zero s.own_zero s.known_range i

theorem simultaneous_signal (i : Three) :
    (T.U i).map s.simultaneous.toLinearMap =
      (T.U i).map (squareZeroShear (s.corrections i) (s.square_zero i)).toLinearMap :=
  task_simultaneous_pair_signal T s.corrections s.square_zero s.own_zero s.known_range i

/-- The single global shear achieves all three exact graph separations. -/
theorem simultaneous_separation (i : Three) :
    ((T.U i).map s.simultaneous.toLinearMap).map (s.chart i).symm.toLinearMap =
      (((T.U i).map (s.chart i).symm.toLinearMap).comap
        (LinearMap.inl K (T.pairKnown i) (s.residual i))).prod
      (((T.U i).map (s.chart i).symm.toLinearMap).map
        (LinearMap.snd K (T.pairKnown i) (s.residual i))) := by
  rw [s.simultaneous_signal]
  exact (pairChartCorrection_map _ _ _).trans (s.separation i)

/-- The constructed active factor is exactly the original signal's
intersection with the intrinsic pair block, expressed in subtype coordinates. -/
theorem active_factor_eq (i : Three) :
    (((T.U i).map (s.chart i).symm.toLinearMap).comap
      (LinearMap.inl K (T.pairKnown i) (s.residual i))) =
      (T.U i).comap (T.pairKnown i).subtype := by
  ext b
  constructor
  · rintro ⟨y, hy, he⟩
    have hyb : y = (b : F) := by
      calc
        y = s.chart i ((s.chart i).symm y) := ((s.chart i).apply_symm_apply y).symm
        _ = s.chart i (b, 0) := congrArg (s.chart i) he
        _ = b := s.chart_pair i b
    change (b : F) ∈ T.U i
    simpa only [hyb] using hy
  · intro hb
    refine ⟨b, hb, ?_⟩
    exact (s.chart i).symm_apply_eq.mpr (s.chart_pair i b).symm

theorem active_factor_finrank [FiniteDimensional K F] (i : Three) :
    Module.finrank K
      (((T.U i).map (s.chart i).symm.toLinearMap).comap
        (LinearMap.inl K (T.pairKnown i) (s.residual i))) =
      Module.finrank K ↥(T.U i ⊓ T.pairKnown i) := by
  rw [s.active_factor_eq]
  have h := (Submodule.comapSubtypeEquivOfLe
    (show T.U i ⊓ T.pairKnown i ≤ T.pairKnown i from inf_le_right)).finrank_eq
  have hb : (T.pairKnown i).comap (T.pairKnown i).subtype = ⊤ := by
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_top, iff_true]
    exact x.property
  rw [Submodule.comap_inf, hb, inf_top_eq] at h
  exact h

/-- Intrinsic active factor as represented inside the pair-known subtype. -/
abbrev activeFactor (i : Three) : Submodule K (T.pairKnown i) :=
  (((T.U i).map (s.chart i).symm.toLinearMap).comap
    (LinearMap.inl K (T.pairKnown i) (s.residual i)))

/-- Projection onto the selected passive part of one pair-known block. -/
noncomputable def passiveProjection (i : Three) : F →ₗ[K] F :=
  (s.chart i).toLinearMap.comp ((LinearMap.inl K (T.pairKnown i) (s.residual i)).comp
    ((s.passive i).subtype.comp (((s.passive i).linearProjOfIsCompl
      (s.activeFactor i) (s.complementary i)).comp
        ((LinearMap.fst K (T.pairKnown i) (s.residual i)).comp (s.chart i).symm.toLinearMap))))

@[simp] theorem passiveProjection_apply (i : Three) (x : F) :
    s.passiveProjection i x = s.chart i
      (((s.passive i).linearProjOfIsCompl (s.activeFactor i)
        (s.complementary i) ((s.chart i).symm x).1 : T.pairKnown i), 0) := rfl

theorem passiveProjection_own (i : Three) (x : F) (hx : x ∈ T.A i) :
    s.passiveProjection i x = 0 := by
  simp [s.chart_own i x hx]

theorem passiveProjection_known (i j : Three) (h : i ≠ j) (x : F) :
    s.passiveProjection i x ∈ T.A j := by
  rw [s.passiveProjection_apply, s.chart_pair]
  exact T.pairKnown_le i j h.symm (Subtype.prop _)

theorem passiveProjection_idempotent (i : Three) :
    (s.passiveProjection i).comp (s.passiveProjection i) = s.passiveProjection i := by
  ext x
  simp only [LinearMap.comp_apply, passiveProjection_apply, LinearEquiv.symm_apply_apply]
  rw [Submodule.linearProjOfIsCompl_apply_left]

theorem passiveProjection_mixed (i j : Three) (h : i ≠ j) :
    (s.passiveProjection i).comp (s.passiveProjection j) = 0 := by
  ext x
  exact s.passiveProjection_own i _ (s.passiveProjection_known j i h.symm x)

theorem passiveProjection_signal (i : Three) (x : F)
    (hx : x ∈ (T.U i).map s.simultaneous.toLinearMap) :
    s.passiveProjection i x = 0 := by
  have hm : (s.chart i).symm x ∈
      ((T.U i).map s.simultaneous.toLinearMap).map (s.chart i).symm.toLinearMap := ⟨x, hx, rfl⟩
  rw [s.simultaneous_separation] at hm
  have hp := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff (s.complementary i)).mpr hm.1
  rw [s.passiveProjection_apply, hp]
  exact (s.chart i).map_zero

noncomputable def totalPassiveProjection : F →ₗ[K] F := ∑ i, s.passiveProjection i

theorem totalPassiveProjection_idempotent :
    s.totalPassiveProjection.comp s.totalPassiveProjection = s.totalPassiveProjection := by
  classical
  ext x
  simp only [totalPassiveProjection, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact LinearMap.congr_fun (s.passiveProjection_idempotent i) x
  · intro j _ hji
    exact LinearMap.congr_fun (s.passiveProjection_mixed j i hji) x
  · simp

theorem totalPassiveProjection_local (i : Three) (x : F)
    (hx : x ∈ (Profile.mapTask s.simultaneous T).U i) :
    s.totalPassiveProjection x ∈ (Profile.mapTask s.simultaneous T).A i := by
  change s.totalPassiveProjection x ∈ (T.A i).map s.simultaneous.toLinearMap
  rw [s.simultaneous_side]
  simp only [totalPassiveProjection, LinearMap.sum_apply]
  apply (T.A i).sum_mem
  intro j _
  by_cases h : j = i
  · subst j
    rw [s.passiveProjection_signal i x hx]
    exact (T.A i).zero_mem
  · exact s.passiveProjection_known j i h x

/-- The actual task remaining after all passive pair directions are deleted. -/
noncomputable def pairReducedTask : Task K (LinearMap.ker s.totalPassiveProjection) :=
  (Profile.mapTask s.simultaneous T).imageTask
    (Task.complementaryProjection s.totalPassiveProjection s.totalPassiveProjection_idempotent)

noncomputable def pairPassiveRetraction :
    PassiveRetraction (Profile.mapTask s.simultaneous T) s.pairReducedTask :=
  (Profile.mapTask s.simultaneous T).idempotentPassiveRetraction
    s.totalPassiveProjection s.totalPassiveProjection_idempotent s.totalPassiveProjection_local

theorem pairReduced_achievableAt_eq [Finite K] [FiniteDimensional K F] (L : ℕ) :
    T.achievableAt L = s.pairReducedTask.achievableAt L :=
  (T.coordinate_achievableAt_eq s.simultaneous L).trans (s.pairPassiveRetraction.achievableAt_eq L)

theorem simultaneous_achievableAt_eq [Finite K] [FiniteDimensional K F] (L : ℕ) :
    T.achievableAt L = (Profile.mapTask s.simultaneous T).achievableAt L :=
  T.coordinate_achievableAt_eq s.simultaneous L

end ActivePairSelection
/-- A definite, choice-selected active-pair reduction of every feasible task. -/
noncomputable def selectedPairs (T : Task K F) :
    (T.quotientTask T.commonKnown).ActivePairSelection :=
  Classical.choice T.exists_commonQuotient_activePairSelection

theorem selectedPairs_activeFactor_finrank [FiniteDimensional K F]
    (T : Task K F) (i : Three) :
    Module.finrank K (T.selectedPairs.activeFactor i) = T.intrinsicActivePairRank i :=
  (T.selectedPairs.active_factor_finrank i).trans (T.intrinsicActivePairRank_quotient i).symm

noncomputable def pairReduction (T : Task K F) :
    Task K (LinearMap.ker T.selectedPairs.totalPassiveProjection) :=
  T.selectedPairs.pairReducedTask

/-- The constructed reduction, including deletion of all passive pair blocks,
preserves every nonlinear achievable region for every original feasible task. -/
theorem pairReduction_achievableAt_eq [Finite K] [FiniteDimensional K F]
    (T : Task K F) (L : ℕ) : T.achievableAt L = T.pairReduction.achievableAt L :=
  (T.commonKnown_achievableAt_eq L).trans (T.selectedPairs.pairReduced_achievableAt_eq L)

theorem pairReduction_costRegion_eq [Finite K] [FiniteDimensional K F]
    (T : Task K F) : T.costRegion = T.pairReduction.costRegion := by
  unfold costRegion
  simp_rw [T.pairReduction_achievableAt_eq]

/-- End-to-end nonlinear fixed-block invariance through the constructed
common quotient and simultaneous active-pair coordinate change. -/
theorem commonQuotient_activePair_achievableAt_eq
    [Finite K] [FiniteDimensional K F] (T : Task K F)
    (s : (T.quotientTask T.commonKnown).ActivePairSelection) (L : ℕ) :
    T.achievableAt L =
      (Profile.mapTask s.simultaneous (T.quotientTask T.commonKnown)).achievableAt L :=
  (T.commonKnown_achievableAt_eq L).trans (s.simultaneous_achievableAt_eq L)

end Task

end UploadBroadcast
