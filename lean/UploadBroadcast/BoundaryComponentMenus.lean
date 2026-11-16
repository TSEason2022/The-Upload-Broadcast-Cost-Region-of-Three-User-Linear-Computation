import UploadBroadcast.ActiveComponentClassification
import UploadBroadcast.NonzeroSameChartMenus

/-! Actual n=0 tripod boundary relay choices, including the profile-preserving
T₂ boundary that survives the active reduction. No normal-form oracle is used. -/
namespace UploadBroadcast.BoundaryComponentMenus
open Module Profile NonzeroDefectProfile NonzeroFamilyRanks NonzeroDefectRelays
open IntersectionProbes
variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

structure Geometry (T : Task K F) (g : Family) : Prop where
  ambient : finrank K F = 2
  side : ∀ i, finrank K (T.A i) = 1
  pair_inf : ∀ i j, i ≠ j → T.A i ⊓ T.A j = ⊥
  pair_sup : ∀ i j, i ≠ j → T.A i ⊔ T.A j = ⊤
  signal_zero : T.U 0 = ⊤
  signal_one : T.U 1 = if g = .T1 then T.A 1 else ⊤
  signal_two : T.U 2 = T.A 2

/-- The actual three sides are distinct lines spanning the plane. -/
theorem geometry (T : Task K F)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (hg : g = .T1 ∨ g = .T2) (h : Dimensions T g 0) :
    Geometry T g := by
  have hf : finrank K F = 2 := by rw [h.ambient]; rcases hg with rfl | rfl <;> rfl
  have ha (i : Three) : finrank K (T.A i) = 1 := by
    rw [h.side]; rcases hg with rfl | rfl <;> fin_cases i <;> rfl
  have hinf (i j : Three) (hij : i ≠ j) : T.A i ⊓ T.A j = ⊥ := by
    have hh := probe_intersection_finrank (EdgeExtraction.configuration T) hi
      (h.positive_defect T g 0) (sidePair i j)
    rw [sidePair_intersection,euler_sidePair _ i j hij] at hh
    change (finrank K ↥(T.A i ⊓ T.A j) : ℤ) =
      max 0 ((finrank K (T.A i) : ℤ) + finrank K (T.A j) - finrank K F) at hh
    rw [hf,ha,ha] at hh
    exact Submodule.finrank_eq_zero.mp (by omega)
  refine ⟨hf,ha,hinf,?_,?_,?_,?_⟩
  · intro i j hij
    apply Submodule.eq_of_le_of_finrank_eq le_top
    have hh := Submodule.finrank_sup_add_finrank_inf_eq (T.A i) (T.A j)
    rw [hinf i j hij,finrank_bot,add_zero,ha,ha] at hh
    simpa [finrank_top,hf] using hh
  · apply Submodule.eq_of_le_of_finrank_eq le_top
    rw [finrank_top,hf,h.signal]
    rcases hg with rfl | rfl <;> rfl
  · rcases hg with rfl | rfl
    · simp only [ite_true]
      symm
      apply Submodule.eq_of_le_of_finrank_eq (T.side_le_signal 1)
      rw [ha,h.signal]; rfl
    · simp only [show Family.T2 ≠ .T1 from by decide,ite_false]
      apply Submodule.eq_of_le_of_finrank_eq le_top
      rw [finrank_top,hf,h.signal]; rfl
  · symm
    apply Submodule.eq_of_le_of_finrank_eq (T.side_le_signal 2)
    rw [ha,h.signal]
    rcases hg with rfl | rfl <;> rfl

omit [FiniteDimensional K F] in
lemma side_locally_generated (T : Task K F) (i : Three) : T.LocallyGenerated (T.A i) := by
  apply le_antisymm
  · exact le_iSup_of_le i (by simp)
  · exact iSup_le fun _ => inf_le_left

omit [FiniteDimensional K F] in
lemma T1_side_feasible (T : Task K F) (h : Geometry T .T1)
    (s : Three) (hs : s = 1 ∨ s = 2) : T.RelayFeasible (T.A s) := by
  intro i
  fin_cases i
  · change T.U 0 ≤ T.A 0 ⊔ T.A s
    rw [h.signal_zero,h.pair_sup 0 s (by rcases hs with rfl | rfl <;> decide)]
  · change T.U 1 ≤ T.A 1 ⊔ T.A s
    rw [h.signal_one]; simp
  · change T.U 2 ≤ T.A 2 ⊔ _
    rw [h.signal_two]; exact le_sup_left

omit [FiniteDimensional K F] in
lemma T2_side_feasible (T : Task K F) (h : Geometry T .T2) : T.RelayFeasible (T.A 2) := by
  intro i
  fin_cases i
  · change T.U 0 ≤ T.A 0 ⊔ T.A 2
    rw [h.signal_zero,h.pair_sup 0 2 (by decide)]
  · change T.U 1 ≤ T.A 1 ⊔ T.A 2
    rw [h.signal_one,h.pair_sup 1 2 (by decide)]; simp
  · change T.U 2 ≤ T.A 2 ⊔ _
    rw [h.signal_two]; exact le_sup_left

omit [FiniteDimensional K F] in
/-- The simplifier needs an explicit congruence rule for subtype-valued
subspace dimensions; the default dependent congruence does not descend here. -/
theorem finrank_submodule_congr (A B : Submodule K F) (h : A = B) :
    finrank K A = finrank K B := by rw [h]

attribute [local congr] finrank_submodule_congr

/-- All full and induced profile entries for the canonical T₁ boundary. -/
theorem T1_exact_profile (T : Task K F) (h : Geometry T .T1) (s : Three)
    (hs : s = 1 ∨ s = 2) :
    (∀ r : Fin 6, entry T (.inl r) = (![1,1,0,0,0,0] r : ℝ)) ∧
    (∀ r : Fin 6, entry (inducedTask T (T.A s) (side_locally_generated T s)) (.inl r) =
      entry T (.inl r) + (if s = 1 then ![0,0,0,0,1,0] r else ![0,0,1,0,0,0] r : ℝ)) ∧
    (∀ i ell : Three, 2 * entry T (.inr (i,ell)) = 1 ∧
      entry (inducedTask T (T.A s) (side_locally_generated T s)) (.inr (i,ell)) =
        entry T (.inr (i,ell))) := by
  have hi01 := h.pair_inf 0 1 (by decide)
  have hi02 := h.pair_inf 0 2 (by decide)
  have hi12 := h.pair_inf 1 2 (by decide)
  have hi10 := h.pair_inf 1 0 (by decide)
  have hi20 := h.pair_inf 2 0 (by decide)
  have hi21 := h.pair_inf 2 1 (by decide)
  have hs01 := h.pair_sup 0 1 (by decide)
  have hs02 := h.pair_sup 0 2 (by decide)
  have hs12 := h.pair_sup 1 2 (by decide)
  have hs10 := h.pair_sup 1 0 (by decide)
  have hs20 := h.pair_sup 2 0 (by decide)
  have hs21 := h.pair_sup 2 1 (by decide)
  rcases hs with rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals (intro r; try intro ell)
  all_goals fin_cases r <;> try fin_cases ell
  all_goals simp [entry,firstOrder,firstEntry,secondEntry,totalDemand,condRank,
    inducedTask,Fin.sum_univ_succ,h.signal_zero,h.signal_one,h.signal_two,
    hi01,hi02,hi12,hi10,hi20,hi21,hs01,hs02,hs12,hs10,hs20,hs21,h.ambient,h.side] <;> norm_num

/-- The T₂ boundary is profile-preserving in all fifteen entries. -/
theorem T2_preserves_profile (T : Task K F) (h : Geometry T .T2) :
    ∀ r : Profile.Index,
      entry (inducedTask T (T.A 2) (side_locally_generated T 2)) r = entry T r := by
  have hi02 := h.pair_inf 0 2 (by decide)
  have hi12 := h.pair_inf 1 2 (by decide)
  have hi20 := h.pair_inf 2 0 (by decide)
  have hi21 := h.pair_inf 2 1 (by decide)
  have hs02 := h.pair_sup 0 2 (by decide)
  have hs12 := h.pair_sup 1 2 (by decide)
  have hs20 := h.pair_sup 2 0 (by decide)
  have hs21 := h.pair_sup 2 1 (by decide)
  rintro (r | ⟨i,ell⟩)
  · fin_cases r <;> simp [entry,firstOrder,firstEntry,totalDemand,condRank,
      inducedTask,Fin.sum_univ_succ,h.signal_zero,h.signal_one,h.signal_two,
      hi02,hi12,hi20,hi21,hs02,hs12,hs20,hs21,h.ambient,h.side]
  · fin_cases i <;> fin_cases ell <;>
      simp [entry,secondEntry,totalDemand,condRank,
        inducedTask,Fin.sum_univ_succ,h.signal_zero,h.signal_one,h.signal_two,
        hi02,hi12,hi20,hi21,hs02,hs12,hs20,hs21,h.ambient,h.side]

/-- The converse used for the boundary is operational and nonlinear, not
merely a minimum over linear relays. -/
theorem boundary_code_lower [Finite K] {L : ℕ} {m : Three → ℕ} {s : ℕ}
    (T : Task K F) (g : Family) (hg : g = .T1 ∨ g = .T2) (h : Geometry T g)
    (c : T.Code L (fun i => Fin (m i)) (Fin s)) (hL : 0 < L) :
    1 ≤ c.uploadCost := by
  have hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j = ⊤ := by
    intro i j hij
    apply top_unique
    rw [←h.pair_sup i j hij]
    exact sup_le_sup (T.side_le_signal i) (T.side_le_signal j)
  have hj : T.U 2 ⊔ (T.U 0 ⊓ T.U 1) = ⊤ := by
    rw [h.signal_zero,top_inf_eq,h.signal_two,h.signal_one]
    rcases hg with rfl | rfl <;> simp [h.pair_sup 2 1 (by decide)]
  have ha : T.A 0 ⊔ T.A 1 ⊔ T.A 2 = ⊤ := by rw [h.pair_sup 0 1 (by decide),top_sup_eq]
  have hh := GeometricUploadConverse.code_lower T
    (disjoint_iff.mpr (h.pair_inf 0 1 (by decide)))
    (disjoint_iff.mpr (h.pair_inf 0 2 (by decide)))
    (disjoint_iff.mpr (h.pair_inf 1 2 (by decide))) ha hp hj c hL
  rw [h.ambient,h.side,h.side,h.side] at hh
  norm_num at hh
  exact hh

/-- Every constructed one-dimensional boundary relay attains U*. -/
theorem boundary_relay_optimal [Finite K]
    (T : Task K F) (g : Family) (hg : g = .T1 ∨ g = .T2) (h : Geometry T g)
    (P : Submodule K F) (hl : T.LocallyGenerated P) (hf : T.RelayFeasible P)
    (hd : finrank K P = 1) : (finrank K P : ℝ) = T.uploadOptimum := by
  obtain ⟨owner,c,hc⟩ := ResidualOperational.finiteCode_of_local_relay T P hl hf
  letI := c.finite_upload
  letI := c.finite_broadcast
  symm
  apply Task.uploadOptimum_eq_of_code c.toCode (by decide) _ hc
  intro L m s d hL
  rw [hd,Nat.cast_one]
  exact boundary_code_lower T g hg h d hL

/-- Both exact canonical boundary choices, in the same choice interface as
all positive-index T₁ menus. Works over every finite field. -/
theorem T1_all_menu_choices [Finite K] (T : Task K F)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (hd : Dimensions T .T1 0) (choice : Three) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P = 1 ∧ (finrank K P : ℝ) = T.uploadOptimum ∧
      (∀ r : Fin 6, entry (inducedTask T P hl) (.inl r) = entry T (.inl r) +
        (NonzeroSameChartMenus.menuIncrement .T1 choice r : ℝ)) ∧
      (∀ i ell : Three, entry (inducedTask T P hl) (.inr (i,ell)) = entry T (.inr (i,ell))) := by
  have h := geometry T hi .T1 (Or.inl rfl) hd
  let s : Three := if choice = 0 then 1 else 2
  have hs : s = 1 ∨ s = 2 := by simp only [s]; split_ifs <;> simp
  have hl := side_locally_generated T s
  have hf := T1_side_feasible T h s hs
  have hp := T1_exact_profile T h s hs
  refine ⟨T.A s,hl,hf,h.side s,boundary_relay_optimal T .T1 (Or.inl rfl) h
    _ hl hf (h.side s),?_,fun i ell => (hp.2.2 i ell).2⟩
  intro r
  rw [hp.2.1 r]
  congr 1
  fin_cases choice <;> fin_cases r <;> norm_num [s,NonzeroSameChartMenus.menuIncrement]

/-- The low-index T₂ residual is genuinely profile-preserving and attains U*. -/
theorem T2_optimal_preserving [Finite K] (T : Task K F)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (hd : Dimensions T .T2 0) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P = 1 ∧ (finrank K P : ℝ) = T.uploadOptimum ∧
      ∀ r : Profile.Index, entry (inducedTask T P hl) r = entry T r := by
  have h := geometry T hi .T2 (Or.inr rfl) hd
  have hl := side_locally_generated T 2
  have hf := T2_side_feasible T h
  exact ⟨T.A 2,hl,hf,h.side 2,boundary_relay_optimal T .T2 (Or.inr rfl) h
    _ hl hf (h.side 2),T2_preserves_profile T h⟩

omit [FiniteDimensional K F] in
/-- The signal intersection-spanning identity holds at both tripod boundaries. -/
lemma Geometry.pair_intersections_span (T : Task K F) (g : Family)
    (hg : g = .T1 ∨ g = .T2) (h : Geometry T g)
    (i j k : Three) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k) = T.U i := by
  rcases hg with rfl | rfl
  all_goals fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [h.signal_zero,h.signal_one,h.signal_two,h.pair_inf,h.pair_sup]

/-- The boundary upload converse in every actual user order. -/
theorem boundary_code_lower_permuted [Finite K] {L : ℕ} {m : Three → ℕ} {s : ℕ}
    (T : Task K F) (p : Equiv.Perm Three) (g : Family) (hg : g = .T1 ∨ g = .T2)
    (h : Geometry (reindexTask p T) g)
    (c : T.Code L (fun i => Fin (m i)) (Fin s)) (hL : 0 < L) :
    1 ≤ c.uploadCost := by
  have hA (i : Three) : finrank K (T.A i) = 1 := by
    simpa only [reindexTask,p.apply_symm_apply] using h.side (p.symm i)
  have hd (i j : Three) (hij : i ≠ j) : Disjoint (T.A i) (T.A j) := by
    apply disjoint_iff.mpr
    simpa only [reindexTask,p.apply_symm_apply] using
      h.pair_inf (p.symm i) (p.symm j) (p.symm.injective.ne hij)
  have hs (i j : Three) (hij : i ≠ j) : T.A i ⊔ T.A j = ⊤ := by
    simpa only [reindexTask,p.apply_symm_apply] using
      h.pair_sup (p.symm i) (p.symm j) (p.symm.injective.ne hij)
  have hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j = ⊤ := by
    intro i j hij
    apply top_unique
    rw [←hs i j hij]
    exact sup_le_sup (T.side_le_signal i) (T.side_le_signal j)
  have hint (i j k : Three) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k) = T.U i := by
    simpa only [reindexTask,p.apply_symm_apply] using
      Geometry.pair_intersections_span _ g hg h (p.symm i) (p.symm j) (p.symm k)
        (p.symm.injective.ne hij) (p.symm.injective.ne hik) (p.symm.injective.ne hjk)
  have hj : T.U 2 ⊔ (T.U 0 ⊓ T.U 1) = ⊤ := by
    have hu : T.U 0 ≤ T.U 2 ⊔ (T.U 0 ⊓ T.U 1) := by
      calc
        T.U 0 = (T.U 0 ⊓ T.U 1) ⊔ (T.U 0 ⊓ T.U 2) :=
          (hint 0 1 2 (by decide) (by decide) (by decide)).symm
        _ ≤ T.U 2 ⊔ (T.U 0 ⊓ T.U 1) :=
          sup_le le_sup_right (inf_le_right.trans le_sup_left)
    apply top_unique
    rw [←hp 2 0 (by decide)]
    exact sup_le le_sup_left hu
  have ha : T.A 0 ⊔ T.A 1 ⊔ T.A 2 = ⊤ := by rw [hs 0 1 (by decide),top_sup_eq]
  have hh := GeometricUploadConverse.code_lower T (hd 0 1 (by decide))
    (hd 0 2 (by decide)) (hd 1 2 (by decide)) ha hp hj c hL
  rw [h.ambient,hA,hA,hA] at hh
  norm_num at hh ⊢
  exact hh

lemma boundary_relay_optimal_permuted [Finite K]
    (T : Task K F) (p : Equiv.Perm Three) (g : Family) (hg : g = .T1 ∨ g = .T2)
    (h : Geometry (reindexTask p T) g)
    (P : Submodule K F) (hl : T.LocallyGenerated P) (hf : T.RelayFeasible P)
    (hd : finrank K P = 1) : (finrank K P : ℝ) = T.uploadOptimum := by
  obtain ⟨owner,c,hc⟩ := ResidualOperational.finiteCode_of_local_relay T P hl hf
  letI := c.finite_upload
  letI := c.finite_broadcast
  symm
  apply Task.uploadOptimum_eq_of_code c.toCode (by decide) _ hc
  intro L m s d hL
  rw [hd,Nat.cast_one]
  exact boundary_code_lower_permuted T p g hg h d hL

/-- Every exact Z boundary menu, transported into the original task's six-entry
order and attaining that original task's operational minimum upload. -/
theorem T1_all_permuted_choices [Finite K] (T : Task K F)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (k : Fin 6) (hd : Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) .T1 0)
    (choice : Three) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P = 1 ∧ (finrank K P : ℝ) = T.uploadOptimum ∧
      (∀ r : Fin 6, entry (inducedTask T P hl) (.inl r) = entry T (.inl r) +
        (NonzeroSameChartMenus.menuIncrement .T1 choice (R2PermutedMenus.inverseFirst k r) : ℝ)) ∧
      (∀ i ell : Three, entry (inducedTask T P hl) (.inr (i,ell)) = entry T (.inr (i,ell))) := by
  let p := R2PermutedMenus.pathPerm k
  have hi' := TaskUserPermutation.reindex_indecomposable T p hi
  obtain ⟨P,hl,hf,hr,_,hfirst,hsecond⟩ := T1_all_menu_choices (reindexTask p T) hi' hd choice
  have hl' := (reindex_locallyGenerated T p P).mp hl
  have hf' := (reindex_relayFeasible T p P).mp hf
  have he : inducedTask (reindexTask p T) P hl = reindexTask p (inducedTask T P hl') := rfl
  refine ⟨P,hl',hf',hr,boundary_relay_optimal_permuted T p .T1 (Or.inl rfl)
    (geometry _ hi' .T1 (Or.inl rfl) hd) P hl' hf' hr,?_,?_⟩
  · intro r
    have hh := hfirst (R2PermutedMenus.inverseFirst k r)
    rw [he] at hh
    simpa only [p,R2PermutedMenus.firstEntry_path_reindex] using hh
  · intro i ell
    have hh := hsecond (R2PermutedMenus.inverseUser k i) (R2PermutedMenus.inverseUser k ell)
    rw [he] at hh
    simpa only [p,R2PermutedMenus.secondEntry_path_reindex] using hh

/-- The other low-index survivor preserves all fifteen entries in every arm
order, and its one-dimensional relay is upload-optimal for the original task. -/
theorem T2_permuted_preserving [Finite K] (T : Task K F)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (k : Fin 6) (hd : Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) .T2 0) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P = 1 ∧ (finrank K P : ℝ) = T.uploadOptimum ∧
      ∀ r : Profile.Index, entry (inducedTask T P hl) r = entry T r := by
  let p := R2PermutedMenus.pathPerm k
  have hi' := TaskUserPermutation.reindex_indecomposable T p hi
  obtain ⟨P,hl,hf,hr,_,hprofile⟩ := T2_optimal_preserving (reindexTask p T) hi' hd
  have hl' := (reindex_locallyGenerated T p P).mp hl
  have hf' := (reindex_relayFeasible T p P).mp hf
  have he : inducedTask (reindexTask p T) P hl = reindexTask p (inducedTask T P hl') := rfl
  refine ⟨P,hl',hf',hr,boundary_relay_optimal_permuted T p .T2 (Or.inr rfl)
    (geometry _ hi' .T2 (Or.inr rfl) hd) P hl' hf' hr,?_⟩
  rintro (r | ⟨i,ell⟩)
  · have hh := hprofile (.inl (R2PermutedMenus.inverseFirst k r))
    rw [he] at hh
    simpa only [p,R2PermutedMenus.firstEntry_path_reindex] using hh
  · have hh := hprofile (.inr (R2PermutedMenus.inverseUser k i,R2PermutedMenus.inverseUser k ell))
    rw [he] at hh
    simpa only [p,R2PermutedMenus.secondEntry_path_reindex] using hh

end UploadBroadcast.BoundaryComponentMenus
