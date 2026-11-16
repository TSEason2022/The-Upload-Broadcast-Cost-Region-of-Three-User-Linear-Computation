import UploadBroadcast.BinaryExactFamilyMenus
import UploadBroadcast.NonzeroSameChartOptimality
import UploadBroadcast.NonzeroExceptionalRelays

/-! The binary menus attain the genuine operational upload infimum, including
arbitrary nonlinear competitors and every positive blocklength. -/
namespace UploadBroadcast.BinaryMenuOptimality
open Module Profile NonzeroDefectRelays NonzeroDefectProfile NonzeroFamilyRanks
open NonzeroBinaryMenus
variable {K F : Type} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

theorem codimension_one_optimal (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Kind) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T (family g) n)
    (P : Submodule K F) (hg : T.LocallyGenerated P) (hf : T.RelayFeasible P)
    (hd : finrank K P=fullAmbient (family g) n-1) :
    (finrank K P : ℝ)=T.uploadOptimum := by
  apply NonzeroSameChartOptimality.relay_rank_eq_uploadOptimum T hT (family g) n hn h P hg hf
  simpa [codimension,show family g ≠ .R2 by cases g <;> decide] using hd

theorem original_exact_optimal_menu (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Kind) (hg : g=.T1 ∨ g=.O) (n : ℕ) (hn : 1 ≤ n)
    (h : Dimensions T (family g) n) (k : Fin 6) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (finrank K P : ℝ)=T.uploadOptimum ∧
      (∀ r : Fin 6, entry (inducedTask T P hl) (.inl r)=entry T (.inl r)+(menu g k r : ℝ)) ∧
      (∀ r : Three × Three, entry (inducedTask T P hl) (.inr r)=entry T (.inr r)) := by
  obtain ⟨P,hl,hf,hd,he,hq⟩ := BinaryExactFamilyMenus.full_original_binary_exact_menu T hT g hg n hn h k
  exact ⟨P,hl,hf,codimension_one_optimal T hT g n hn h P hl hf hd,he,hq⟩

theorem additional_optimal_menu (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Kind) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T (family g) n) (k : Fin 6) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (finrank K P : ℝ)=T.uploadOptimum ∧
      (∀ r : Fin 6, entry (inducedTask T P hl) (.inl r) ≤ entry T (.inl r)+(menu g k r : ℝ)) ∧
      (∀ r : Three × Three, entry (inducedTask T P hl) (.inr r)=entry T (.inr r)) := by
  obtain ⟨P,hl,hf,hd,he,hq⟩ := full_binary_menu T hT g n hn h k
  exact ⟨P,hl,hf,codimension_one_optimal T hT g n hn h P hl hf hd,he,hq⟩

theorem additional_optimal_fits_capacity (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Kind) (hT1 : g ≠ .T1) (hO : g ≠ .O)
    (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T (family g) n) (c : Fin 6 → ℕ)
    (hcap : ∀ p : Fin 3, BinaryMenuAllocation.charge (extraFamily g) p ≤
      c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p)) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (finrank K P : ℝ)=T.uploadOptimum ∧
      (∀ r : Fin 6, entry (inducedTask T P hl) (.inl r) ≤ entry T (.inl r)+(c r : ℝ)) ∧
      (∀ r : Three × Three, entry (inducedTask T P hl) (.inr r)=entry T (.inr r)) := by
  obtain ⟨P,hl,hf,hd,he,hq⟩ := full_extra_menu_fits T hT g hT1 hO n hn h c hcap
  exact ⟨P,hl,hf,codimension_one_optimal T hT g n hn h P hl hf hd,he,hq⟩

theorem r2_optimal_menu (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T .R2 n) (k : Fin 6) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (finrank K P : ℝ)=T.uploadOptimum ∧
      (∀ r : Fin 6, entry (inducedTask T P hl) (.inl r) ≤
        entry T (.inl r)+(BinaryMenuAllocation.menu .R2 k r : ℝ)) ∧
      (∀ r : Three × Three, entry (inducedTask T P hl) (.inr r)=entry T (.inr r)) := by
  obtain ⟨P,hl,hf,hd,he,hq⟩ := R2PermutedMenus.full_binary_R2_menu T hT n hn h k
  refine ⟨P,hl,hf,?_,he,hq⟩
  apply NonzeroSameChartOptimality.relay_rank_eq_uploadOptimum T hT .R2 n hn h P hl hf
  norm_num [fullAmbient,codimension]
  omega

theorem small_exceptions_optimal (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (hg : g=.H ∨ g=.R2) (h : Dimensions T g 1) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (finrank K P : ℝ)=T.uploadOptimum ∧
      ∀ r : Index, entry (inducedTask T P hl) r ≤ entry T r := by
  obtain ⟨P,hl,hf,hd,he⟩ := NonzeroExceptionalRelays.full_small_exception_profile T hT g hg h
  refine ⟨P,hl,hf,?_,he⟩
  apply NonzeroSameChartOptimality.relay_rank_eq_uploadOptimum T hT g 1 (by decide) h P hl hf
  rcases hg with rfl | rfl <;> simpa [fullAmbient,codimension] using hd

theorem tripod_exception_optimal (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (h : Dimensions T .T3 1) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (finrank K P : ℝ)=T.uploadOptimum ∧
      ∀ r : Index, entry (inducedTask T P hl) r ≤ entry T r := by
  obtain ⟨P,hl,hf,hd,he⟩ := NonzeroExceptionalRelays.full_tripod_exception_profile T hT h
  refine ⟨P,hl,hf,?_,he⟩
  apply NonzeroSameChartOptimality.relay_rank_eq_uploadOptimum T hT .T3 1 (by decide) h P hl hf
  simpa [fullAmbient,codimension] using hd

omit [Finite K] in
/-- Actual first/second profile margins dominate every tabulated charge. -/
theorem charge_le_actual_margin (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Kind) (hT1 : g≠.T1) (hO : g≠.O) (n : ℕ)
    (hn : BinaryMenuAllocation.minimumParameter (extraFamily g) ≤ n)
    (h : Dimensions T (family g) n) (p : Three) (i ell : Three) :
    (BinaryMenuAllocation.charge (extraFamily g) p : ℝ) ≤
      2*entry T (.inr (i,ell))-
        (entry T (.inl (BinaryMenuAllocation.pairLeft p))+
         entry T (.inl (BinaryMenuAllocation.pairRight p))) := by
  have hn1 : 1 ≤ n := by cases g <;> simp_all [extraFamily,BinaryMenuAllocation.minimumParameter] <;> omega
  rw [full_second_profile T hT (family g) n hn1 h i ell,
    full_first_profile T hT (family g) n hn1 h,
    full_first_profile T hT (family g) n hn1 h]
  have ha : BinaryMenuAllocation.charge (extraFamily g) p+
      (fullFirst (family g) n (BinaryMenuAllocation.pairLeft p)+
       fullFirst (family g) n (BinaryMenuAllocation.pairRight p)) ≤ doubledSecond (family g) n := by
    cases g <;> fin_cases p <;>
      simp_all [family,extraFamily,BinaryMenuAllocation.charge,BinaryMenuAllocation.minimumParameter,
        BinaryMenuAllocation.pairLeft,BinaryMenuAllocation.pairRight,fullFirst,doubledSecond] <;> omega
  have hr : (BinaryMenuAllocation.charge (extraFamily g) p : ℝ)+
      ((fullFirst (family g) n (BinaryMenuAllocation.pairLeft p) : ℝ)+
       fullFirst (family g) n (BinaryMenuAllocation.pairRight p)) ≤ doubledSecond (family g) n := by
    exact_mod_cast ha
  linarith

omit [Finite K] in
/-- R2's one-unit charge in each opposite pair is also an actual profile margin. -/
theorem r2_charge_le_actual_margin (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (n : ℕ) (hn : 2 ≤ n) (h : Dimensions T .R2 n) (p : Three) (i ell : Three) :
    (1:ℝ) ≤ 2*entry T (.inr (i,ell))-
      (entry T (.inl (BinaryMenuAllocation.pairLeft p))+
       entry T (.inl (BinaryMenuAllocation.pairRight p))) := by
  rw [full_second_profile T hT .R2 n (by omega) h i ell,
    full_first_profile T hT .R2 n (by omega) h,
    full_first_profile T hT .R2 n (by omega) h]
  have ha : 1+(fullFirst .R2 n (BinaryMenuAllocation.pairLeft p)+
      fullFirst .R2 n (BinaryMenuAllocation.pairRight p)) ≤ doubledSecond .R2 n := by
    fin_cases p <;> simp [fullFirst,doubledSecond,BinaryMenuAllocation.pairLeft,
      BinaryMenuAllocation.pairRight] <;> omega
  have hr : (1:ℝ)+((fullFirst .R2 n (BinaryMenuAllocation.pairLeft p) : ℝ)+
      fullFirst .R2 n (BinaryMenuAllocation.pairRight p)) ≤ doubledSecond .R2 n := by exact_mod_cast ha
  linarith

theorem r2_optimal_fits_capacity (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (n : ℕ) (hn : 2 ≤ n) (h : Dimensions T .R2 n) (c : Fin 6 → ℕ)
    (hcap : ∀ p : Three, 1 ≤ c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p)) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (finrank K P : ℝ)=T.uploadOptimum ∧
      (∀ r : Fin 6, entry (inducedTask T P hl) (.inl r) ≤ entry T (.inl r)+(c r : ℝ)) ∧
      (∀ r : Three × Three, entry (inducedTask T P hl) (.inr r)=entry T (.inr r)) := by
  obtain ⟨k,hk⟩ := BinaryMenuAllocation.menu_fits .R2 c (by
    intro p
    have hh := hcap p
    fin_cases p <;> simpa [BinaryMenuAllocation.charge] using hh)
  obtain ⟨P,hl,hf,hu,he,hq⟩ := r2_optimal_menu T hT n (by omega) h k
  refine ⟨P,hl,hf,hu,?_,hq⟩
  intro r
  exact (he r).trans (add_le_add_left (by exact_mod_cast hk r) _)

end UploadBroadcast.BinaryMenuOptimality
