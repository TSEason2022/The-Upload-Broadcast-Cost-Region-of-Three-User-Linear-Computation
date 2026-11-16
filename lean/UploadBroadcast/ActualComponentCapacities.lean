import UploadBroadcast.ActualPairCapacities
import UploadBroadcast.PermutedNonzeroAssembly
import UploadBroadcast.BoundaryComponentMenus
import UploadBroadcast.OrientationRepairAllocation

/-! Actual classified component ranks pay the finite scalar menu charges.
The endpoint constructs its capacities from the original fifteen-entry
rank bound; no target pair-capacity or orientation inequality is an input. -/
namespace UploadBroadcast.ActualComponentCapacities
open Module Profile NonzeroDefectProfile NonzeroFamilyRanks
open BinaryMenuAllocation ActualPairCapacities R2PermutedMenus
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

/-- Charge zero for the profile-preserving low-index exceptions. -/
def charge_for_family (g : NonzeroDefectProfile.Family) (n : ℕ) (j : Fin 3) : ℤ :=
  if n = 0 then
    if g = .T1 then NonzeroFiniteAssembly.charge (.hyperplane .T1) j else 0
  else if n = 1 ∧ (g = .T3 ∨ g = .H ∨ g = .R2) then 0
  else NonzeroFiniteAssembly.charge (PermutedNonzeroAssembly.ofFamily g) j

/-- Pair charges in the original, unpermuted user order. -/
def charge (g : NonzeroDefectProfile.Family) (n : ℕ) (k : Fin 6) (j : Fin 3) : ℤ :=
  charge_for_family g n (PermutedNonzeroAssembly.pairIndex k j)

abbrev permuted_charge := charge

theorem charge_nonneg (g : NonzeroDefectProfile.Family) (n : ℕ) (k : Fin 6) (j : Fin 3) :
    0 ≤ charge g n k j := by
  unfold charge charge_for_family
  split_ifs <;> first | exact le_refl _ | exact NonzeroFiniteAssembly.charge_nonneg _ _

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Full actual family profiles, including the small profile-preserving
exceptions, dominate exactly the charges used by scalar menu selection. -/
theorem positive_charge_le_margin (T : Task K V)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : NonzeroDefectProfile.Family) (n : ℕ) (hn : 1 ≤ n)
    (h : Dimensions T g n) (p : Fin 3) :
    (charge_for_family g n p : ℝ) ≤ ActualPairCapacities.margin T p := by
  by_cases he : n = 1 ∧ (g = .T3 ∨ g = .H ∨ g = .R2)
  · simpa [charge_for_family,show n ≠ 0 by omega,he] using margin_nonneg T p
  have hm : (charge_for_family g n p : ℝ) =
      (NonzeroFiniteAssembly.charge (PermutedNonzeroAssembly.ofFamily g) p : ℝ) := by
    simp [charge_for_family,show n ≠ 0 by omega,he]
  rw [hm]
  unfold ActualPairCapacities.margin
  obtain ⟨i,ell⟩ := secondIndex p
  rw [full_second_profile T hT g n hn h i ell,
    full_first_profile T hT g n hn h,full_first_profile T hT g n hn h]
  have ha : NonzeroFiniteAssembly.charge (PermutedNonzeroAssembly.ofFamily g) p+
      ((fullFirst g n (pairLeft p) : ℤ)+fullFirst g n (pairRight p)) ≤
      (doubledSecond g n : ℤ) := by
    cases g <;> fin_cases p <;>
      simp_all [NonzeroFiniteAssembly.charge,PermutedNonzeroAssembly.ofFamily,
        NonzeroBinaryMenus.extraFamily,BinaryMenuAllocation.charge,
        fullFirst,doubledSecond,pairLeft,pairRight] <;> omega
  have hr : (NonzeroFiniteAssembly.charge (PermutedNonzeroAssembly.ofFamily g) p : ℝ)+
      ((fullFirst g n (pairLeft p) : ℝ)+fullFirst g n (pairRight p)) ≤
      doubledSecond g n := by exact_mod_cast ha
  linarith only [hr]

/-- The boundary T1 charge is computed from actual plane geometry. T2 is
profile-preserving and therefore needs no charge. -/
theorem boundary_charge_le_margin (T : Task K V)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : NonzeroDefectProfile.Family) (hg : g = .T1 ∨ g = .T2)
    (h : Dimensions T g 0) (p : Fin 3) :
    (charge_for_family g 0 p : ℝ) ≤ ActualPairCapacities.margin T p := by
  rcases hg with rfl | rfl
  · have hp := BoundaryComponentMenus.T1_exact_profile T
      (BoundaryComponentMenus.geometry T hT .T1 (Or.inl rfl) h) 1 (Or.inl rfl)
    unfold ActualPairCapacities.margin
    obtain ⟨i,ell⟩ := secondIndex p
    rw [(hp.2.2 i ell).1,hp.1,hp.1]
    fin_cases p <;> norm_num [charge_for_family,NonzeroFiniteAssembly.charge,pairLeft,pairRight]
    all_goals first | exact le_refl _ | (change (0 : ℝ)+0 ≤ 0; norm_num)
  · simpa [charge_for_family] using margin_nonneg T p

/-- Opposite pairs are permuted as unordered pairs by the actual user relabeling. -/
theorem inverse_pair (k : Fin 6) (p : Fin 3) :
    (inverseFirst k (pairLeft p)=pairLeft (PermutedNonzeroAssembly.pairIndex k p) ∧
     inverseFirst k (pairRight p)=pairRight (PermutedNonzeroAssembly.pairIndex k p)) ∨
    (inverseFirst k (pairLeft p)=pairRight (PermutedNonzeroAssembly.pairIndex k p) ∧
     inverseFirst k (pairRight p)=pairLeft (PermutedNonzeroAssembly.pairIndex k p)) := by
  fin_cases k <;> fin_cases p <;> decide

theorem inverse_secondIndex (k : Fin 6) (p : Fin 3) :
    secondIndex (PermutedNonzeroAssembly.pairIndex k p) =
      (inverseUser k (secondIndex p).1,inverseUser k (secondIndex p).2) := by
  fin_cases k <;> fin_cases p <;> decide

/-- Conditional-rank margins transform with the same pair permutation as
menu charges, with no symmetry assumption on the task. -/
theorem margin_reindex (T : Task K V) (k : Fin 6) (p : Fin 3) :
    ActualPairCapacities.margin (reindexTask (pathPerm k) T)
      (PermutedNonzeroAssembly.pairIndex k p) = ActualPairCapacities.margin T p := by
  unfold ActualPairCapacities.margin
  rw [inverse_secondIndex,secondEntry_path_reindex]
  rcases inverse_pair k p with ⟨hL,hR⟩ | ⟨hL,hR⟩
  · rw [←hL,←hR,firstEntry_path_reindex,firstEntry_path_reindex]
  · rw [←hR,←hL,firstEntry_path_reindex,firstEntry_path_reindex]
    ring

/-- Raw family dimensions in any user order supply the actual charge bound,
including all active low-index survivors and small exceptional components. -/
theorem classified_charge_le_margin (T : Task K V)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : NonzeroDefectProfile.Family) (n : ℕ) (k : Fin 6)
    (hn : 1 ≤ n ∨ (n = 0 ∧ (g = .T1 ∨ g = .T2)))
    (h : Dimensions (reindexTask (pathPerm k) T) g n) (p : Fin 3) :
    (charge g n k p : ℝ) ≤ ActualPairCapacities.margin T p := by
  rw [←margin_reindex T k p]
  have hi := TaskUserPermutation.reindex_indecomposable T (pathPerm k) hT
  rcases hn with hn | ⟨rfl,hg⟩
  · exact positive_charge_le_margin _ hi g n hn h _
  · exact boundary_charge_le_margin _ hi g hg h _

section FiniteComponents
variable {I R W : Type} [Fintype I] [Fintype R] {F : I → Type}
  [∀ t, AddCommGroup (F t)] [∀ t, Module K (F t)] [∀ t, FiniteDimensional K (F t)]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The original full task, including resonant blocks and any uncharged
profile-preserving remainder. The remainder is not required to have zero margin. -/
abbrev fullTask (nR : R → ℕ) (T : (t : I) → Task K (F t)) (Z : Task K W) :=
  Profile.directSum (ResonantFiniteAssembly.task (K := K) nR)
    (Profile.directSum (FiniteRelayAssembly.task T) Z)

def totalCharge (g : I → NonzeroDefectProfile.Family) (n : I → ℕ) (k : I → Fin 6)
    (p : Fin 3) : ℤ := ∑ t, charge (g t) (n t) (k t) p

theorem totalCharge_nonneg (g : I → NonzeroDefectProfile.Family) (n : I → ℕ)
    (k : I → Fin 6) (p : Fin 3) : 0 ≤ totalCharge g n k p :=
  Finset.sum_nonneg (fun t _ => charge_nonneg (g t) (n t) (k t) p)

/-- Every original resonant copy contributes one unit to every pair;
its additional margin is kept rather than discarded by an assumption. -/
theorem resonant_count_le_margin (nR : R → ℕ) (p : Fin 3) :
    (Fintype.card R : ℝ) ≤ ActualPairCapacities.margin
      (ResonantFiniteAssembly.task (K := K) nR) p := by
  rw [margin_finite_task]
  have h : (∑ _t : R, (1 : ℝ)) ≤ ∑ t : R, ActualPairCapacities.margin
      (ResonantRelay.jordanTask K (nR t)) p := by
    apply Finset.sum_le_sum
    intro t _
    rw [resonant_margin]
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  simpa using h

/-- The strengthened pair reservation is derived from actual component
geometry and the full task's original fifteen-entry rank bound. -/
theorem strengthened_capacities (nR : R → ℕ) (T : (t : I) → Task K (F t)) (Z : Task K W)
    (hT : ∀ t, TaskDecomposition.Indecomposable (EdgeExtraction.configuration (T t)).spaces ⊤)
    (g : I → NonzeroDefectProfile.Family) (n : I → ℕ) (k : I → Fin 6)
    (hn : ∀ t, 1 ≤ n t ∨ (n t = 0 ∧ (g t = .T1 ∨ g t = .T2)))
    (h : ∀ t, Dimensions (reindexTask (pathPerm (k t)) (T t)) (g t) (n t))
    (D : ℤ) (hD : rankBound (fullTask nR T Z) ≤ (D : ℝ)) :
    ∀ p, (Fintype.card R : ℤ)+totalCharge g n k p ≤
      capacity (fullTask nR T Z) D (pairLeft p)+capacity (fullTask nR T Z) D (pairRight p) := by
  apply charge_fits_capacity (fullTask nR T Z) D hD
    (fun p => (Fintype.card R : ℤ)+totalCharge g n k p)
  intro p
  have hr := resonant_count_le_margin (K := K) nR p
  have hz := margin_nonneg Z p
  have ht : (totalCharge g n k p : ℝ) ≤
      ActualPairCapacities.margin (FiniteRelayAssembly.task T) p := by
    rw [margin_finite_task]
    simp only [totalCharge,Int.cast_sum]
    exact Finset.sum_le_sum (fun t _ => classified_charge_le_margin
      (T t) (hT t) (g t) (n t) (k t) (hn t) (h t) p)
  simp only [fullTask,margin_directSum,Int.cast_add,Int.cast_natCast]
  linarith only [hr,hz,ht]

/-- Actual-input six-capacity endpoint. Integer slacks, nonnegativity,
strengthened pair budgets, and all nine second-entry bounds are conclusions. -/
theorem actual_integer_capacities (nR : R → ℕ) (T : (t : I) → Task K (F t)) (Z : Task K W)
    (hT : ∀ t, TaskDecomposition.Indecomposable (EdgeExtraction.configuration (T t)).spaces ⊤)
    (g : I → NonzeroDefectProfile.Family) (n : I → ℕ) (k : I → Fin 6)
    (hn : ∀ t, 1 ≤ n t ∨ (n t = 0 ∧ (g t = .T1 ∨ g t = .T2)))
    (h : ∀ t, Dimensions (reindexTask (pathPerm (k t)) (T t)) (g t) (n t))
    (D : ℤ) (hD : rankBound (fullTask nR T Z) ≤ (D : ℝ)) :
    ∃ c : Fin 6 → ℤ,
      (∀ j, 0 ≤ c j) ∧
      (∀ j, entry (fullTask nR T Z) (.inl j)+(c j : ℝ)=D) ∧
      (∀ p, (Fintype.card R : ℤ)+totalCharge g n k p ≤ c (pairLeft p)+c (pairRight p)) ∧
      (∀ r : Three × Three, entry (fullTask nR T Z) (.inr r) ≤ D) := by
  refine ⟨capacity (fullTask nR T Z) D,capacity_nonneg _ D hD,?_,
    strengthened_capacities nR T Z hT g n k hn h D hD,?_⟩
  · intro j
    rw [capacity_cast]
    ring
  · intro r
    exact (entry_le_rankBound _ (.inr r)).trans hD

/-- The paper's orientation repair uses the capacities just derived from
actual inputs; both orientation inequalities and surviving pair budgets are
outputs. The exact reserved first-entry increment is kept explicitly. -/
theorem repaired_actual_capacities (nR : R → ℕ) (T : (t : I) → Task K (F t)) (Z : Task K W)
    (hT : ∀ t, TaskDecomposition.Indecomposable (EdgeExtraction.configuration (T t)).spaces ⊤)
    (g : I → NonzeroDefectProfile.Family) (n : I → ℕ) (k : I → Fin 6)
    (hn : ∀ t, 1 ≤ n t ∨ (n t = 0 ∧ (g t = .T1 ∨ g t = .T2)))
    (h : ∀ t, Dimensions (reindexTask (pathPerm (k t)) (T t)) (g t) (n t))
    (D : ℤ) (hD : rankBound (fullTask nR T Z) ≤ (D : ℝ)) :
    let c := capacity (fullTask nR T Z) D
    let m : ℤ := Fintype.card R
    let a := OrientationRepairAllocation.positiveCount m c
    let b := OrientationRepairAllocation.negativeCount m c
    let c' := OrientationRepairAllocation.repaired m c
    0 ≤ a ∧ 0 ≤ b ∧ a+b ≤ m ∧ (a=0 ∨ b=0) ∧
    (∀ j, 0 ≤ c' j) ∧
    (∀ p, m-a-b+totalCharge g n k p ≤ c' (pairLeft p)+c' (pairRight p)) ∧
    m-a-b ≤ OrientationRepairAllocation.plus c' ∧
    m-a-b ≤ OrientationRepairAllocation.minus c' := by
  have hp := strengthened_capacities nR T Z hT g n k hn h D hD
  exact OrientationRepairAllocation.repaired_capacities _ _ _ (Nat.cast_nonneg _)
    (totalCharge_nonneg g n k) (capacity_nonneg _ D hD) hp
    (OrientationRepairAllocation.sum_capacity _ _ _ (totalCharge_nonneg g n k) hp)

end FiniteComponents
end UploadBroadcast.ActualComponentCapacities
