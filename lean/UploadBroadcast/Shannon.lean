import UploadBroadcast.EntropyCalculus
import PFR.ForMathlib.Entropy.Basic

/-!
# Concrete finite Shannon entropy

Here the entropy-function laws used in the converse are proved for the
Shannon entropy of actual observations on a finite probability space. The
underlying entropy is PFR's `ProbabilityTheory.entropy`, defined by the sum of
`-p * log p` over the pushforward distribution, not an uninterpreted symbol.
Natural-number-valued coordinates allow every finite alphabet to be encoded.
-/
namespace UploadBroadcast
open MeasureTheory ProbabilityTheory

instance (priority := 100) finiteRange_of_finite_domain
    {Ω T : Type*} [Finite Ω] (f : Ω → T) : FiniteRange f :=
  ⟨Set.finite_range f⟩

namespace Shannon
variable {Ω ι : Type*} [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  [Fintype ι] [DecidableEq ι]

/-- A collection of finite-alphabet observations, padded by zero outside `A`.
Padding is only an encoding; it contributes no entropy. -/
def observe (X : Ω → ι → ℕ) (A : Finset ι) : Ω → (ι → ℕ) :=
  fun ω i => if i ∈ A then X ω i else 0

def restrict (A : Finset ι) (v : ι → ℕ) : ι → ℕ :=
  fun i => if i ∈ A then v i else 0

omit [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] [Fintype ι] in
lemma observe_subset (X : Ω → ι → ℕ) {A B : Finset ι} (hab : A ⊆ B) :
    observe X A = restrict A ∘ observe X B := by
  funext ω i
  by_cases hi : i ∈ A
  · simp [observe, restrict, hi, hab hi]
  · simp [observe, restrict, hi]

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ι → ℕ)

/-- The joint Shannon entropy of a finite collection of named observations. -/
noncomputable def value (A : Finset ι) : ℝ := entropy (observe X A) μ

omit [Fintype Ω] [DiscreteMeasurableSpace Ω] in
lemma value_empty : value μ X ∅ = 0 := by
  change entropy (fun _ : Ω => (fun _ : ι => 0)) μ = 0
  exact entropy_const _

lemma value_mono : Monotone (value μ X) := by
  intro A B hab
  unfold value
  rw [observe_subset X hab]
  exact entropy_comp_le μ (Measurable.of_discrete) _

lemma value_union (A B : Finset ι) :
    value μ X (A ∪ B) = entropy (fun ω => (observe X A ω, observe X B ω)) μ := by
  apply entropy_of_comp_eq_of_comp μ Measurable.of_discrete Measurable.of_discrete
    (fun v => (restrict A v, restrict B v))
    (fun p i => if i ∈ A then p.1 i else p.2 i)
  · funext ω
    apply Prod.ext
    · exact congrFun (observe_subset X (Finset.subset_union_left (s₁ := A) (s₂ := B))) ω
    · exact congrFun (observe_subset X (Finset.subset_union_right (s₁ := A) (s₂ := B))) ω
  · funext ω i
    by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;>
      simp [observe, ha, hb]

omit [IsProbabilityMeasure μ] [Fintype Ω] in
lemma value_pair_of_subset {A B : Finset ι} (hba : B ⊆ A) :
    entropy (fun ω => (observe X A ω, observe X B ω)) μ = value μ X A := by
  rw [observe_subset X hba]
  exact entropy_prod_comp Measurable.of_discrete μ (restrict B)

lemma value_submod (A B : Finset ι) :
    value μ X (A ∪ B) + value μ X (A ∩ B) ≤ value μ X A + value μ X B := by
  have hs := entropy_triple_add_entropy_le μ
    (X := observe X A) (Y := observe X B) (Z := observe X (A ∩ B))
    Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
  have hp := entropy_comp_le μ
    (X := fun ω => (observe X A ω, (observe X B ω, observe X (A ∩ B) ω)))
    Measurable.of_discrete (fun p => (p.1, p.2.1))
  change entropy (fun ω => (observe X A ω, observe X B ω)) μ ≤ _ at hp
  rw [value_pair_of_subset μ X Finset.inter_subset_left,
      value_pair_of_subset μ X Finset.inter_subset_right] at hs
  rw [← value_union μ X A B] at hp
  change _ + value μ X (A ∩ B) ≤ _ at hs
  linarith

/-- A proved instance of the entropy-function laws for concrete Shannon entropy.
No information-theoretic axioms are added. -/
noncomputable def entropyFunction : EntropyFunction ι where
  value := value μ X
  empty := value_empty μ X
  mono := value_mono μ X
  submod := value_submod μ X

/-- The conditional set entropy is exactly PFR's actual conditional entropy. -/
lemma condition_eq_condEntropy (A C : Finset ι) :
    (entropyFunction μ X).condition C A =
      condEntropy (observe X A) (observe X C) μ := by
  change value μ X (A ∪ C) - value μ X C = _
  rw [value_union, chain_rule'' μ Measurable.of_discrete Measurable.of_discrete]
  rfl

/-- The set-function mutual information is exactly actual Shannon mutual
information, making its independence semantics explicit. -/
lemma mutual_eq (A B : Finset ι) :
    (entropyFunction μ X).Mutual A B =
      mutualInfo (observe X A) (observe X B) μ := by
  unfold EntropyFunction.Mutual
  change value μ X A + value μ X B - value μ X (A ∪ B) = _
  rw [value_union]
  rfl

lemma value_union_triple (A B C : Finset ι) :
    value μ X (A ∪ B ∪ C) =
      entropy (fun ω => ((observe X A ω, observe X B ω), observe X C ω)) μ := by
  apply entropy_of_comp_eq_of_comp μ Measurable.of_discrete Measurable.of_discrete
    (fun v => ((restrict A v, restrict B v), restrict C v))
    (fun p i => if i ∈ A then p.1.1 i else if i ∈ B then p.1.2 i else p.2 i)
  · funext ω
    apply Prod.ext
    · apply Prod.ext
      · exact congrFun (observe_subset X (by
          intro i hi; simp only [Finset.mem_union]; exact Or.inl (Or.inl hi))) ω
      · exact congrFun (observe_subset X (by
          intro i hi; simp only [Finset.mem_union]; exact Or.inl (Or.inr hi))) ω
    · exact congrFun (observe_subset X Finset.subset_union_right) ω
  · funext ω i
    by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> by_cases hc : i ∈ C <;>
      simp [observe, ha, hb, hc]

/-- The conditional mutual information in the set calculus agrees exactly
with PFR's Shannon conditional mutual information, not merely its sign. -/
lemma condMutual_eq (A B C : Finset ι) :
    (entropyFunction μ X).CondMutual A B C =
      condMutualInfo (observe X A) (observe X B) (observe X C) μ := by
  rw [condMutualInfo_eq Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete]
  rw [chain_rule'' μ Measurable.of_discrete Measurable.of_discrete,
      chain_rule'' μ Measurable.of_discrete Measurable.of_discrete,
      chain_rule'' μ Measurable.of_discrete Measurable.of_discrete]
  rw [← value_union μ X A C, ← value_union μ X B C, ← value_union_triple μ X A B C]
  change value μ X (A ∪ C) + value μ X (B ∪ C) - value μ X C -
    value μ X (A ∪ B ∪ C) = _
  change _ = (value μ X (A ∪ C) - value μ X C) +
    (value μ X (B ∪ C) - value μ X C) -
    (value μ X (A ∪ B ∪ C) - value μ X C)
  ring

/-- Information-theoretic functional dependence is conditional entropy zero. -/
lemma determines_iff (A B : Finset ι) :
    (entropyFunction μ X).Determines A B ↔
      condEntropy (observe X B) (observe X A) μ = 0 := by
  rw [← condition_eq_condEntropy]
  change value μ X (A ∪ B) = value μ X A ↔
    value μ X (B ∪ A) - value μ X A = 0
  rw [Finset.union_comm B A]
  exact sub_eq_zero.symm

/-- The conditioned functional-dependence predicate means recoverability
from the conditioning observations together with the local observations. -/
lemma condition_determines_iff (O A B : Finset ι) :
    ((entropyFunction μ X).condition O).Determines A B ↔
      condEntropy (observe X B) (observe X (A ∪ O)) μ = 0 := by
  rw [← determines_iff μ X (A ∪ O) B]
  change (value μ X ((A ∪ B) ∪ O) - value μ X O = value μ X (A ∪ O) - value μ X O) ↔
    value μ X ((A ∪ O) ∪ B) = value μ X (A ∪ O)
  have heq : (A ∪ B) ∪ O = (A ∪ O) ∪ B := by
    simp only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
  rw [heq]
  exact sub_left_inj

/-- Conditional independence agrees with additivity of the conditioned
entropy set function. -/
lemma condition_independent_iff (O A B : Finset ι) :
    (entropyFunction μ X).condition O (A ∪ B) =
      (entropyFunction μ X).condition O A + (entropyFunction μ X).condition O B ↔
    CondIndepFun (observe X A) (observe X B) (observe X O) μ := by
  rw [← condMutualInfo_eq_zero Measurable.of_discrete Measurable.of_discrete,
      ← condMutual_eq μ X A B O]
  change (value μ X ((A ∪ B) ∪ O) - value μ X O =
    (value μ X (A ∪ O) - value μ X O) + (value μ X (B ∪ O) - value μ X O)) ↔
    value μ X (A ∪ O) + value μ X (B ∪ O) - value μ X O -
      value μ X (A ∪ B ∪ O) = 0
  constructor <;> intro h <;> linarith

/-- Retained conditional mutual information after conditioning the entropy
function includes the common conditioning observations exactly once. -/
lemma condition_condMutual_eq (O A B C : Finset ι) :
    ((entropyFunction μ X).condition O).CondMutual A B C =
      condMutualInfo (observe X A) (observe X B) (observe X (C ∪ O)) μ := by
  rw [← condMutual_eq]
  change (value μ X ((A ∪ C) ∪ O) - value μ X O) +
    (value μ X ((B ∪ C) ∪ O) - value μ X O) -
    (value μ X (C ∪ O) - value μ X O) -
    (value μ X ((A ∪ B ∪ C) ∪ O) - value μ X O) = _
  change _ = value μ X (A ∪ (C ∪ O)) + value μ X (B ∪ (C ∪ O)) -
    value μ X (C ∪ O) - value μ X (A ∪ B ∪ (C ∪ O))
  simp only [Finset.union_assoc]
  ring

end Shannon
end UploadBroadcast
