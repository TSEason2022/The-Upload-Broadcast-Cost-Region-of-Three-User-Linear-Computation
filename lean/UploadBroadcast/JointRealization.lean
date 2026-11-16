import UploadBroadcast.FiniteEntropyConverse

/-! Reduction from an arbitrary underlying sample space to the finite joint
alphabet. This avoids assuming the original probability sample space is finite.
The joint observation must have finite range, exactly the finite-alphabet
hypothesis for finitely many observations. -/
namespace UploadBroadcast.Shannon
open MeasureTheory ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ι → ℕ)

/-- Send an outcome to its value in the joint observation alphabet. -/
def realize : Ω → Set.range X := fun ω => ⟨X ω, ⟨ω, rfl⟩⟩

/-- The distribution of the entire joint observation, supported on its range. -/
noncomputable def realizeLaw : Measure (Set.range X) := μ.map (realize X)

omit [Fintype ι] [DecidableEq ι] in
lemma measurable_realize (hX : Measurable X) : Measurable (realize X) := hX.subtype_mk

omit [Fintype ι] [DecidableEq ι] in
lemma realizeLaw_probability (hX : Measurable X) : IsProbabilityMeasure (realizeLaw μ X) :=
  isProbabilityMeasure_map (measurable_realize X hX).aemeasurable

omit [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι] in
lemma identDistrib_realize (hX : Measurable X) :
    IdentDistrib X (Subtype.val : Set.range X → ι → ℕ) μ (realizeLaw μ X) := by
  refine ⟨hX.aemeasurable, measurable_subtype_coe.aemeasurable, ?_⟩
  change μ.map X = (μ.map (realize X)).map Subtype.val
  rw [Measure.map_map measurable_subtype_coe (measurable_realize X hX)]
  rfl

omit [IsProbabilityMeasure μ] in
/-- Entropy of every subcollection is preserved by finite joint realization. -/
lemma value_realize (hX : Measurable X) (A : Finset ι) :
    value μ X A = value (realizeLaw μ X) (Subtype.val : Set.range X → ι → ℕ) A := by
  exact ((identDistrib_realize μ X hX).comp (u := restrict A) Measurable.of_discrete).entropy_congr

variable [FiniteRange X]

noncomputable local instance : Fintype (Set.range X) := FiniteRange.fintype X

omit [FiniteRange X] in
lemma observe_measurable (hX : Measurable X) (A : Finset ι) : Measurable (observe X A) :=
  (Measurable.of_discrete (f := restrict A)).comp hX

instance observe_finiteRange (A : Finset ι) : FiniteRange (observe X A) :=
  inferInstanceAs (FiniteRange (restrict A ∘ X))

/-- Conditional entropy of every subcollection is preserved by realization. -/
lemma cvalue_realize (hX : Measurable X) (A C : Finset ι) :
    cvalue μ X A C = cvalue (realizeLaw μ X) (Subtype.val : Set.range X → ι → ℕ) A C := by
  letI : Fintype (Set.range X) := FiniteRange.fintype X
  letI : FiniteRange (Subtype.val : Set.range X → ι → ℕ) := ⟨Set.finite_range _⟩
  letI := realizeLaw_probability μ X hX
  apply IdentDistrib.condEntropy_eq
    (X' := observe (Subtype.val : Set.range X → ι → ℕ) A)
    (Y' := observe (Subtype.val : Set.range X → ι → ℕ) C)
    (μ' := realizeLaw μ X) (observe_measurable X hX A) (observe_measurable X hX C)
    Measurable.of_discrete Measurable.of_discrete
  exact (identDistrib_realize μ X hX).comp
    (u := fun v => (restrict A v, restrict C v)) Measurable.of_discrete

/-- Conditional mutual information is preserved by joint realization. -/
lemma cinfo_realize (hX : Measurable X) (A B C : Finset ι) :
    cinfo μ X A B C =
      cinfo (realizeLaw μ X) (Subtype.val : Set.range X → ι → ℕ) A B C := by
  letI : Fintype (Set.range X) := FiniteRange.fintype X
  letI : FiniteRange (Subtype.val : Set.range X → ι → ℕ) := ⟨Set.finite_range _⟩
  letI := realizeLaw_probability μ X hX
  unfold cinfo
  rw [condMutualInfo_eq (observe_measurable X hX A) (observe_measurable X hX B)
      (observe_measurable X hX C),
    condMutualInfo_eq Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete]
  have hp : condEntropy (fun ω => (observe X A ω, observe X B ω)) (observe X C) μ =
      condEntropy (fun v : Set.range X => (observe (Subtype.val : Set.range X → ι → ℕ) A v, observe (Subtype.val : Set.range X → ι → ℕ) B v))
        (observe (Subtype.val : Set.range X → ι → ℕ) C) (realizeLaw μ X) := by
    apply IdentDistrib.condEntropy_eq
      (X' := fun v : Set.range X => (observe Subtype.val A v, observe Subtype.val B v))
      (Y' := observe (Subtype.val : Set.range X → ι → ℕ) C)
      (μ' := realizeLaw μ X)
      ((observe_measurable X hX A).prodMk (observe_measurable X hX B))
      (observe_measurable X hX C) Measurable.of_discrete Measurable.of_discrete
    exact (identDistrib_realize μ X hX).comp
      (u := fun v => ((restrict A v, restrict B v), restrict C v)) Measurable.of_discrete
  rw [show condEntropy (observe X A) (observe X C) μ = _ from cvalue_realize μ X hX A C,
      show condEntropy (observe X B) (observe X C) μ = _ from cvalue_realize μ X hX B C,
      hp]
  rfl

/-- Conditional independence is preserved by finite joint realization. -/
lemma condIndep_realize (hX : Measurable X) (A B C : Finset ι) :
    CondIndepFun (observe X A) (observe X B) (observe X C) μ ↔
    CondIndepFun (observe (Subtype.val : Set.range X → ι → ℕ) A)
      (observe (Subtype.val : Set.range X → ι → ℕ) B) (observe (Subtype.val : Set.range X → ι → ℕ) C) (realizeLaw μ X) := by
  letI : Fintype (Set.range X) := FiniteRange.fintype X
  letI : FiniteRange (Subtype.val : Set.range X → ι → ℕ) := ⟨Set.finite_range _⟩
  letI := realizeLaw_probability μ X hX
  rw [← condMutualInfo_eq_zero (observe_measurable X hX A) (observe_measurable X hX B),
    ← condMutualInfo_eq_zero
      (X := observe (Subtype.val : Set.range X → ι → ℕ) A)
      (Y := observe (Subtype.val : Set.range X → ι → ℕ) B)
      (Z := observe (Subtype.val : Set.range X → ι → ℕ) C)
      (μ := realizeLaw μ X) Measurable.of_discrete Measurable.of_discrete]
  change cinfo μ X A B C = 0 ↔ cinfo (realizeLaw μ X) Subtype.val A B C = 0
  rw [cinfo_realize μ X hX]

/-- Ordinary independence is also unchanged by joint realization. -/
lemma indep_realize (hX : Measurable X) (A B : Finset ι) :
    IndepFun (observe X A) (observe X B) μ ↔
    IndepFun (observe (Subtype.val : Set.range X → ι → ℕ) A)
      (observe (Subtype.val : Set.range X → ι → ℕ) B) (realizeLaw μ X) := by
  letI : Fintype (Set.range X) := FiniteRange.fintype X
  letI : FiniteRange (Subtype.val : Set.range X → ι → ℕ) := ⟨Set.finite_range _⟩
  letI := realizeLaw_probability μ X hX
  rw [← mutualInfo_eq_zero (observe_measurable X hX A) (observe_measurable X hX B),
    ← mutualInfo_eq_zero Measurable.of_discrete Measurable.of_discrete]
  have hh := ((identDistrib_realize μ X hX).comp
    (u := fun v => (restrict A v, restrict B v)) Measurable.of_discrete).mutualInfo_eq
  exact Iff.of_eq (congrArg (fun r : ℝ => r = 0) hh)

end UploadBroadcast.Shannon
