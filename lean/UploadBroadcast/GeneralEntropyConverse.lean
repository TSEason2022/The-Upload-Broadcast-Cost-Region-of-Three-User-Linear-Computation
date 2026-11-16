import UploadBroadcast.JointRealization

/-! Common-function entropy converse on an arbitrary probability sample space,
proved by passage to the finite joint observation distribution. -/
namespace UploadBroadcast.Shannon
open MeasureTheory ProbabilityTheory
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ι → ℕ) [FiniteRange X]

/-- The source-faithful common-function inequality for finite-alphabet
observations on an arbitrary probability space. The joint observation `X` has
finite range; the underlying sample space need not be finite. -/
theorem commonFunction_general (hX : Measurable X)
    (Y₁ Y₂ Y₃ T₁ T₂ T₃ M₁ M₂ M₃ Θ O : Finset ι)
    (ind₁₂ : CondIndepFun (observe X (Y₁ ∪ T₁)) (observe X (Y₂ ∪ T₂)) (observe X O) μ)
    (ind₁₃ : CondIndepFun (observe X (Y₁ ∪ T₁)) (observe X (Y₃ ∪ T₃)) (observe X O) μ)
    (ind₂₃ : CondIndepFun (observe X (Y₂ ∪ T₂)) (observe X (Y₃ ∪ T₃)) (observe X O) μ)
    (enc₁ : cvalue μ X M₁ ((Y₁ ∪ T₁) ∪ O) = 0)
    (enc₂ : cvalue μ X M₂ ((Y₂ ∪ T₂) ∪ O) = 0)
    (enc₃ : cvalue μ X M₃ ((Y₃ ∪ T₃) ∪ O) = 0)
    (dec₁ : cvalue μ X Y₁ ((M₁ ∪ T₁) ∪ O) = 0)
    (dec₂ : cvalue μ X Y₂ ((M₂ ∪ T₂) ∪ O) = 0)
    (dec₃ : cvalue μ X Y₃ ((M₃ ∪ T₃) ∪ O) = 0)
    (tri₃ : cvalue μ X T₃ ((T₁ ∪ T₂) ∪ O) = 0)
    (tri₂ : cvalue μ X T₂ ((T₁ ∪ T₃) ∪ O) = 0)
    (common₁ : cvalue μ X Θ (((M₁ ∪ M₂ ∪ M₃) ∪ T₁) ∪ O) = 0)
    (common₂ : cvalue μ X Θ (((M₁ ∪ M₂ ∪ M₃) ∪ T₂) ∪ O) = 0)
    (bridge : cvalue μ X T₁ ((((M₁ ∪ M₂ ∪ M₃) ∪ Θ) ∪ T₃) ∪ O) = 0) :
    2 * cvalue μ X ((Y₁ ∪ T₁) ∪ (Y₂ ∪ T₂) ∪ (Y₃ ∪ T₃)) O -
      (cvalue μ X (Y₁ ∪ T₁) O + cvalue μ X (Y₂ ∪ T₂) O + cvalue μ X (Y₃ ∪ T₃) O) +
      cinfo μ X M₂ M₃ ((M₁ ∪ T₁) ∪ O) + cinfo μ X M₁ M₃ ((M₂ ∪ T₂) ∪ O) ≤
      cvalue μ X M₁ O + cvalue μ X M₂ O + cvalue μ X M₃ O := by
  letI : Fintype (Set.range X) := FiniteRange.fintype X
  letI : FiniteRange (Subtype.val : Set.range X → ι → ℕ) := ⟨Set.finite_range _⟩
  letI := realizeLaw_probability μ X hX
  have cv {A C : Finset ι} (hz : cvalue μ X A C = 0) :
      cvalue (realizeLaw μ X) (Subtype.val : Set.range X → ι → ℕ) A C = 0 := by
    rw [← cvalue_realize μ X hX]
    exact hz
  have result := commonFunction_finite (realizeLaw μ X)
    (Subtype.val : Set.range X → ι → ℕ)
    Y₁ Y₂ Y₃ T₁ T₂ T₃ M₁ M₂ M₃ Θ O
    ((condIndep_realize μ X hX _ _ _).mp ind₁₂)
    ((condIndep_realize μ X hX _ _ _).mp ind₁₃)
    ((condIndep_realize μ X hX _ _ _).mp ind₂₃)
    (cv enc₁) (cv enc₂) (cv enc₃) (cv dec₁) (cv dec₂) (cv dec₃)
    (cv tri₃) (cv tri₂) (cv common₁) (cv common₂) (cv bridge)
  simpa only [← cvalue_realize μ X hX, ← cinfo_realize μ X hX] using result

end UploadBroadcast.Shannon
