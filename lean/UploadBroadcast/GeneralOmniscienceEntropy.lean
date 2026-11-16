import UploadBroadcast.OmniscienceEntropy
import UploadBroadcast.JointRealization

/-! The omniscience entropy lift on an arbitrary probability sample space. -/
namespace UploadBroadcast.Shannon
open MeasureTheory ProbabilityTheory
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ι → ℕ) [FiniteRange X]

/-- The omniscience lift on an arbitrary sample space. Only the joint
observation has finite range, as guaranteed by the finite-alphabet hypothesis. -/
theorem omniscience_lift_general (hX : Measurable X)
    (O S₁ S₂ S₃ R₁ R₂ R₃ M₁ M₂ M₃ : Finset ι) (Γ : ℝ)
    (joint : IndepFun (observe X O) (observe X (R₁ ∪ R₂ ∪ R₃)) μ)
    (pair₁₂ : IndepFun (observe X R₁) (observe X R₂) μ)
    (pair₁₃ : IndepFun (observe X R₁) (observe X R₃) μ)
    (pair₂₃ : IndepFun (observe X R₂) (observe X R₃) μ)
    (side₁ : condEntropy (observe X S₁) (observe X O) μ = 0) (side₂ : condEntropy (observe X S₂) (observe X O) μ = 0)
    (side₃ : condEntropy (observe X S₃) (observe X O) μ = 0)
    (enc₁ : condEntropy (observe X M₁) (observe X (S₁ ∪ R₁)) μ = 0)
    (enc₂ : condEntropy (observe X M₂) (observe X (S₂ ∪ R₂)) μ = 0)
    (enc₃ : condEntropy (observe X M₃) (observe X (S₃ ∪ R₃)) μ = 0)
    (rec₁ : condEntropy (observe X O) (observe X (R₁ ∪ S₁ ∪ M₂ ∪ M₃)) μ = 0)
    (rec₂ : condEntropy (observe X O) (observe X (R₂ ∪ S₂ ∪ M₁ ∪ M₃)) μ = 0)
    (rec₃ : condEntropy (observe X O) (observe X (R₃ ∪ S₃ ∪ M₁ ∪ M₂)) μ = 0)
    (bound₁₂ : Γ + condMutualInfo (observe X M₂) (observe X M₃) (observe X (R₁ ∪ O)) μ + condMutualInfo (observe X M₁) (observe X M₃) (observe X (R₂ ∪ O)) μ ≤
      condEntropy (observe X M₁) (observe X O) μ + condEntropy (observe X M₂) (observe X O) μ + condEntropy (observe X M₃) (observe X O) μ)
    (bound₁₃ : Γ + condMutualInfo (observe X M₂) (observe X M₃) (observe X (R₁ ∪ O)) μ + condMutualInfo (observe X M₁) (observe X M₂) (observe X (R₃ ∪ O)) μ ≤
      condEntropy (observe X M₁) (observe X O) μ + condEntropy (observe X M₂) (observe X O) μ + condEntropy (observe X M₃) (observe X O) μ)
    (bound₂₃ : Γ + condMutualInfo (observe X M₁) (observe X M₃) (observe X (R₂ ∪ O)) μ + condMutualInfo (observe X M₁) (observe X M₂) (observe X (R₃ ∪ O)) μ ≤
      condEntropy (observe X M₁) (observe X O) μ + condEntropy (observe X M₂) (observe X O) μ + condEntropy (observe X M₃) (observe X O) μ) :
    Γ + max (max (condEntropy (observe X O) (observe X S₁) μ) (max (condEntropy (observe X O) (observe X S₂) μ) (condEntropy (observe X O) (observe X S₃) μ)))
      (((condEntropy (observe X O) (observe X S₁) μ) + (condEntropy (observe X O) (observe X S₂) μ) + (condEntropy (observe X O) (observe X S₃) μ)) / 2) ≤
      entropy (observe X M₁) μ + entropy (observe X M₂) μ + entropy (observe X M₃) μ := by
  letI : Fintype (Set.range X) := FiniteRange.fintype X
  letI : FiniteRange (Subtype.val : Set.range X → ι → ℕ) := ⟨Set.finite_range _⟩
  letI := realizeLaw_probability μ X hX
  have ce (A C : Finset ι) : condEntropy (observe X A) (observe X C) μ =
      condEntropy (observe (Subtype.val : Set.range X → ι → ℕ) A)
        (observe Subtype.val C) (realizeLaw μ X) := cvalue_realize μ X hX A C
  have ci (A B C : Finset ι) : condMutualInfo (observe X A) (observe X B) (observe X C) μ =
      condMutualInfo (observe (Subtype.val : Set.range X → ι → ℕ) A)
        (observe Subtype.val B) (observe Subtype.val C) (realizeLaw μ X) := cinfo_realize μ X hX A B C
  have he (A : Finset ι) : entropy (observe X A) μ =
      entropy (observe (Subtype.val : Set.range X → ι → ℕ) A) (realizeLaw μ X) := value_realize μ X hX A
  have cz {A C : Finset ι} (hz : condEntropy (observe X A) (observe X C) μ = 0) :
      condEntropy (observe (Subtype.val : Set.range X → ι → ℕ) A)
        (observe Subtype.val C) (realizeLaw μ X) = 0 := (ce A C).symm.trans hz
  have result := omniscience_lift (realizeLaw μ X) (Subtype.val : Set.range X → ι → ℕ)
    O S₁ S₂ S₃ R₁ R₂ R₃ M₁ M₂ M₃ Γ
    ((indep_realize μ X hX _ _).mp joint)
    ((indep_realize μ X hX _ _).mp pair₁₂)
    ((indep_realize μ X hX _ _).mp pair₁₃)
    ((indep_realize μ X hX _ _).mp pair₂₃)
    (cz side₁) (cz side₂) (cz side₃)
    (cz enc₁) (cz enc₂) (cz enc₃) (cz rec₁) (cz rec₂) (cz rec₃)
    (by simpa only [← ce, ← ci] using bound₁₂)
    (by simpa only [← ce, ← ci] using bound₁₃)
    (by simpa only [← ce, ← ci] using bound₂₃)
  simpa only [← ce, ← he] using result

end UploadBroadcast.Shannon
