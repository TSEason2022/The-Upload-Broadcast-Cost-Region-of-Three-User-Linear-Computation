import UploadBroadcast.GeneralOmniscienceEntropy
import UploadBroadcast.FiniteAlphabetEncoding

/-! The paper's omniscience lift with genuine heterogeneous finite alphabets
and an arbitrary underlying probability sample space. -/
namespace UploadBroadcast.FiniteAlphabet
open MeasureTheory ProbabilityTheory
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  {α : ι → Type*} [∀ i, Fintype (α i)]
  [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ∀ i, α i)

/-- Upload lower bound with an omniscience component. All quantities are actual
Shannon quantities for finite-alphabet random variables; the interaction
inequality is proved internally, not added as a hypothesis. -/
theorem omniscience_lift (hX : Measurable X)
    (O S₁ S₂ S₃ R₁ R₂ R₃ M₁ M₂ M₃ : Finset ι) (Γ : ℝ)
    (joint : IndepFun (project O ∘ X) (project (R₁ ∪ R₂ ∪ R₃) ∘ X) μ)
    (pair₁₂ : IndepFun (project R₁ ∘ X) (project R₂ ∘ X) μ)
    (pair₁₃ : IndepFun (project R₁ ∘ X) (project R₃ ∘ X) μ)
    (pair₂₃ : IndepFun (project R₂ ∘ X) (project R₃ ∘ X) μ)
    (side₁ : condEntropy (project S₁ ∘ X) (project O ∘ X) μ = 0) (side₂ : condEntropy (project S₂ ∘ X) (project O ∘ X) μ = 0)
    (side₃ : condEntropy (project S₃ ∘ X) (project O ∘ X) μ = 0)
    (enc₁ : condEntropy (project M₁ ∘ X) (project (S₁ ∪ R₁) ∘ X) μ = 0)
    (enc₂ : condEntropy (project M₂ ∘ X) (project (S₂ ∪ R₂) ∘ X) μ = 0)
    (enc₃ : condEntropy (project M₃ ∘ X) (project (S₃ ∪ R₃) ∘ X) μ = 0)
    (rec₁ : condEntropy (project O ∘ X) (project (R₁ ∪ S₁ ∪ M₂ ∪ M₃) ∘ X) μ = 0)
    (rec₂ : condEntropy (project O ∘ X) (project (R₂ ∪ S₂ ∪ M₁ ∪ M₃) ∘ X) μ = 0)
    (rec₃ : condEntropy (project O ∘ X) (project (R₃ ∪ S₃ ∪ M₁ ∪ M₂) ∘ X) μ = 0)
    (bound₁₂ : Γ + condMutualInfo (project M₂ ∘ X) (project M₃ ∘ X) (project (R₁ ∪ O) ∘ X) μ + condMutualInfo (project M₁ ∘ X) (project M₃ ∘ X) (project (R₂ ∪ O) ∘ X) μ ≤
      condEntropy (project M₁ ∘ X) (project O ∘ X) μ + condEntropy (project M₂ ∘ X) (project O ∘ X) μ + condEntropy (project M₃ ∘ X) (project O ∘ X) μ)
    (bound₁₃ : Γ + condMutualInfo (project M₂ ∘ X) (project M₃ ∘ X) (project (R₁ ∪ O) ∘ X) μ + condMutualInfo (project M₁ ∘ X) (project M₂ ∘ X) (project (R₃ ∪ O) ∘ X) μ ≤
      condEntropy (project M₁ ∘ X) (project O ∘ X) μ + condEntropy (project M₂ ∘ X) (project O ∘ X) μ + condEntropy (project M₃ ∘ X) (project O ∘ X) μ)
    (bound₂₃ : Γ + condMutualInfo (project M₁ ∘ X) (project M₃ ∘ X) (project (R₂ ∪ O) ∘ X) μ + condMutualInfo (project M₁ ∘ X) (project M₂ ∘ X) (project (R₃ ∪ O) ∘ X) μ ≤
      condEntropy (project M₁ ∘ X) (project O ∘ X) μ + condEntropy (project M₂ ∘ X) (project O ∘ X) μ + condEntropy (project M₃ ∘ X) (project O ∘ X) μ) :
    Γ + max (max (condEntropy (project O ∘ X) (project S₁ ∘ X) μ) (max (condEntropy (project O ∘ X) (project S₂ ∘ X) μ) (condEntropy (project O ∘ X) (project S₃ ∘ X) μ)))
      (((condEntropy (project O ∘ X) (project S₁ ∘ X) μ) + (condEntropy (project O ∘ X) (project S₂ ∘ X) μ) + (condEntropy (project O ∘ X) (project S₃ ∘ X) μ)) / 2) ≤
      entropy (project M₁ ∘ X) μ + entropy (project M₂ ∘ X) μ + entropy (project M₃ ∘ X) μ := by
  have ce (A C : Finset ι) :
      condEntropy (Shannon.observe (encodeFamily ∘ X) A)
        (Shannon.observe (encodeFamily ∘ X) C) μ =
      condEntropy (project A ∘ X) (project C ∘ X) μ := conditional_entropy_encoded μ X hX A C
  have ci (A B C : Finset ι) :
      condMutualInfo (Shannon.observe (encodeFamily ∘ X) A)
        (Shannon.observe (encodeFamily ∘ X) B) (Shannon.observe (encodeFamily ∘ X) C) μ =
      condMutualInfo (project A ∘ X) (project B ∘ X) (project C ∘ X) μ :=
    conditional_mutual_information_encoded μ X hX A B C
  have he (A : Finset ι) : entropy (Shannon.observe (encodeFamily ∘ X) A) μ =
      entropy (project A ∘ X) μ := entropy_encoded μ X hX A
  have cz {A C : Finset ι} (hz : condEntropy (project A ∘ X) (project C ∘ X) μ = 0) :
      condEntropy (Shannon.observe (encodeFamily ∘ X) A)
        (Shannon.observe (encodeFamily ∘ X) C) μ = 0 := (ce A C).trans hz
  have result := Shannon.omniscience_lift_general μ (encodeFamily ∘ X)
    (measurable_encodeFamily X hX) O S₁ S₂ S₃ R₁ R₂ R₃ M₁ M₂ M₃ Γ
    ((independence_encoded μ X hX _ _).mpr joint)
    ((independence_encoded μ X hX _ _).mpr pair₁₂)
    ((independence_encoded μ X hX _ _).mpr pair₁₃)
    ((independence_encoded μ X hX _ _).mpr pair₂₃)
    (cz side₁) (cz side₂) (cz side₃)
    (cz enc₁) (cz enc₂) (cz enc₃) (cz rec₁) (cz rec₂) (cz rec₃)
    (by simpa only [ce, ci] using bound₁₂)
    (by simpa only [ce, ci] using bound₁₃)
    (by simpa only [ce, ci] using bound₂₃)
  simpa only [ce, he] using result

end UploadBroadcast.FiniteAlphabet
