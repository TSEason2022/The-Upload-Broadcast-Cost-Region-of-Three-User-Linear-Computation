import UploadBroadcast.FiniteAlphabetEncoding

/-! Source-level common-function theorem for arbitrary heterogeneous finite
alphabets on an arbitrary probability space. -/
namespace UploadBroadcast.FiniteAlphabet
open MeasureTheory ProbabilityTheory
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  {α : ι → Type*} [∀ i, Fintype (α i)]
  [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ∀ i, α i)

noncomputable def conditionalEntropy (A C : Finset ι) : ℝ :=
  condEntropy (project A ∘ X) (project C ∘ X) μ

noncomputable def conditionalMutualInformation (A B C : Finset ι) : ℝ :=
  condMutualInfo (project A ∘ X) (project B ∘ X) (project C ∘ X) μ

/-- Common-function entropy bound for genuine finite-alphabet random variables.
The named variables can be represented by singleton coordinate sets; using
collections of coordinates merely permits tuples without repeated pair syntax.
The entropy is in nats, and the inequality is homogeneous, so it also holds in
any other logarithmic units after a positive rescaling. -/
theorem commonFunction (hX : Measurable X)
    (Y₁ Y₂ Y₃ T₁ T₂ T₃ M₁ M₂ M₃ Θ O : Finset ι)
    (ind₁₂ : CondIndepFun (project (Y₁ ∪ T₁) ∘ X) (project (Y₂ ∪ T₂) ∘ X) (project O ∘ X) μ)
    (ind₁₃ : CondIndepFun (project (Y₁ ∪ T₁) ∘ X) (project (Y₃ ∪ T₃) ∘ X) (project O ∘ X) μ)
    (ind₂₃ : CondIndepFun (project (Y₂ ∪ T₂) ∘ X) (project (Y₃ ∪ T₃) ∘ X) (project O ∘ X) μ)
    (enc₁ : conditionalEntropy μ X M₁ ((Y₁ ∪ T₁) ∪ O) = 0)
    (enc₂ : conditionalEntropy μ X M₂ ((Y₂ ∪ T₂) ∪ O) = 0)
    (enc₃ : conditionalEntropy μ X M₃ ((Y₃ ∪ T₃) ∪ O) = 0)
    (dec₁ : conditionalEntropy μ X Y₁ ((M₁ ∪ T₁) ∪ O) = 0)
    (dec₂ : conditionalEntropy μ X Y₂ ((M₂ ∪ T₂) ∪ O) = 0)
    (dec₃ : conditionalEntropy μ X Y₃ ((M₃ ∪ T₃) ∪ O) = 0)
    (tri₃ : conditionalEntropy μ X T₃ ((T₁ ∪ T₂) ∪ O) = 0)
    (tri₂ : conditionalEntropy μ X T₂ ((T₁ ∪ T₃) ∪ O) = 0)
    (common₁ : conditionalEntropy μ X Θ (((M₁ ∪ M₂ ∪ M₃) ∪ T₁) ∪ O) = 0)
    (common₂ : conditionalEntropy μ X Θ (((M₁ ∪ M₂ ∪ M₃) ∪ T₂) ∪ O) = 0)
    (bridge : conditionalEntropy μ X T₁ ((((M₁ ∪ M₂ ∪ M₃) ∪ Θ) ∪ T₃) ∪ O) = 0) :
    2 * conditionalEntropy μ X ((Y₁ ∪ T₁) ∪ (Y₂ ∪ T₂) ∪ (Y₃ ∪ T₃)) O -
      (conditionalEntropy μ X (Y₁ ∪ T₁) O + conditionalEntropy μ X (Y₂ ∪ T₂) O + conditionalEntropy μ X (Y₃ ∪ T₃) O) +
      conditionalMutualInformation μ X M₂ M₃ ((M₁ ∪ T₁) ∪ O) + conditionalMutualInformation μ X M₁ M₃ ((M₂ ∪ T₂) ∪ O) ≤
      conditionalEntropy μ X M₁ O + conditionalEntropy μ X M₂ O + conditionalEntropy μ X M₃ O := by
  have cv {A C : Finset ι} (hz : conditionalEntropy μ X A C = 0) :
      Shannon.cvalue μ (encodeFamily ∘ X) A C = 0 := by
    rw [conditional_entropy_encoded μ X hX]
    exact hz
  have result := Shannon.commonFunction_general μ (encodeFamily ∘ X)
    (measurable_encodeFamily X hX)
    Y₁ Y₂ Y₃ T₁ T₂ T₃ M₁ M₂ M₃ Θ O
    ((conditional_independence_encoded μ X hX _ _ _).mpr ind₁₂)
    ((conditional_independence_encoded μ X hX _ _ _).mpr ind₁₃)
    ((conditional_independence_encoded μ X hX _ _ _).mpr ind₂₃)
    (cv enc₁) (cv enc₂) (cv enc₃) (cv dec₁) (cv dec₂) (cv dec₃)
    (cv tri₃) (cv tri₂) (cv common₁) (cv common₂) (cv bridge)
  simpa only [conditional_entropy_encoded μ X hX,
    conditional_mutual_information_encoded μ X hX] using result

end UploadBroadcast.FiniteAlphabet
