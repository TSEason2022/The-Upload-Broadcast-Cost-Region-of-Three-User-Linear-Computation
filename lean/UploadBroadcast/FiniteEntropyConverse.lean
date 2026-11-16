import UploadBroadcast.Shannon
import UploadBroadcast.CommonFunction

/-! Concrete finite-alphabet Shannon version of the common-function converse.
All entropy and independence expressions below are actual PFR probability
expressions. There are no postulated entropy laws in this theorem's hypotheses. -/
namespace UploadBroadcast.Shannon
open MeasureTheory ProbabilityTheory

variable {Ω ι : Type*} [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  [Fintype ι] [DecidableEq ι]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ι → ℕ)

/-- Conditional Shannon entropy of the indicated observation collections. -/
noncomputable def cvalue (A C : Finset ι) : ℝ :=
  condEntropy (observe X A) (observe X C) μ

/-- Conditional Shannon mutual information of observation collections. -/
noncomputable def cinfo (A B C : Finset ι) : ℝ :=
  condMutualInfo (observe X A) (observe X B) (observe X C) μ

/-- The paper's common-function entropy bound on a concrete finite probability
space. A collection of finite-alphabet variables is represented by finitely many
natural-number-valued coordinate observations. `Yᵢ,Tᵢ,Mᵢ,Θ,O` are collections of
these coordinates; no disjointness is assumed or needed.

The hypotheses are exactly conditional pairwise independence, deterministic
local encoding, zero-error local recovery, tripod recovery, and the specified
common-function recovery conditions. Two of the paper's three tripod recovery
conditions suffice for this particular ordering. -/
theorem commonFunction_finite
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
  let h := (entropyFunction μ X).condition O
  have encoding {Y T M : Finset ι} (he : cvalue μ X M ((Y ∪ T) ∪ O) = 0) :
      h.Determines (Y ∪ T) (M ∪ T) := by
    have hm : h.Determines (Y ∪ T) M := (condition_determines_iff μ X O (Y ∪ T) M).mpr he
    exact h.determines_union hm (h.determines_of_subset Finset.subset_union_right)
  have decoding {Y T M : Finset ι} (hd : cvalue μ X Y ((M ∪ T) ∪ O) = 0) :
      h.Determines (M ∪ T) (Y ∪ T) := by
    have hy : h.Determines (M ∪ T) Y := (condition_determines_iff μ X O (M ∪ T) Y).mpr hd
    exact h.determines_union hy (h.determines_of_subset Finset.subset_union_right)
  have result := h.commonFunction (Y₁ ∪ T₁) (Y₂ ∪ T₂) (Y₃ ∪ T₃)
    M₁ M₂ M₃ T₁ T₂ T₃ Θ
    (encoding enc₁) (encoding enc₂) (encoding enc₃)
    (decoding dec₁) (decoding dec₂) (decoding dec₃)
    ((condition_independent_iff μ X O _ _).mpr ind₁₂)
    ((condition_independent_iff μ X O _ _).mpr ind₁₃)
    ((condition_independent_iff μ X O _ _).mpr ind₂₃)
    ((condition_determines_iff μ X O _ _).mpr tri₃)
    ((condition_determines_iff μ X O _ _).mpr tri₂)
    ((condition_determines_iff μ X O _ _).mpr common₁)
    ((condition_determines_iff μ X O _ _).mpr common₂)
    ((condition_determines_iff μ X O _ _).mpr bridge)
  dsimp only [h] at result
  simp only [condition_eq_condEntropy, condition_condMutual_eq] at result
  exact result

end UploadBroadcast.Shannon
