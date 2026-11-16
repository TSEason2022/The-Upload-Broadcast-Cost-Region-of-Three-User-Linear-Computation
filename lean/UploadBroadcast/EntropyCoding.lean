import PFR.ForMathlib.Entropy.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Basic verified bridges between deterministic finite-alphabet codes and
entropy constraints, and between entropy and attainable-alphabet costs. -/
namespace UploadBroadcast
open MeasureTheory ProbabilityTheory

variable {Ω S T : Type*} [MeasurableSpace Ω]
  [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace T] [Countable T] [MeasurableSingletonClass T]

/-- Deterministic encoding or decoding implies conditional entropy zero. -/
theorem deterministic_condEntropy_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (hX : Measurable X) [FiniteRange X] (f : S → T) :
    condEntropy (f ∘ X) X μ = 0 := by
  have hfX : Measurable (f ∘ X) := Measurable.of_discrete.comp hX
  have hc := chain_rule' μ hX hfX
  rw [entropy_prod_comp hX μ f] at hc
  linarith

/-- An explicitly supplied deterministic reconstruction gives zero conditional
entropy. This turns the paper's encoder equations into entropy hypotheses. -/
theorem condEntropy_zero_of_factor (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (hX : Measurable X) [FiniteRange X]
    (f : S → T) (hY : Y = f ∘ X) : condEntropy Y X μ = 0 := by
  rw [hY]
  exact deterministic_condEntropy_zero μ X hX f

/-- The entropy of an upload is bounded by the logarithm of its attainable
alphabet, not merely by its declared (possibly unused) output alphabet. -/
theorem entropy_le_log_attainable (μ : Measure Ω)
    (X : Ω → S) (hX : Measurable X) [FiniteRange X] :
    entropy X μ ≤ Real.log (Nat.card (Set.range X)) := by
  apply entropy_le_log_card_of_mem_finite (FiniteRange.finite (X := X)) hX
  exact Filter.Eventually.of_forall (fun ω => ⟨ω, rfl⟩)

/-- Conversion of the attainable-alphabet entropy bound to logarithmic units
with base `q > 1`. -/
theorem entropy_div_log_le_logb_attainable (μ : Measure Ω)
    (X : Ω → S) (hX : Measurable X) [FiniteRange X] (q : ℝ) (hq : 1 < q) :
    entropy X μ / Real.log q ≤ Real.logb q (Nat.card (Set.range X)) := by
  rw [Real.logb]
  exact div_le_div_of_nonneg_right (entropy_le_log_attainable μ X hX)
    (le_of_lt (Real.log_pos hq))

end UploadBroadcast
