import UploadBroadcast.RegularPositiveCross
import UploadBroadcast.GeneralTransverseClassification

/-!
# Complete positive-excess zero-defect classification

The source hypotheses are actual nested flags, indecomposability, side spanning,
zero defect, and positive side excess. Cross-transversality, the dimension family,
Tits value one, and excess one are conclusions, not assumptions. The regular-simple
separation argument supplies transversality; the marked nilpotent argument then
constructs the canonical configuration isomorphism over the original finite field.
-/
namespace UploadBroadcast.RegularResonantClassification
open TaskDecomposition GeneralTransverseClassification
variable {K F : Type} [Field K] [Finite K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The dimension vector is derived from the original flags. -/
theorem dimensions (T : TaskDecomposition.Task K F)
    (hi : Indecomposable T.spaces ⊤)
    (hzero : ReflectionReduction.defect T.dimensionVector = 0)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hpos : Module.finrank K F < Module.finrank K (T.A 0) +
      Module.finrank K (T.A 1) + Module.finrank K (T.A 2)) :
    ∃ n : ℕ, T.dimensionVector =
      ⟨3*(n:ℤ)+2,2*(n:ℤ)+1,2*(n:ℤ)+1,2*(n:ℤ)+1,
        (n:ℤ)+1,(n:ℤ)+1,(n:ℤ)+1⟩ :=
  task_transverse_indec_dimensions T hi hzero hspan hpos
    (RegularPositiveCross.cross_disjoint T hi hzero hpos)

/-- Both numerical invariants are consequences of genuine indecomposability. -/
theorem tits_and_excess (T : TaskDecomposition.Task K F)
    (hi : Indecomposable T.spaces ⊤)
    (hzero : ReflectionReduction.defect T.dimensionVector = 0)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hpos : Module.finrank K F < Module.finrank K (T.A 0) +
      Module.finrank K (T.A 1) + Module.finrank K (T.A 2)) :
    ReflectionReduction.tits T.dimensionVector = 1 ∧
      Structural.excess T.dimensionVector.f T.dimensionVector.a₁
        T.dimensionVector.a₂ T.dimensionVector.a₃ = 1 :=
  task_transverse_tits_and_excess T hi hzero hspan hpos
    (RegularPositiveCross.cross_disjoint T hi hzero hpos)

/-- Complete classification, including the passive tripod endpoint. -/
theorem classification (T : TaskDecomposition.Task K F)
    (hi : Indecomposable T.spaces ⊤)
    (hzero : ReflectionReduction.defect T.dimensionVector = 0)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hpos : Module.finrank K F < Module.finrank K (T.A 0) +
      Module.finrank K (T.A 1) + Module.finrank K (T.A 2)) :
    ((∀ i, T.A i = T.U i) ∧
      ConfigurationIso T.spaces (graphTask K (Fin 0 → K) 0 0).spaces) ∨
    ∃ n : ℕ, ConfigurationIso T.spaces
      (graphTask K (JordanResonance.V K n)
        (JordanResonance.shift K n) (JordanResonance.head K n)).spaces :=
  classify_transverse_task T hi hzero hspan hpos
    (RegularPositiveCross.cross_disjoint T hi hzero hpos)

/-- An active regular indecomposable is actually isomorphic to a resonant block. -/
theorem active_classification (T : TaskDecomposition.Task K F)
    (hi : Indecomposable T.spaces ⊤)
    (hzero : ReflectionReduction.defect T.dimensionVector = 0)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hpos : Module.finrank K F < Module.finrank K (T.A 0) +
      Module.finrank K (T.A 1) + Module.finrank K (T.A 2))
    (hactive : ∃ i, T.A i ≠ T.U i) :
    ∃ n : ℕ, ConfigurationIso T.spaces
      (graphTask K (JordanResonance.V K n)
        (JordanResonance.shift K n) (JordanResonance.head K n)).spaces :=
  classify_active_task T hi hzero hspan hpos
    (RegularPositiveCross.cross_disjoint T hi hzero hpos) hactive

end UploadBroadcast.RegularResonantClassification
