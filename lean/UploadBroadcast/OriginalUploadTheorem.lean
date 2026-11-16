import UploadBroadcast.OriginalUploadModel
import UploadBroadcast.OriginalUploadFormula

namespace UploadBroadcast.Task
open ResidualTaskAssembly Module
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Source thm:upload, for every original feasible finite-dimensional task.
The infimum ranges over arbitrary nonlinear fixed-length zero-error codes and
its closure; all reduction maps and the matching linear codes are constructed. -/
theorem minimum_upload (T : Task K F) : T.uploadOptimum = T.minimumUploadFormula := by
  have h := T.pairFreeChart.uploadOptimum_from T.residualPairSelection
    T.normalized.pairReduction_pairKnown_le T T.pairCanonicalRetraction
  simpa only [minimumUploadFormula,T.preResidual_pairKnown_finrank 0,
    T.preResidual_pairKnown_finrank 1,T.preResidual_pairKnown_finrank 2] using h

/-- A genuine original-field length-two code attains the original task's
minimum. Its nominal upload symbol count is exactly twice that minimum. -/
theorem minimum_upload_two_instance (T : Task K F) :
    ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode 2 r b),
      ((∑ i,r i : ℕ) : ℝ) / 2 = T.minimumUploadFormula ∧
      c.toCode.uploadCost = T.minimumUploadFormula := by
  have h := T.pairFreeChart.two_instance_from T.residualPairSelection
    T.normalized.pairReduction_pairKnown_le T T.pairCanonicalRetraction
  simpa only [minimumUploadFormula,T.preResidual_pairKnown_finrank 0,
    T.preResidual_pairKnown_finrank 1,T.preResidual_pairKnown_finrank 2] using h

/-- When Ω is integral, scalar linear uploads attain the minimum over the
original field, with exactly the source minimum in nominal upload symbols. -/
theorem minimum_upload_scalar (T : Task K F) (n : ℕ) (hn : (n : ℝ) = T.uploadOmniscienceValue) :
    ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode 1 r b),
      ((∑ i,r i : ℕ) : ℝ) = T.minimumUploadFormula ∧
      c.toCode.uploadCost = T.minimumUploadFormula := by
  have hn' : (n : ℝ) = T.pairFreeChart.omegaValue
      (finrank K (T.preResidual.pairKnown 0)) (finrank K (T.preResidual.pairKnown 1))
      (finrank K (T.preResidual.pairKnown 2)) := by
    simpa only [uploadOmniscienceValue,T.preResidual_pairKnown_finrank 0,
      T.preResidual_pairKnown_finrank 1,T.preResidual_pairKnown_finrank 2] using hn
  have h := T.pairFreeChart.scalar_from T.residualPairSelection
    T.normalized.pairReduction_pairKnown_le T T.pairCanonicalRetraction n hn'
  simpa only [minimumUploadFormula,T.preResidual_pairKnown_finrank 0,
    T.preResidual_pairKnown_finrank 1,T.preResidual_pairKnown_finrank 2] using h

omit [Finite K] in
/-- The Ω expression is max of the three original deficits and half their sum. -/
theorem uploadOmniscienceValue_eq (T : Task K F) :
    let d₀ := (T.pairFreeChart.commonDimension : ℝ) + T.intrinsicActivePairRank 0
    let d₁ := (T.pairFreeChart.commonDimension : ℝ) + T.intrinsicActivePairRank 1
    let d₂ := (T.pairFreeChart.commonDimension : ℝ) + T.intrinsicActivePairRank 2
    T.uploadOmniscienceValue = max (max d₀ (max d₁ d₂)) ((d₀+d₁+d₂)/2) := by
  simp only [uploadOmniscienceValue,PrivateTripodChart.omegaValue,Allocation.omniscienceValue,max_assoc]

/-- Expanded manuscript formula: retained private rank plus noncommon tripod
rank plus the maximum omniscience deficit/half-sum expression. -/
theorem minimum_upload_source_formula (T : Task K F) :
    let d₀ := (T.pairFreeChart.commonDimension : ℝ) + T.intrinsicActivePairRank 0
    let d₁ := (T.pairFreeChart.commonDimension : ℝ) + T.intrinsicActivePairRank 1
    let d₂ := (T.pairFreeChart.commonDimension : ℝ) + T.intrinsicActivePairRank 2
    T.uploadOptimum = (T.pairFreeChart.privateDimension : ℝ) + T.pairFreeChart.tripodDimension +
      max (max d₀ (max d₁ d₂)) ((d₀+d₁+d₂)/2) := by
  rw [T.minimum_upload]
  simp only [minimumUploadFormula,PrivateTripodChart.uploadFormula,
    PrivateTripodChart.omegaValue,Allocation.omniscienceValue,max_assoc]

/-- No boundary point introduced by regularization and closure can improve
the source minimum-upload expression. -/
theorem minimum_upload_closed_lower (T : Task K F) {b : ℝ × ℝ} (hb : b ∈ T.costRegion) :
    T.minimumUploadFormula ≤ b.1 := by
  rw [← T.minimum_upload]
  exact csInf_le (T.upload_budget_bddBelow)
    ⟨b.2,(costRegion_nonneg hb).2,hb⟩

/-- The source one-or-two-instance claim with no integrality witness supplied:
use one instance exactly in the integral-Ω branch and two otherwise. -/
theorem minimum_upload_attainment (T : Task K F) :
    ∃ (L : ℕ) (r : Three → ℕ) (b : ℕ) (c : T.LinearCode L r b),
      (L = 1 ∨ L = 2) ∧
      ((∃ n : ℕ, (n : ℝ) = T.uploadOmniscienceValue) ↔ L = 1) ∧
      ((∑ i,r i : ℕ) : ℝ) / L = T.minimumUploadFormula ∧
      c.toCode.uploadCost = T.minimumUploadFormula := by
  classical
  by_cases hi : ∃ n : ℕ, (n : ℝ) = T.uploadOmniscienceValue
  · obtain ⟨n,hn⟩ := hi
    obtain ⟨r,b,c,hN,hc⟩ := T.minimum_upload_scalar n hn
    refine ⟨1,r,b,c,Or.inl rfl,?_,?_,hc⟩
    · exact ⟨fun _ => rfl,fun _ => ⟨n,hn⟩⟩
    · simpa only [Nat.cast_one,div_one] using hN
  · obtain ⟨r,b,c,hN,hc⟩ := T.minimum_upload_two_instance
    refine ⟨2,r,b,c,Or.inr rfl,?_,hN,hc⟩
    simp only [hi,false_iff]
    decide

omit [Finite K] in
/-- Ω is nonnegative, so integer integrality and natural-number integrality agree. -/
theorem uploadOmniscienceValue_nonneg (T : Task K F) : 0 ≤ T.uploadOmniscienceValue := by
  rw [T.uploadOmniscienceValue_eq]
  positivity

omit [Finite K] in
theorem uploadOmniscienceValue_integral_iff_nat (T : Task K F) :
    (∃ z : ℤ, (z : ℝ) = T.uploadOmniscienceValue) ↔
      ∃ n : ℕ, (n : ℝ) = T.uploadOmniscienceValue := by
  constructor
  · rintro ⟨z,hz⟩
    have hz₀ : (0 : ℝ) ≤ z := by rw [hz]; exact T.uploadOmniscienceValue_nonneg
    have hz₀' : (0 : ℤ) ≤ z := by exact_mod_cast hz₀
    refine ⟨z.toNat,?_⟩
    have he : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hz₀'
    exact he.trans hz
  · rintro ⟨n,hn⟩
    exact ⟨(n : ℤ),by exact_mod_cast hn⟩

/-- Scalar attainment under integrality in the usual integer sense. -/
theorem minimum_upload_scalar_of_integral (T : Task K F)
    (h : ∃ z : ℤ, (z : ℝ) = T.uploadOmniscienceValue) :
    ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode 1 r b),
      ((∑ i,r i : ℕ) : ℝ) = T.minimumUploadFormula ∧
      c.toCode.uploadCost = T.minimumUploadFormula := by
  obtain ⟨n,hn⟩ := T.uploadOmniscienceValue_integral_iff_nat.mp h
  exact T.minimum_upload_scalar n hn

end UploadBroadcast.Task
