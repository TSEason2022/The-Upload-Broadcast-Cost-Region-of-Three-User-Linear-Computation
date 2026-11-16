import UploadBroadcast.DoubleOperationalScaling
import UploadBroadcast.BroadcastRegion

/-! Unconditional arithmetic and converse consequences for the operational
optima. Joint achievability is deliberately not asserted in this module. -/
namespace UploadBroadcast.Task
open Module
variable {K F : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- The original-task upload optimum is a half-integer, witnessed by the
integer nominal symbol count of its actual two-instance optimal upload code. -/
theorem uploadOptimum_halfInteger (T : Task K F) : Profile.HalfInteger T.uploadOptimum := by
  obtain ⟨r,b,c,hn,_⟩ := T.minimum_upload_two_instance
  refine ⟨(∑ i,r i : ℕ),?_⟩
  rw [T.minimum_upload]
  exact hn.symm

/-- Half-integrality here concerns the optimum over arbitrary nonlinear
codes, using the established operational identification of the profile. -/
theorem broadcastOptimum_halfInteger (T : Task K F) :
    Profile.HalfInteger (broadcastOptimum T.A T.U) := by
  rw [task_general_broadcastOptimum_eq_rankBound]
  exact Profile.rankBound_halfInteger T

/-- Two identical tasks double the operational fully informed optimum. -/
theorem broadcastOptimum_double (T : Task K F) :
    broadcastOptimum (Profile.directSum T T).A (Profile.directSum T T).U =
      2*broadcastOptimum T.A T.U := by
  simp only [task_general_broadcastOptimum_eq_rankBound,Profile.rankBound_double]

/-- Both operational minima of the doubled task are integers. -/
theorem doubled_optima_integral (T : Task K F) :
    (∃ z : ℤ, (Profile.directSum T T).uploadOptimum = z) ∧
    (∃ z : ℤ, broadcastOptimum (Profile.directSum T T).A (Profile.directSum T T).U = z) := by
  obtain ⟨u,hu⟩ := T.uploadOptimum_halfInteger
  obtain ⟨d,hd⟩ := T.broadcastOptimum_halfInteger
  constructor
  · refine ⟨u,?_⟩
    rw [T.uploadOptimum_double,hu]
    ring
  · refine ⟨d,?_⟩
    rw [T.broadcastOptimum_double,hd]
    ring

/-- The retained private/tripod ranks are integers, so U* is integral
exactly when the source omniscience term Ω is integral. -/
theorem uploadOptimum_integral_iff_omega_integral (T : Task K F) :
    (∃ z : ℤ, T.uploadOptimum = z) ↔
      ∃ z : ℤ, T.uploadOmniscienceValue = z := by
  have he : T.uploadOptimum = (T.pairFreeChart.privateDimension : ℝ) +
      T.pairFreeChart.tripodDimension + T.uploadOmniscienceValue := by
    rw [T.minimum_upload]
    rfl
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z-T.pairFreeChart.privateDimension-T.pairFreeChart.tripodDimension,?_⟩
    push_cast
    linarith
  · rintro ⟨z,hz⟩
    refine ⟨T.pairFreeChart.privateDimension+T.pairFreeChart.tripodDimension+z,?_⟩
    push_cast
    linarith

/-- The original-field minimum-upload scalar endpoint can be stated directly
in terms of integrality of U*, without providing the Ω witness separately. -/
theorem minimum_upload_scalar_of_optimum_integral (T : Task K F)
    (h : ∃ z : ℤ, T.uploadOptimum = z) :
    ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode 1 r b),
      c.toCode.uploadCost = T.uploadOptimum := by
  obtain ⟨z,hz⟩ := T.uploadOptimum_integral_iff_omega_integral.mp h
  obtain ⟨r,b,c,_,hc⟩ := T.minimum_upload_scalar_of_integral ⟨z,hz.symm⟩
  exact ⟨r,b,c,hc.trans T.minimum_upload.symm⟩

/-- Both independently proved converse bounds throughout the actual closed
region; this is the unconditional outer half of the manuscript main theorem. -/
theorem costRegion_subset_optimal_rectangle (T : Task K F) :
    T.costRegion ⊆ budgetRectangle T.uploadOptimum (broadcastOptimum T.A T.U) := by
  intro b hb
  refine ⟨?_,broadcastOptimum_le_of_costRegion hb⟩
  rw [T.minimum_upload]
  exact T.minimum_upload_closed_lower hb

/-- Every genuine scalar corner code forces both operational minima to be
integers. Redundant nominal coordinates do not weaken this obstruction. -/
theorem scalar_joint_requires_integral (T : Task K F)
    {r : Three → ℕ} {b : ℕ} (c : T.LinearCode 1 r b)
    (hu : c.toCode.uploadCost = T.uploadOptimum)
    (hd : c.toCode.broadcastCost = broadcastOptimum T.A T.U) :
    (∃ z : ℤ, T.uploadOptimum = z) ∧ (∃ z : ℤ, broadcastOptimum T.A T.U = z) := by
  simpa only [hu,hd] using c.scalar_costs_integral

/-- With a genuine two-instance corner supplied, no additional converse or
closure hypothesis remains in the main region assembly. -/
theorem region_eq_rectangle_of_joint_two (T : Task K F)
    (hcorner : (T.uploadOptimum,broadcastOptimum T.A T.U) ∈ T.achievableAt 2) :
    T.achievableAt 2 = budgetRectangle T.uploadOptimum (broadcastOptimum T.A T.U) ∧
    T.costRegion = budgetRectangle T.uploadOptimum (broadcastOptimum T.A T.U) := by
  apply T.region_eq_rectangle_of_upload_and_corner T.uploadOptimum hcorner
  intro L m s c hL
  exact c.uploadOptimum_le hL

end UploadBroadcast.Task
