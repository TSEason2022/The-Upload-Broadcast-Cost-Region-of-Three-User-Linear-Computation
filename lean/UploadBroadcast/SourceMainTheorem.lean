import UploadBroadcast.ResidualBackgroundSelectionTheorem
import UploadBroadcast.CanonicalSelectionAssembly
import UploadBroadcast.BinaryOperationalTightness

/-! Unconditional source-facing global theorems. Every geometric selection
input is discharged by the constructed original-field relay theorem. -/
namespace UploadBroadcast
variable {K F : Type} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- The canonical global geometry is a theorem, not an axiom or premise. -/
theorem canonical_scalar_selection (K : Type) [Field K] [Finite K] : CanonicalScalarSelection K :=
  canonicalScalarSelection_of_residualBackground
    (ResidualBackgroundSelectionTheorem.residual_background_selection K)

namespace Task
/-- Every original feasible task admits the required scalar relay selection,
with all normalization and passive restoration constructed internally. -/
theorem scalar_relay_selection (T : Task K F) : T.ScalarRelaySelection :=
  T.scalarRelaySelection_of_canonical (canonical_scalar_selection K)

/-- Source prop:stable, strengthened from active reduced tasks to arbitrary
original feasible coefficient tasks. -/
theorem stable_relay (T : Task K F) (D : ℤ)
    (hD : broadcastOptimum T.A T.U ≤ (D:ℝ))
    (hU : ∃ z : ℤ, T.uploadOptimum=(z:ℝ)) : Nonempty (T.ScalarRelayWitness D) :=
  T.scalar_relay_selection D hD hU

/-- Expanded original-space source statement, including the binary side
separation on actual ambient intersections. Local generation supplies their sum. -/
theorem stable_relay_source (T : Task K F) (D : ℤ)
    (hD : broadcastOptimum T.A T.U ≤ (D:ℝ))
    (hU : ∃ z : ℤ, T.uploadOptimum=(z:ℝ)) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (Module.finrank K P : ℝ)=T.uploadOptimum ∧
      (∀ r, Profile.entry (T.inducedRelay P hg) r ≤ (D:ℝ)) ∧
      (Nat.card K=2 → ∃ p : Equiv.Perm Three,
        (P ⊓ T.A (p 0)) ⊓ ((P ⊓ T.A (p 1)) ⊔ (P ⊓ T.A (p 2)))=⊥) := by
  obtain ⟨w⟩ := T.stable_relay D hD hU
  refine ⟨w.space,w.locallyGenerated,w.feasible,w.upload_optimal,w.profile_bound,?_⟩
  intro hK
  obtain ⟨p,hp⟩ := w.binary_separation hK
  exact ⟨p,(OptimalRelaySeparation.induced_separation_iff T.A w.space p).mp hp⟩

/-- Source lem:binary-integer-relay, with its stronger separation conclusion. -/
theorem binary_integer_relay (T : Task K F) (hK : Nat.card K=2) (D : ℤ)
    (hD : broadcastOptimum T.A T.U ≤ (D:ℝ))
    (hU : ∃ z : ℤ, T.uploadOptimum=(z:ℝ)) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ (Module.finrank K P : ℝ)=T.uploadOptimum ∧
      (∀ r, Profile.entry (T.inducedRelay P hg) r ≤ (D:ℝ)) ∧
      ∃ p : Equiv.Perm Three,
        (P ⊓ T.A (p 0)) ⊓ ((P ⊓ T.A (p 1)) ⊔ (P ⊓ T.A (p 2)))=⊥ := by
  obtain ⟨P,hg,hf,hu,hp,hs⟩ := T.stable_relay_source D hD hU
  exact ⟨P,hg,hf,hu,hp,hs hK⟩

/-- Source cor:scalar-budget: both attained-alphabet costs are exact. -/
theorem scalar_budget (T : Task K F) (hU : ∃ z : ℤ, T.uploadOptimum=(z:ℝ)) :
    ∃ (r : Three→ℕ) (b : ℕ) (c : T.LinearCode 1 r b),
      c.toCode.uploadCost=T.uploadOptimum ∧
      c.toCode.broadcastCost=((⌈broadcastOptimum T.A T.U⌉:ℤ):ℝ) :=
  T.scalar_ceiling_of_selection T.scalar_relay_selection hU

/-- Actual simultaneous optimal length-two linear code over the original
finite field, including the binary field. -/
theorem joint_two (T : Task K F) : T.LinearJointAt 2 :=
  T.joint_two_of_doubled_selection (Profile.directSum T T).scalar_relay_selection

/-- Source thm:intro-main: L=2 already gives the full closed nonlinear budget
region, with the original upload formula and fully informed fifteen-entry bound. -/
theorem main_region (T : Task K F) :
    T.achievableAt 2=budgetRectangle T.minimumUploadFormula (Profile.rankBound T) ∧
    T.costRegion=budgetRectangle T.minimumUploadFormula (Profile.rankBound T) := by
  have h := T.region_eq_rectangle_of_doubled_selection
    (Profile.directSum T T).scalar_relay_selection
  simpa only [T.minimum_upload,task_general_broadcastOptimum_eq_rankBound] using h

/-- The least original-field linear blocklength is exactly one when both
optima are integers, and exactly two otherwise. -/
theorem minimum_linear_blocklength (T : Task K F) :
    IsLeast {L : ℕ | 0<L ∧ T.LinearJointAt L} T.linearJointLengthFormula :=
  T.least_linear_joint_blocklength_of_selection T.scalar_relay_selection
    (Profile.directSum T T).scalar_relay_selection

theorem scalar_joint_iff_integral (T : Task K F) :
    T.LinearJointAt 1 ↔ (∃ z : ℤ, T.uploadOptimum=(z:ℝ)) ∧
      (∃ z : ℤ, broadcastOptimum T.A T.U=(z:ℝ)) :=
  T.linearJointAt_one_iff_of_selection T.scalar_relay_selection

end Task

/-- The uniform blocklength-two bound is tight even against nonlinear codes,
in the actual operational model rather than a separate Boolean toy model. -/
theorem nonlinear_uniform_bound_tight :
    BinaryOperationalTightness.task.LinearJointAt 2 ∧
      ∀ (m : Three→ℕ) (s : ℕ)
        (c : BinaryOperationalTightness.task.Code 1 (fun i => Fin (m i)) (Fin s)),
        broadcastOptimum BinaryOperationalTightness.task.A BinaryOperationalTightness.task.U <
          c.broadcastCost :=
  ⟨BinaryOperationalTightness.task.joint_two,fun _ _ c => BinaryOperationalTightness.scalar_broadcast_cost_strict c⟩

end UploadBroadcast
