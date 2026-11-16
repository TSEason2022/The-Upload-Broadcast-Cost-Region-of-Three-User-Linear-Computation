import UploadBroadcast.EndpointArithmetic
import UploadBroadcast.RelayLinearComposition
import UploadBroadcast.RelayTask

/-! Operational endpoint assembly from actual relay spaces. The explicitly
named `ScalarRelaySelection` property is a remaining geometric input, not a
proved arbitrary-task selection theorem. No theorem in this file silently
assumes that a numerical profile allocation is a communication code. -/
namespace UploadBroadcast.Task
open Module
variable {K F : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Concrete geometric input for an integer-budget scalar endpoint. The
binary separation condition is required only when the original field has
cardinality two. Its sides span automatically by local generation. -/
structure ScalarRelayWitness (T : Task K F) (D : ℤ) where
  space : Submodule K F
  locallyGenerated : T.LocallyGenerated space
  feasible : T.RelayFeasible space
  upload_optimal : (finrank K space : ℝ) = T.uploadOptimum
  profile_bound : ∀ r, Profile.entry (T.inducedRelay space locallyGenerated) r ≤ (D : ℝ)
  binary_separation : Nat.card K = 2 → ∃ p : Equiv.Perm Three,
    (T.A (p 0)).comap space.subtype ⊓
      ((T.A (p 1)).comap space.subtype ⊔ (T.A (p 2)).comap space.subtype) = ⊥

/-- Precisely the unresolved arbitrary-task geometric selection premise.
This definition is not asserted to hold for all tasks. -/
def ScalarRelaySelection (T : Task K F) : Prop :=
  ∀ D : ℤ, broadcastOptimum T.A T.U ≤ (D : ℝ) →
    (∃ z : ℤ, T.uploadOptimum = z) → Nonempty (T.ScalarRelayWitness D)

namespace ScalarRelayWitness
variable {T : Task K F} {D : ℤ}

theorem induced_optimum_le (w : T.ScalarRelayWitness D) :
    broadcastOptimum (fun i => (T.A i).comap w.space.subtype)
      (fun i => (T.U i).comap w.space.subtype) ≤ (D : ℝ) := by
  change broadcastOptimum (T.inducedRelay w.space w.locallyGenerated).A
    (T.inducedRelay w.space w.locallyGenerated).U ≤ _
  rw [task_general_broadcastOptimum_eq_rankBound]
  exact Finset.sup'_le _ _ (fun r _ => w.profile_bound r)

/-- Actual original-field linear uploads and broadcast from a concrete
relay: upload cost equals the operational minimum; broadcast meets D. -/
theorem scalar_code (w : T.ScalarRelayWitness D) :
    ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode 1 r b),
      c.toCode.uploadCost = T.uploadOptimum ∧ c.toCode.broadcastCost ≤ (D : ℝ) := by
  have hceil : ((⌈broadcastOptimum (fun i => (T.A i).comap w.space.subtype)
      (fun i => (T.U i).comap w.space.subtype)⌉ : ℤ) : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast (Int.ceil_le.mpr w.induced_optimum_le)
  have hex : ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode 1 r b),
      c.toCode.uploadCost ≤ finrank K w.space ∧ c.toCode.broadcastCost ≤ (D : ℝ) := by
    by_cases hq : 3 ≤ Nat.card K
    · obtain ⟨r,b,c,_,hu,hd⟩ := RelayLinearComposition.exists_code_at_induced_ceiling
        T w.space w.locallyGenerated w.feasible hq
      exact ⟨r,b,c,hu,hd.trans hceil⟩
    · letI := Fintype.ofFinite K
      have htwo : Nat.card K = 2 := by
        have h := Finite.one_lt_card (α := K)
        omega
      have hK : Fintype.card K = 2 := by simpa only [Nat.card_eq_fintype_card] using htwo
      obtain ⟨p,hsep⟩ := w.binary_separation htwo
      obtain ⟨r,b,c,_,hu,hd⟩ := RelayLinearComposition.exists_binary_code_at_induced_ceiling
        T w.space w.locallyGenerated w.feasible hK
        (T.induced_sides_span w.space w.locallyGenerated) p hsep
      exact ⟨r,b,c,hu,hd.trans hceil⟩
  obtain ⟨r,b,c,hu,hd⟩ := hex
  exact ⟨r,b,c,le_antisymm (hu.trans_eq w.upload_optimal)
    (c.uploadOptimum_le (by decide)),hd⟩
end ScalarRelayWitness

/-- Scalar linear broadcast cost cannot fall below the ceiling of D*, even
if its nominal alphabet contains unused coordinates. -/
theorem LinearCode.scalar_ceiling_le {T : Task K F} {r : Three → ℕ} {b : ℕ}
    (c : T.LinearCode 1 r b) :
    ((⌈broadcastOptimum T.A T.U⌉ : ℤ) : ℝ) ≤ c.toCode.broadcastCost := by
  obtain ⟨z,hz⟩ := c.scalar_costs_integral.2
  rw [hz]
  exact_mod_cast (Int.ceil_le.mpr (by
    rw [← hz]
    exact c.toCode.broadcastOptimum_le (by decide)))

/-- Exact scalar endpoint, conditional only on the displayed actual relay
at the original task's ceiling budget. -/
theorem scalar_ceiling_of_actual_relay (T : Task K F)
    (w : T.ScalarRelayWitness ⌈broadcastOptimum T.A T.U⌉) :
    ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode 1 r b),
      c.toCode.uploadCost = T.uploadOptimum ∧
      c.toCode.broadcastCost = ((⌈broadcastOptimum T.A T.U⌉ : ℤ) : ℝ) := by
  obtain ⟨r,b,c,hu,hd⟩ := w.scalar_code
  exact ⟨r,b,c,hu,le_antisymm hd c.scalar_ceiling_le⟩

/-- Field-size-at-least-three endpoint, stated directly with the actual
relay hypotheses. No binary separation premise is needed in this branch. -/
theorem scalar_ceiling_of_large_field_relay (T : Task K F)
    (P : Submodule K F) (hg : T.LocallyGenerated P) (hf : T.RelayFeasible P)
    (hu : (finrank K P : ℝ) = T.uploadOptimum)
    (hp : ∀ r, Profile.entry (T.inducedRelay P hg) r ≤
      ((⌈broadcastOptimum T.A T.U⌉ : ℤ) : ℝ))
    (hq : 3 ≤ Nat.card K) :
    ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode 1 r b),
      c.toCode.uploadCost = T.uploadOptimum ∧
      c.toCode.broadcastCost = ((⌈broadcastOptimum T.A T.U⌉ : ℤ) : ℝ) := by
  apply T.scalar_ceiling_of_actual_relay
  refine ⟨P,hg,hf,hu,hp,?_⟩
  intro h
  omega

/-- Separated-relay endpoint over the original field, including the binary
field. Spanning of the induced sides follows from local generation. -/
theorem scalar_ceiling_of_separated_relay (T : Task K F)
    (P : Submodule K F) (hg : T.LocallyGenerated P) (hf : T.RelayFeasible P)
    (hu : (finrank K P : ℝ) = T.uploadOptimum)
    (hp : ∀ r, Profile.entry (T.inducedRelay P hg) r ≤
      ((⌈broadcastOptimum T.A T.U⌉ : ℤ) : ℝ))
    (p : Equiv.Perm Three)
    (hs : (T.A (p 0)).comap P.subtype ⊓
      ((T.A (p 1)).comap P.subtype ⊔ (T.A (p 2)).comap P.subtype) = ⊥) :
    ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode 1 r b),
      c.toCode.uploadCost = T.uploadOptimum ∧
      c.toCode.broadcastCost = ((⌈broadcastOptimum T.A T.U⌉ : ℤ) : ℝ) := by
  apply T.scalar_ceiling_of_actual_relay
  exact ⟨P,hg,hf,hu,hp,fun _ => ⟨p,hs⟩⟩

/-- Conditional form of the source scalar-budget corollary. The selection
hypothesis remains explicit until the arbitrary-task geometric theorem is
proved. -/
theorem scalar_ceiling_of_selection (T : Task K F) (hselect : T.ScalarRelaySelection)
    (hu : ∃ z : ℤ, T.uploadOptimum = z) :
    ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode 1 r b),
      c.toCode.uploadCost = T.uploadOptimum ∧
      c.toCode.broadcastCost = ((⌈broadcastOptimum T.A T.U⌉ : ℤ) : ℝ) := by
  obtain ⟨w⟩ := hselect _ (Int.le_ceil _) hu
  exact T.scalar_ceiling_of_actual_relay w

/-- An integral pair of minima is a scalar corner under actual relay
selection, with both attained-alphabet costs exact. -/
theorem scalar_joint_of_selection (T : Task K F) (hselect : T.ScalarRelaySelection)
    (hu : ∃ z : ℤ, T.uploadOptimum = z)
    (hd : ∃ z : ℤ, broadcastOptimum T.A T.U = z) :
    ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode 1 r b),
      c.toCode.uploadCost = T.uploadOptimum ∧
      c.toCode.broadcastCost = broadcastOptimum T.A T.U := by
  obtain ⟨r,b,c,hcu,hcd⟩ := T.scalar_ceiling_of_selection hselect hu
  obtain ⟨z,hz⟩ := hd
  refine ⟨r,b,c,hcu,?_⟩
  simpa only [hz,Int.ceil_intCast] using hcd

/-- Two-instance exact corner from actual scalar relay selection on the
*doubled task*. All doubling, integrality and code-flattening steps are
proved, over the original field including cardinality two. -/
theorem joint_two_of_doubled_selection (T : Task K F)
    (hselect : (Profile.directSum T T).ScalarRelaySelection) :
    ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode 2 r b),
      c.toCode.uploadCost = T.uploadOptimum ∧
      c.toCode.broadcastCost = broadcastOptimum T.A T.U := by
  obtain ⟨hu,hd⟩ := T.doubled_optima_integral
  obtain ⟨r,b,c,hcu,hcd⟩ := (Profile.directSum T T).scalar_joint_of_selection hselect hu hd
  refine ⟨r,b,c.toBlockDouble,?_,?_⟩
  · rw [c.toBlockDouble_uploadCost,hcu,T.uploadOptimum_double]
    ring
  · rw [c.toBlockDouble_broadcastCost,hcd,T.broadcastOptimum_double]
    ring

/-- A single actual relay on the doubled task is sufficient; the caller
need not supply a selection procedure for every budget. -/
theorem joint_two_of_actual_doubled_relay (T : Task K F)
    (w : (Profile.directSum T T).ScalarRelayWitness
      ⌈broadcastOptimum (Profile.directSum T T).A (Profile.directSum T T).U⌉) :
    ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode 2 r b),
      c.toCode.uploadCost = T.uploadOptimum ∧
      c.toCode.broadcastCost = broadcastOptimum T.A T.U := by
  obtain ⟨r,b,c,hu,hd⟩ := (Profile.directSum T T).scalar_ceiling_of_actual_relay w
  obtain ⟨z,hz⟩ := T.doubled_optima_integral.2
  have hd' : c.toCode.broadcastCost =
      broadcastOptimum (Profile.directSum T T).A (Profile.directSum T T).U := by
    simpa only [hz,Int.ceil_intCast] using hd
  refine ⟨r,b,c.toBlockDouble,?_,?_⟩
  · rw [c.toBlockDouble_uploadCost,hu,T.uploadOptimum_double]
    ring
  · rw [c.toBlockDouble_broadcastCost,hd',T.broadcastOptimum_double]
    ring

/-- Actual linear corner attainment at a specified original-field blocklength. -/
def LinearJointAt (T : Task K F) (L : ℕ) : Prop :=
  ∃ (r : Three → ℕ) (b : ℕ) (c : T.LinearCode L r b),
    c.toCode.uploadCost = T.uploadOptimum ∧
    c.toCode.broadcastCost = broadcastOptimum T.A T.U

/-- The exact scalar criterion, conditional on the explicit selection input
for this task. The necessity direction is unconditional. -/
theorem linearJointAt_one_iff_of_selection (T : Task K F)
    (hselect : T.ScalarRelaySelection) :
    T.LinearJointAt 1 ↔
      (∃ z : ℤ, T.uploadOptimum = z) ∧
      (∃ z : ℤ, broadcastOptimum T.A T.U = z) := by
  constructor
  · rintro ⟨r,b,c,hu,hd⟩
    exact T.scalar_joint_requires_integral c hu hd
  · rintro ⟨hu,hd⟩
    exact T.scalar_joint_of_selection hselect hu hd

/-- The manuscript's one-or-two-instance expression; this is only a
numerical candidate until the subsequent IsLeast theorem is applied. -/
noncomputable def linearJointLengthFormula (T : Task K F) : ℕ := by
  classical
  exact if (∃ z : ℤ, T.uploadOptimum = z) ∧
    (∃ z : ℤ, broadcastOptimum T.A T.U = z) then 1 else 2

/-- Exact minimum linear joint blocklength in the source's IsLeast form.
Both needed relay-selection assumptions remain explicit. This theorem does
not weaken the source's L=1-or-2 claim to an L≤4 extension-field bound. -/
theorem least_linear_joint_blocklength_of_selection (T : Task K F)
    (hselect : T.ScalarRelaySelection)
    (hdouble : (Profile.directSum T T).ScalarRelaySelection) :
    IsLeast {L : ℕ | 0 < L ∧ T.LinearJointAt L} T.linearJointLengthFormula := by
  classical
  unfold linearJointLengthFormula
  by_cases hi : (∃ z : ℤ, T.uploadOptimum = z) ∧
      (∃ z : ℤ, broadcastOptimum T.A T.U = z)
  · simp only [if_pos hi]
    refine ⟨⟨by decide,(T.linearJointAt_one_iff_of_selection hselect).mpr hi⟩,?_⟩
    intro L hL
    exact hL.1
  · simp only [if_neg hi]
    refine ⟨⟨by decide,T.joint_two_of_doubled_selection hdouble⟩,?_⟩
    intro L hL
    have hne : L ≠ 1 := by
      intro he
      have hc : T.LinearJointAt 1 := he ▸ hL.2
      exact hi ((T.linearJointAt_one_iff_of_selection hselect).mp hc)
    have hp : 0 < L := hL.1
    omega

/-- Conditional final region glue. This is not an unconditional proof of
source thm:intro-main: the remaining doubled-task relay-selection premise
is visible in the statement. -/
theorem region_eq_rectangle_of_doubled_selection (T : Task K F)
    (hselect : (Profile.directSum T T).ScalarRelaySelection) :
    T.achievableAt 2 = budgetRectangle T.uploadOptimum (broadcastOptimum T.A T.U) ∧
    T.costRegion = budgetRectangle T.uploadOptimum (broadcastOptimum T.A T.U) := by
  obtain ⟨r,b,c,hu,hd⟩ := T.joint_two_of_doubled_selection hselect
  apply T.region_eq_rectangle_of_joint_two
  simpa only [hu,hd] using c.mem_achievableAt (by decide)

/-- The main rectangle follows from just one concrete doubled-task relay;
no unproved universal selection property is hidden by this wrapper. -/
theorem region_eq_rectangle_of_actual_doubled_relay (T : Task K F)
    (w : (Profile.directSum T T).ScalarRelayWitness
      ⌈broadcastOptimum (Profile.directSum T T).A (Profile.directSum T T).U⌉) :
    T.achievableAt 2 = budgetRectangle T.uploadOptimum (broadcastOptimum T.A T.U) ∧
    T.costRegion = budgetRectangle T.uploadOptimum (broadcastOptimum T.A T.U) := by
  obtain ⟨r,b,c,hu,hd⟩ := T.joint_two_of_actual_doubled_relay w
  apply T.region_eq_rectangle_of_joint_two
  simpa only [hu,hd] using c.mem_achievableAt (by decide)

end UploadBroadcast.Task
