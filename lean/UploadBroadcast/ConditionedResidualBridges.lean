import UploadBroadcast.GlobalUploadGeometry
import UploadBroadcast.ResidualPrivateSplit

/-! The signal-intersection bridge lemma at the manuscript's full strength:
all retained inequalities for arbitrary nonlinear codes jointly encoding an
omniscience summand and the constructed active residual task. -/
namespace UploadBroadcast.ConditionedResidualBridges
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
open MeasureTheory ProbabilityTheory
open ResidualUpload ResidualTaskAssembly GlobalUploadGeometry

variable {K E F P₁ P₂ P₃ D : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]

/-- Construct the residual geometry directly from the canonical reduction.
In particular, none of the intersection bridges, private inverses, or
retained entropy inequalities is a hypothesis of this construction. -/
noncomputable def canonicalResidualGeometry
    (task : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D) :
    ResidualGeometry (canonicalReduction task h₀ h₁ h₂) := by
  let res := canonicalReduction task h₀ h₁ h₂
  let a := canonicalReductionBridge task h₀ h₁ h₂
  obtain ⟨hs₀,hs₁,hs₂⟩ := canonicalReduction_sides task h₀ h₁ h₂
  obtain ⟨hu₀,hu₁,hu₂⟩ := canonicalReduction_fully_used task h₀ h₁ h₂
  have hU : ∀ i, res.U i = ![a.U₁,a.U₂,a.U₃] i := by intro i; fin_cases i <;> rfl
  have pair : ∀ i j, i ≠ j → Disjoint (res.A i) (res.A j) := by
    have hd₀₁ : Disjoint (res.A 0) (res.A 1) := by rw [hs₀,hs₁]; exact sides_disjoint₁₂
    have hd₀₂ : Disjoint (res.A 0) (res.A 2) := by rw [hs₀,hs₂]; exact sides_disjoint₁₃
    have hd₁₂ : Disjoint (res.A 1) (res.A 2) := by rw [hs₁,hs₂]; exact sides_disjoint₂₃
    intro i j hij
    have hd₁₀ := hd₀₁.symm
    have hd₂₀ := hd₀₂.symm
    have hd₂₁ := hd₁₂.symm
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hd₀₁
    · exact hd₀₂
    · exact hd₁₀
    · exact (hij rfl).elim
    · exact hd₁₂
    · exact hd₂₀
    · exact hd₂₁
    · exact (hij rfl).elim
  have priv : ∀ i, ResidualConverse.PrivateSplit res i (tripodSpaces a.v a.r i) := by
    exact ResidualPrivateSplit.fully_used_splits res hs₀ hs₁ hs₂ hu₀ hu₁ hu₂
  exact of_active_data res a hU pair priv

/-- The signal-space inclusion and both cyclic counterparts hold for the
constructed canonical task, using its actual signed-relation bridge. -/
theorem canonicalReduction_all_tripod_bridges
    (task : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D) :
    let res := canonicalReduction task h₀ h₁ h₂
    let a := canonicalReductionBridge task h₀ h₁ h₂
    (LinearMap.range a.v ⊔ LinearMap.range a.r ≤ res.U 2 ⊔ (res.U 0 ⊓ res.U 1)) ∧
    (LinearMap.range a.v ⊔ LinearMap.range a.r ≤ res.U 1 ⊔ (res.U 2 ⊓ res.U 0)) ∧
    (LinearMap.range a.v ⊔ LinearMap.range a.r ≤ res.U 0 ⊔ (res.U 1 ⊓ res.U 2)) :=
  SignalBridge.all_tripod_bridges (canonicalReductionBridge task h₀ h₁ h₂)

local instance sourceMeasurable (V : Type*) [AddCommGroup V] [Module K V] (n : ℕ) :
    MeasurableSpace (Source K V n) := ⊤
local instance sourceDiscrete (V : Type*) [AddCommGroup V] [Module K V] (n : ℕ) :
    DiscreteMeasurableSpace (Source K V n) := ⟨fun _ => trivial⟩

section Finite
variable [Finite K] [FiniteDimensional K E] [FiniteDimensional K F]

/-- The q-ary Ω-conditioned retained bounds for actual joint codes on a
direct sum. The messages need not split into independent factor codes. -/
theorem directSum_conditioned_retained_bounds {n : ℕ} {M : Three → Type*} {B : Type*}
    [∀ i, Fintype (M i)] [∀ i, MeasurableSpace (M i)] [∀ i, DiscreteMeasurableSpace (M i)]
    (om : Task K E) (res : Task K F) (hom : ∀ i, om.U i = ⊤)
    (r : ResidualGeometry res) (code : (Profile.directSum om res).Code n M B) :
    let μ := uniformOn (Set.univ : Set (Source K (E × F) n))
    let obs := fun A : Submodule K (E × F) => UploadBroadcast.observe K (E × F) A (L := n)
    let Ω := obs ((⊤ : Submodule K E).prod (⊥ : Submodule K F))
    let W := fun i => obs ((⊥ : Submodule K E).prod (res.A i))
    let msg := fun i x => code.encode i (obs ((om.A i).prod (res.A i)) x)
    let q := Real.log (Nat.card K)
    let Γ := (n : ℝ) * (2 * (Module.finrank K ↥(res.A 0 ⊔ res.A 1 ⊔ res.A 2) : ℝ) -
      (Module.finrank K (res.A 0) + Module.finrank K (res.A 1) + Module.finrank K (res.A 2)))
    let J : Three → ℝ := ![
      condMutualInfo (msg 1) (msg 2) (fun x => (W 0 x, Ω x)) μ / q,
      condMutualInfo (msg 0) (msg 2) (fun x => (W 1 x, Ω x)) μ / q,
      condMutualInfo (msg 0) (msg 1) (fun x => (W 2 x, Ω x)) μ / q]
    ∀ i j, i ≠ j → Γ + J i + J j ≤
      condEntropy (msg 0) Ω μ / q + condEntropy (msg 1) Ω μ / q + condEntropy (msg 2) Ω μ / q := by
  have hb := GlobalUploadConverse.code_conditioned_retained_rank_bounds
    (Profile.directSum om res) (directSumGeometry om res hom r) code
  simp only [directSumGeometry, Profile.directSum] at hb
  rw [Submodule.prod_sup_prod, Submodule.prod_sup_prod, bot_sup_eq, bot_sup_eq] at hb
  simpa only [bot_sup_eq,
    Profile.finrank_submodule_prod, finrank_bot, Nat.cast_zero, zero_add] using hb
end Finite

section Canonical
variable [Finite K] [FiniteDimensional K E]
  [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K D]
  (task : Task K (Ambient P₁ P₂ P₃ D))
  (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
  (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
  (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)
abbrev CanonicalAmbient := Ambient (used₁ task) (used₂ task) (used₃ task)
  (selectedTrimData task h₀ h₁ h₂).activeRows
local notation "V" => CanonicalAmbient task h₀ h₁ h₂

/-- Source-strength form of the signal-intersection bridge lemma. On the
actual constructed active residual task, every arbitrary joint Ω⊕residual
code obeys all three retained inequalities with Γ = n(dpriv+dtri). The
canonical signal intersections, private slices, independence and rank
identity are proved from the task, rather than supplied as certificates. -/
theorem canonicalReduction_conditioned_retained_bounds {n : ℕ} {M : Three → Type*} {B : Type*}
    [∀ i, Fintype (M i)] [∀ i, MeasurableSpace (M i)] [∀ i, DiscreteMeasurableSpace (M i)]
    (om : Task K E) (hom : ∀ i, om.U i = ⊤)
    (code : (Profile.directSum om (canonicalReduction task h₀ h₁ h₂)).Code n M B) :
    let res := canonicalReduction task h₀ h₁ h₂
    let μ := uniformOn (Set.univ : Set (Source K (E × V) n))
    let obs := fun A : Submodule K (E × V) => UploadBroadcast.observe K (E × V) A (L := n)
    let Ω := obs ((⊤ : Submodule K E).prod (⊥ : Submodule K V))
    let W := fun i => obs ((⊥ : Submodule K E).prod (res.A i))
    let msg := fun i x => code.encode i (obs ((om.A i).prod (res.A i)) x)
    let q := Real.log (Nat.card K)
    let Γ := (n : ℝ) * ((Module.finrank K (used₁ task) : ℝ) + Module.finrank K (used₂ task) +
      Module.finrank K (used₃ task) + Module.finrank K (selectedTrimData task h₀ h₁ h₂).activeRows)
    let J : Three → ℝ := ![
      condMutualInfo (msg 1) (msg 2) (fun x => (W 0 x, Ω x)) μ / q,
      condMutualInfo (msg 0) (msg 2) (fun x => (W 1 x, Ω x)) μ / q,
      condMutualInfo (msg 0) (msg 1) (fun x => (W 2 x, Ω x)) μ / q]
    ∀ i j, i ≠ j → Γ + J i + J j ≤
      condEntropy (msg 0) Ω μ / q + condEntropy (msg 1) Ω μ / q + condEntropy (msg 2) Ω μ / q := by
  let res := canonicalReduction task h₀ h₁ h₂
  have hb := directSum_conditioned_retained_bounds om res hom
    (canonicalResidualGeometry task h₀ h₁ h₂) code
  obtain ⟨hs₀,hs₁,hs₂⟩ := canonicalReduction_sides task h₀ h₁ h₂
  have hg : 2 * (Module.finrank K ↥(res.A 0 ⊔ res.A 1 ⊔ res.A 2) : ℝ) -
      (Module.finrank K (res.A 0) + Module.finrank K (res.A 1) + Module.finrank K (res.A 2)) =
      (Module.finrank K (used₁ task) : ℝ) + Module.finrank K (used₂ task) +
        Module.finrank K (used₃ task) + Module.finrank K (selectedTrimData task h₀ h₁ h₂).activeRows := by
    rw [hs₀,hs₁,hs₂,sides_span,finrank_top]
    exact_mod_cast (gamma_rank (K := K) (P₁ := used₁ task) (P₂ := used₂ task)
      (P₃ := used₃ task) (T := (selectedTrimData task h₀ h₁ h₂).activeRows))
  dsimp only at hb ⊢
  simpa only [hg] using hb
end Canonical

end UploadBroadcast.ConditionedResidualBridges
