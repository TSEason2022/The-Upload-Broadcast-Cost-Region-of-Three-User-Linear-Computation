import UploadBroadcast.SourceMainTheorem
import UploadBroadcast.CycleUploadOptimality
import UploadBroadcast.CycleDirectSumCoordinates
import UploadBroadcast.ResidualComponentFactors
import UploadBroadcast.RegularRelayOptimality

/-! Unconditional operational upload optima for the literal resonant family
and the five-bit binary task, with an actual length-two joint-optimal code. -/
namespace UploadBroadcast.ResonantUploadSpecializations
open ResidualComponentAdditivity
variable (K : Type*) [Field K]

/-- The original resonant coefficient task is intrinsically active. The
positive-cycle coordinate model supplies activity, which restricts to its
literal resonant direct summand. No activity or classification chart is assumed. -/
theorem jordan_active (n : ℕ) : ActiveResidual (ResonantRelay.jordanTask K n) := by
  let e := CycleDirectSumCoordinates.coordinates K (n+1)
  let T := Profile.directSum (ResonantRelay.jordanTask K n)
    (CycleDirectSumCoordinates.cycleTask K)
  have he : Profile.mapTask e T = CycleRepair.canonicalTask K n :=
    CycleDirectSumCoordinates.map_directSum K (n+1)
      (JordanResonance.shift K n) (JordanResonance.head K n)
  have ha := (CycleUploadOptimality.canonical_active K n).map e.symm
  have hb : Profile.mapTask e.symm (CycleRepair.canonicalTask K n)=T := by
    rw [←he]
    exact ResidualRelayAssembly.mapTask_inverse T e.symm
  rw [hb] at ha
  exact ha.directSum_left _ _

variable [Finite K]

/-- The source block R_(n+1) has exact nonlinear, regularized upload optimum
3(n+1)+1 over every finite field. -/
theorem jordan_uploadOptimum (n : ℕ) :
    (ResonantRelay.jordanTask K n).uploadOptimum = (3*(n+1)+1 : ℕ) := by
  rw [minimum_upload _ (jordan_active K n),RegularRelayOptimality.jordan_uploadValue]

/-- Source indexing: the manuscript's R_n has U*=3n+1 for every n≥1. -/
theorem source_uploadOptimum (n : ℕ) (hn : 1≤n) :
    (ResonantRelay.jordanTask K (n-1)).uploadOptimum = (3*n+1 : ℕ) := by
  have he : n-1+1=n := by omega
  simpa only [he] using jordan_uploadOptimum K (n-1)

section ScalarCoordinates
variable (K : Type*) [Field K]

/-- Evaluate each one-dimensional private block at its sole coordinate. -/
def scalarCoordinates : ResonantEndomorphisms.Ambient K (JordanResonance.V K 0) ≃ₗ[K]
    ResonantEndomorphisms.Ambient K K where
  toFun p := (p.1 0,p.2.1 0,p.2.2.1 0,p.2.2.2.1,p.2.2.2.2)
  invFun p := ((fun _ => p.1),(fun _ => p.2.1),(fun _ => p.2.2.1),p.2.2.2.1,p.2.2.2.2)
  left_inv p := by
    apply Prod.ext
    · funext i; fin_cases i; rfl
    apply Prod.ext
    · funext i; fin_cases i; rfl
    apply Prod.ext
    · funext i; fin_cases i; rfl
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The size-one Jordan task is exactly the scalar-coordinate resonant model. -/
theorem map_scalarCoordinates : Profile.mapTask (scalarCoordinates K)
    (ResonantRelay.jordanTask K 0)=ResonantRelay.task K K 0 LinearMap.id := by
  have ha : (Profile.mapTask (scalarCoordinates K) (ResonantRelay.jordanTask K 0)).A=
      (ResonantRelay.task K K 0 LinearMap.id).A := by
    funext i
    ext p
    change p ∈ (ResonantRelay.side K (JordanResonance.V K 0) i).map
      (scalarCoordinates K).toLinearMap ↔ p ∈ ResonantRelay.side K K i
    rw [Submodule.mem_map_equiv]
    fin_cases i <;>
      simp [ResonantRelay.side,ResonantEndomorphisms.side₁,ResonantEndomorphisms.side₂,
        ResonantEndomorphisms.side₃,scalarCoordinates,Pi.zero_def,funext_iff]
  have hu : (Profile.mapTask (scalarCoordinates K) (ResonantRelay.jordanTask K 0)).U=
      (ResonantRelay.task K K 0 LinearMap.id).U := by
    funext i
    ext p
    change p ∈ (ResonantRelay.signal K (JordanResonance.V K 0)
      (JordanResonance.shift K 0) (JordanResonance.head K 0) i).map
      (scalarCoordinates K).toLinearMap ↔ p ∈ ResonantRelay.signal K K 0 LinearMap.id i
    rw [Submodule.mem_map_equiv]
    fin_cases i <;>
      simp [ResonantRelay.signal,ResonantEndomorphisms.total₁,ResonantEndomorphisms.total₂,
        ResonantEndomorphisms.total₃,scalarCoordinates,Pi.zero_def,
        JordanResonance.shift,JordanResonance.head,funext_iff]
  cases h₁ : Profile.mapTask (scalarCoordinates K) (ResonantRelay.jordanTask K 0)
  cases h₂ : ResonantRelay.task K K 0 LinearMap.id
  simp_all only [Task.mk.injEq]

end ScalarCoordinates

/-- Intrinsic activity for the literal five-bit binary operational task. -/
theorem binary_active : ActiveResidual BinaryOperationalTightness.task := by
  have h := (jordan_active BinaryOperationalTightness.K 0).map
    (scalarCoordinates BinaryOperationalTightness.K)
  rwa [map_scalarCoordinates] at h

/-- Exact upload optimum of the literal five-bit task, with no coordinate
chart, activity assumption, or target-rank premise. -/
theorem binary_uploadOptimum : BinaryOperationalTightness.task.uploadOptimum=4 := by
  rw [minimum_upload _ binary_active]
  have h := uploadValue_map (ResonantRelay.jordanTask BinaryOperationalTightness.K 0)
    (scalarCoordinates BinaryOperationalTightness.K)
  rw [map_scalarCoordinates,RegularRelayOptimality.jordan_uploadValue] at h
  exact h

/-- A genuine original-field length-two linear code for the five-bit task
attains both exact costs (4,3/2) in the operational attained-alphabet model. -/
theorem binary_joint_two :
    ∃ (r : Three→ℕ) (b : ℕ) (c : BinaryOperationalTightness.task.LinearCode 2 r b),
      c.toCode.uploadCost=4 ∧ c.toCode.broadcastCost=3/2 := by
  obtain ⟨r,b,c,hu,hd⟩ := BinaryOperationalTightness.task.joint_two
  exact ⟨r,b,c,hu.trans binary_uploadOptimum,
    hd.trans BinaryOperationalTightness.broadcastOptimum_eq⟩

end UploadBroadcast.ResonantUploadSpecializations
