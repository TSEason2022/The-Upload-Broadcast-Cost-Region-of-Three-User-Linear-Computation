import UploadBroadcast.PhysicalScalarCycleChart
import UploadBroadcast.CycleFiniteAssembly
import UploadBroadcast.RelayCoordinateTransport

namespace UploadBroadcast.PhysicalCycleRelay
open Module GlobalMenuAssembly RelayCoordinateTransport
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Transport an entire local menu back through actual component coordinates. -/
theorem menu_of_equiv {C : Type*} (T : Task K V) (S : Task K W) (e : V ≃ₗ[K] W)
    (he : Profile.mapTask e T=S) (d : ℕ) (inc : C → Profile.Index → ℝ)
    (hm : RealizesMenu S d inc) : RealizesMenu T d inc := by
  have hb : Profile.mapTask e.symm S=T := by
    rw [← he]
    exact ResidualRelayAssembly.mapTask_inverse T e.symm
  have hp (r : Profile.Index) : Profile.entry S r=Profile.entry T r := by
    rw [← he,Profile.entry_mapTask]
  intro k
  apply transport_exists S T e.symm hb d (fun r => Profile.entry T r+inc k r)
  obtain ⟨P,hg,hf,hd,hp'⟩ := hm k
  exact ⟨P,hg,hf,hd,fun r => by simpa only [hp] using hp' r⟩

/-- Transport an entire local menu into a physical coefficient embedding. -/
theorem menu_of_image {C : Type*} (T : Task K V) (S : Task K W) (f : V →ₗ[K] W)
    (hi : Function.Injective f) (he : T.imageTask f=S) (d : ℕ) (inc : C → Profile.Index → ℝ)
    (hm : RealizesMenu T d inc) : RealizesMenu S d inc := by
  have hp (r : Profile.Index) : Profile.entry S r=Profile.entry T r := by
    rw [← he,Profile.entry_imageTask _ f hi]
  intro k
  apply transport_exists_image T S f hi he d (fun r => Profile.entry S r+inc k r)
  obtain ⟨P,hg,hf,hd,hp'⟩ := hm k
  exact ⟨P,hg,hf,hd,fun r => by simpa only [hp] using hp' r⟩

variable (K)

/-- Positive-cycle repair on the literal direct sum of the original Jordan
resonance and the scalar cycle, with no canonical-chart hypothesis. -/
theorem positive_directSum_realizes (n : ℕ) :
    RealizesMenu (Profile.directSum (ResonantRelay.jordanTask K n)
      (CycleDirectSumCoordinates.cycleTask K)) (3*(n+1)+4)
      (fun (_ : Unit) => firstIncrement CycleFiniteAssembly.positiveIncrement) := by
  apply menu_of_equiv _ (CycleRepair.canonicalTask K n) (CycleDirectSumCoordinates.coordinates K (n+1))
    (CycleDirectSumCoordinates.map_directSum K (n+1) (JordanResonance.shift K n) (JordanResonance.head K n))
  exact CycleFiniteAssembly.positive_realizes n

/-- The same literal direct-sum identity for the reverse demand cycle. -/
theorem negative_directSum_realizes (n : ℕ) :
    RealizesMenu (Profile.directSum (ResonantRelay.jordanTask K n)
      (CycleDirectSumCoordinates.reverseCycleTask K)) (3*(n+1)+4)
      (fun (_ : Unit) => firstIncrement CycleFiniteAssembly.negativeIncrement) := by
  apply menu_of_equiv _ (CycleRepair.canonicalReverseTask K n) (CycleDirectSumCoordinates.coordinates K (n+1))
    (CycleDirectSumCoordinates.map_reverseDirectSum K (n+1) (JordanResonance.shift K n) (JordanResonance.head K n))
  exact CycleFiniteAssembly.negative_realizes n

variable {K}
section ProductEmbedding
variable {X Y Z : Type*} [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]

theorem imageTask_product_right (T : Task K X) (S : Task K Y) (f : Y →ₗ[K] Z) :
    (Profile.directSum T S).imageTask ((LinearMap.id : X →ₗ[K] X).prodMap f) =
      Profile.directSum T (S.imageTask f) := by
  have hh (A : Submodule K X) (B : Submodule K Y) :
      (A.prod B).map ((LinearMap.id : X →ₗ[K] X).prodMap f)=A.prod (B.map f) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨hy.1,⟨y.2,hy.2,rfl⟩⟩
    · rintro ⟨ha,b,hb,he⟩
      exact ⟨(x.1,b),⟨ha,hb⟩,Prod.ext rfl he⟩
  have ha : ((Profile.directSum T S).imageTask ((LinearMap.id : X →ₗ[K] X).prodMap f)).A =
      (Profile.directSum T (S.imageTask f)).A := by funext i; exact hh _ _
  have hu : ((Profile.directSum T S).imageTask ((LinearMap.id : X →ₗ[K] X).prodMap f)).U =
      (Profile.directSum T (S.imageTask f)).U := by funext i; exact hh _ _
  cases h : (Profile.directSum T S).imageTask ((LinearMap.id : X →ₗ[K] X).prodMap f)
  cases h' : Profile.directSum T (S.imageTask f)
  simp_all only [Task.mk.injEq]

end ProductEmbedding

/-- An actual three-edge cycle extracted from the original task can be paired
with an original Jordan summand and repaired. Rank and all fifteen increments
come from a concrete relay in the physical ambient coefficient space. -/
theorem positive_physical_realizes (T : Task K V) (v : Three → V)
    (hv : LinearIndependent K v)
    (h₀ : EdgeExtraction.EdgeBlock T 0 1 2 (PhysicalScalarCycleChart.line v 0))
    (h₁ : EdgeExtraction.EdgeBlock T 1 2 0 (PhysicalScalarCycleChart.line v 1))
    (h₂ : EdgeExtraction.EdgeBlock T 2 0 1 (PhysicalScalarCycleChart.line v 2)) (n : ℕ) :
    RealizesMenu (Profile.directSum (ResonantRelay.jordanTask K n)
      (NonzeroDefectRelays.inducedTask T (Submodule.span K (Set.range v))
        (PhysicalScalarCycleChart.locally_generated T v h₀ h₁ h₂))) (3*(n+1)+4)
      (fun (_ : Unit) => firstIncrement CycleFiniteAssembly.positiveIncrement) := by
  let f := (LinearMap.id : ResonantEndomorphisms.Ambient K (JordanResonance.V K n) →ₗ[K] _).prodMap
    (PhysicalScalarCycleChart.coefficients (K := K) v)
  have hi : Function.Injective f := by
    intro a b he
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    exact Prod.ext h₁ (hv.fintypeLinearCombination_injective h₂)
  have he : (Profile.directSum (ResonantRelay.jordanTask K n)
      (CycleDirectSumCoordinates.cycleTask K)).imageTask f = _ :=
    (imageTask_product_right _ _ _).trans
      (congrArg (Profile.directSum (ResonantRelay.jordanTask K n))
        (PhysicalScalarCycleChart.image_task_eq T v h₀ h₁ h₂))
  exact menu_of_image _ _ f hi he _ _ (positive_directSum_realizes K n)

/-- Literal reverse-cycle repair in the actual physical coefficient space. -/
theorem negative_physical_realizes (T : Task K V) (v : Three → V)
    (hv : LinearIndependent K v)
    (h₀ : EdgeExtraction.EdgeBlock T 1 0 2 (PhysicalScalarCycleChart.line v 0))
    (h₁ : EdgeExtraction.EdgeBlock T 2 1 0 (PhysicalScalarCycleChart.line v 1))
    (h₂ : EdgeExtraction.EdgeBlock T 0 2 1 (PhysicalScalarCycleChart.line v 2)) (n : ℕ) :
    RealizesMenu (Profile.directSum (ResonantRelay.jordanTask K n)
      (NonzeroDefectRelays.inducedTask T (Submodule.span K (Set.range v))
        (PhysicalScalarCycleChart.reverse_locally_generated T v h₀ h₁ h₂))) (3*(n+1)+4)
      (fun (_ : Unit) => firstIncrement CycleFiniteAssembly.negativeIncrement) := by
  let f := (LinearMap.id : ResonantEndomorphisms.Ambient K (JordanResonance.V K n) →ₗ[K] _).prodMap
    (PhysicalScalarCycleChart.coefficients (K := K) v)
  have hi : Function.Injective f := by
    intro a b he
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    exact Prod.ext h₁ (hv.fintypeLinearCombination_injective h₂)
  have he : (Profile.directSum (ResonantRelay.jordanTask K n)
      (CycleDirectSumCoordinates.reverseCycleTask K)).imageTask f = _ :=
    (imageTask_product_right _ _ _).trans
      (congrArg (Profile.directSum (ResonantRelay.jordanTask K n))
        (PhysicalScalarCycleChart.image_reverse_task_eq T v h₀ h₁ h₂))
  exact menu_of_image _ _ f hi he _ _ (negative_directSum_realizes K n)

end UploadBroadcast.PhysicalCycleRelay
