import UploadBroadcast.TaskQuiverBridge
import UploadBroadcast.QuiverHomLinear
import UploadBroadcast.ProjectionCriterion

/-!
# Concrete thin probes for intersections

The test objects here are actual one-dimensional flag configurations. Their
Hom spaces into any six-subspace task are linearly equivalent to the selected
subspace intersections. No generic-position assertion is used.
-/
namespace UploadBroadcast.IntersectionProbes
open TaskDecomposition QuiverRepresentation

structure Probe where
  middle : Finset (Fin 3)
  outer : Finset (Fin 3)
  nested : outer ⊆ middle

variable (K : Type) [Field K]

def Probe.task (p : Probe) : TaskDecomposition.Task K K where
  A i := if i ∈ p.outer then ⊤ else ⊥
  U i := if i ∈ p.middle then ⊤ else ⊥
  nested i := by
    by_cases hi : i ∈ p.outer
    · simp [hi, p.nested hi]
    · simp [hi]

/-- Every thin connected probe is indecomposable over the original field. -/
theorem Probe.indecomposable (p : Probe) :
    TaskDecomposition.Indecomposable (p.task K).spaces ⊤ := by
  apply indecomposable_of_projection_eq_zero_or_id top_ne_bot
  intro f _ hf
  have hfx (x : K) : f x = x * f 1 := by
    simpa using f.map_smul x (1 : K)
  have ha : f 1 * (f 1 - 1) = 0 := by
    have hh := hf 1
    rw [hfx (f 1)] at hh
    linear_combination hh
  obtain hz | ho := mul_eq_zero.mp ha
  · left
    apply LinearMap.ext
    intro x
    change f x = 0
    rw [hfx x, hz, mul_zero]
  · right
    have ho' : f 1 = 1 := sub_eq_zero.mp ho
    apply LinearMap.ext
    intro x
    change f x = x
    rw [hfx x, ho', mul_one]

theorem Probe.rep_indecomposable (p : Probe) :
    QuiverRepresentation.Indecomposable (p.task K).toRep :=
  (p.task K).rep_indec_of_indec (p.indecomposable K)

/-- The dimension vector of the literal top/bottom probe. -/
def Probe.dimension (p : Probe) : E6Vertex → ℤ
  | .center => 1
  | .middle i => if i ∈ p.middle then 1 else 0
  | .outer i => if i ∈ p.outer then 1 else 0

@[simp] theorem Probe.rep_dimension (p : Probe) :
    QuiverRepresentation.dimension (p.task K).toRep = p.dimension := by
  funext v
  cases v with
  | center => simp [QuiverRepresentation.dimension, Task.toRep, Probe.task, Probe.dimension]
  | middle i =>
    change (Module.finrank K ↥(if i ∈ p.middle then (⊤ : Submodule K K) else ⊥) : ℤ) =
      if i ∈ p.middle then 1 else 0
    by_cases hi : i ∈ p.middle
    · rw [if_pos hi]; simp [hi]
    · rw [if_neg hi]; simp [hi]
  | outer i =>
    change (Module.finrank K ↥(if i ∈ p.outer then (⊤ : Submodule K K) else ⊥) : ℤ) =
      if i ∈ p.outer then 1 else 0
    by_cases hi : i ∈ p.outer
    · rw [if_pos hi]; simp [hi]
    · rw [if_neg hi]; simp [hi]

variable {K} {F : Type} [AddCommGroup F] [Module K F]

/-- Literal intersection of all selected signal and side spaces. -/
def Probe.intersection (p : Probe) (T : TaskDecomposition.Task K F) : Submodule K F where
  carrier := {x | (∀ i ∈ p.middle, x ∈ T.U i) ∧ (∀ i ∈ p.outer, x ∈ T.A i)}
  zero_mem' := ⟨fun _ _ => Submodule.zero_mem _, fun _ _ => Submodule.zero_mem _⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨fun i hi => (T.U i).add_mem (hx.1 i hi) (hy.1 i hi),
      fun i hi => (T.A i).add_mem (hx.2 i hi) (hy.2 i hi)⟩
  smul_mem' := by
    intro a x hx
    exact ⟨fun i hi => (T.U i).smul_mem a (hx.1 i hi),
      fun i hi => (T.A i).smul_mem a (hx.2 i hi)⟩

/-- A selected-intersection vector gives the actual quiver morphism. -/
def Probe.homOfVector (p : Probe) (T : TaskDecomposition.Task K F)
    (x : p.intersection T) : Hom (p.task K).toRep T.toRep :=
  (p.task K).homOfPreserves T (LinearMap.toSpanSingleton K F x.val) (by
    rintro ⟨i,b⟩ a ha
    cases b with
    | false =>
      change a • x.val ∈ T.A i
      by_cases hi : i ∈ p.outer
      · exact (T.A i).smul_mem _ (x.property.2 i hi)
      · have hz : a = 0 := by simpa [Task.spaces, Probe.task, hi] using ha
        simp [hz]
    | true =>
      change a • x.val ∈ T.U i
      by_cases hi : i ∈ p.middle
      · exact (T.U i).smul_mem _ (x.property.1 i hi)
      · have hz : a = 0 := by simpa [Task.spaces, Probe.task, hi] using ha
        simp [hz])

/-- Evaluate the ambient component at one to recover the intersection vector. -/
def Probe.vectorOfHom (p : Probe) (T : TaskDecomposition.Task K F)
    (f : Hom (p.task K).toRep T.toRep) : p.intersection T :=
  ⟨f.map .center (1 : K), by
    have hp := (p.task K).preservesOfHom T f
    constructor
    · intro i hi
      exact hp (i,true) 1 (by simp [Task.spaces, Probe.task, hi])
    · intro i hi
      exact hp (i,false) 1 (by simp [Task.spaces, Probe.task, hi])⟩

/-- Hom from a concrete thin probe is exactly the actual selected intersection. -/
def Probe.homLinearEquiv (p : Probe) (T : TaskDecomposition.Task K F) :
    Hom (p.task K).toRep T.toRep ≃ₗ[K] p.intersection T where
  toFun := p.vectorOfHom T
  invFun := p.homOfVector T
  left_inv f := by
    apply (p.task K).hom_center_ext T
    apply LinearMap.ext
    intro a
    change a • f.map .center (1 : K) = f.map .center a
    simpa using (f.map .center).map_smul a (1 : K) |>.symm
  right_inv x := by
    apply Subtype.ext
    change (1 : K) • x.val = x.val
    exact one_smul _ _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Probe.hom_finrank (p : Probe) (T : TaskDecomposition.Task K F) :
    Module.finrank K (Hom (p.task K).toRep T.toRep) =
      Module.finrank K (p.intersection T) := (p.homLinearEquiv T).finrank_eq

/-- Pair of signal spaces. -/
def signalPair (i j : Fin 3) : Probe := ⟨{i,j}, ∅, by simp⟩
/-- One side space intersected with a remote signal space. -/
def sideSignal (i j : Fin 3) : Probe := ⟨{i,j}, {i}, by simp⟩
/-- Common intersection of all three signal spaces. -/
def signalTriple : Probe := ⟨Finset.univ, ∅, by simp⟩
/-- Triple signal intersection conditioned on one side space. -/
def sideTriple (i : Fin 3) : Probe := ⟨Finset.univ, {i}, by simp⟩
/-- Two side spaces, with their compulsory middle vertices. -/
def sidePair (i j : Fin 3) : Probe := ⟨{i,j}, {i,j}, fun _ h => h⟩

@[simp] theorem signalPair_intersection (T : TaskDecomposition.Task K F) (i j : Fin 3) :
    (signalPair i j).intersection T = T.U i ⊓ T.U j := by
  ext x
  simp [Probe.intersection, signalPair]

@[simp] theorem sideSignal_intersection (T : TaskDecomposition.Task K F) (i j : Fin 3) :
    (sideSignal i j).intersection T = T.A i ⊓ T.U j := by
  ext x
  simp only [Probe.intersection, sideSignal, Submodule.mem_mk, Set.mem_setOf_eq,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Submodule.mem_inf]
  exact ⟨fun h => ⟨h.2,h.1.2⟩, fun h => ⟨⟨T.nested i h.1,h.2⟩,h.1⟩⟩

@[simp] theorem signalTriple_intersection (T : TaskDecomposition.Task K F) :
    signalTriple.intersection T = T.U 0 ⊓ T.U 1 ⊓ T.U 2 := by
  ext x
  simp only [Probe.intersection, signalTriple, Submodule.mem_mk, Set.mem_setOf_eq,
    Finset.mem_univ, forall_true_left, Finset.not_mem_empty, IsEmpty.forall_iff,
    implies_true, and_true, Submodule.mem_inf]
  constructor
  · intro h; exact ⟨⟨h 0,h 1⟩,h 2⟩
  · intro h i; fin_cases i <;> tauto

@[simp] theorem sideTriple_intersection (T : TaskDecomposition.Task K F) (i : Fin 3) :
    (sideTriple i).intersection T = (T.U 0 ⊓ T.U 1 ⊓ T.U 2) ⊓ T.A i := by
  rw [← signalTriple_intersection]
  ext x
  simp [Probe.intersection, sideTriple, signalTriple]

@[simp] theorem sidePair_intersection (T : TaskDecomposition.Task K F) (i j : Fin 3) :
    (sidePair i j).intersection T = T.A i ⊓ T.A j := by
  ext x
  simp only [Probe.intersection, sidePair, Submodule.mem_mk, Set.mem_setOf_eq,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Submodule.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨⟨T.nested i h.1,T.nested j h.2⟩,h⟩⟩

end UploadBroadcast.IntersectionProbes
