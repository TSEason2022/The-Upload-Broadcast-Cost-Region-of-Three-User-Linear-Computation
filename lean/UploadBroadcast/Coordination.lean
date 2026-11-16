import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith

/-! Finite-field kernel avoidance, sequential multigroup reconciliation, homogeneous
column coordination, and a verified deterministic exhaustive-search wrapper. -/

namespace UploadBroadcast
open Finset Module

/-- At most `|K|` nonzero linear functionals cannot have kernels covering a
finite-dimensional vector space over the finite field `K`. -/
theorem exists_forall_linearForm_ne_zero
    {K V I : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [Fintype V] [FiniteDimensional K V] [Fintype I]
    (f : I → V →ₗ[K] K) (hf : ∀ i, f i ≠ 0)
    (hcount : Fintype.card I ≤ Fintype.card K) :
    ∃ v : V, ∀ i, f i v ≠ 0 := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h => exact ⟨0, fun i => isEmptyElim i⟩
  | inr h =>
    let i₀ : I := Classical.choice h
    let q := Fintype.card K
    let n := finrank K V
    have hn : 1 ≤ n := by
      have hh := Module.Dual.finrank_ker_add_one_of_ne_zero (hf i₀)
      dsimp [n]
      omega
    have hq : 1 < q := Fintype.one_lt_card
    let s : I → Finset V := fun i => Finset.univ.filter (fun v => f i v = 0)
    have hs0 (i : I) : (0 : V) ∈ s i := by simp [s]
    have hscard (i : I) : (s i).card = q ^ (n - 1) := by
      have hk : finrank K (LinearMap.ker (f i)) = n - 1 := by
        have hh := Module.Dual.finrank_ker_add_one_of_ne_zero (hf i)
        dsimp [n]
        omega
      have hc := Module.card_eq_pow_finrank (K := K) (V := LinearMap.ker (f i))
      simpa [s, q, hk, Fintype.card_subtype] using hc
    let bad : Finset V := insert 0 (Finset.univ.biUnion fun i => (s i).erase 0)
    have hbad : bad.card ≤ 1 + Fintype.card I * (q ^ (n - 1) - 1) := by
      calc
        bad.card ≤ (Finset.univ.biUnion fun i => (s i).erase 0).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ (∑ i : I, ((s i).erase 0).card) + 1 :=
          Nat.add_le_add_right (Finset.card_biUnion_le) 1
        _ = 1 + Fintype.card I * (q ^ (n - 1) - 1) := by
          simp_rw [Finset.card_erase_of_mem (hs0 _), hscard]
          simp [Nat.add_comm]
    have hpow : 0 < q ^ (n - 1) := pow_pos (by omega) _
    have hpoweq : q ^ n = q ^ (n - 1) * q := by
      rw [← pow_succ]
      congr 1
      omega
    have hstrict : 1 + Fintype.card I * (q ^ (n - 1) - 1) < q ^ n := by
      have hm : Fintype.card I * (q ^ (n - 1) - 1) ≤
          q * (q ^ (n - 1) - 1) := Nat.mul_le_mul_right _ hcount
      have hp : q ^ (n - 1) - 1 + 1 = q ^ (n - 1) := Nat.sub_add_cancel (by omega)
      rw [hpoweq]
      nlinarith
    have hlt : bad.card < (Finset.univ : Finset V).card := by
      have hc := Module.card_eq_pow_finrank (K := K) (V := V)
      simpa [q, n, hc] using lt_of_le_of_lt hbad hstrict
    obtain ⟨v, _, hv⟩ := Finset.exists_mem_not_mem_of_card_lt_card hlt
    refine ⟨v, fun i hi => hv ?_⟩
    by_cases hz : v = 0
    · simp [bad, hz]
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      exact ⟨i, Finset.mem_univ _, by simp [s, hz, hi]⟩

/-- Sequential coordination with a verified per-group update rule. This
allows binary pair groups and binary aligned groups to use different proofs
of simultaneous feasibility at a single update. -/
theorem simultaneous_nonzero_of_update_rule
    {K G I : Type*} [Zero K] [DecidableEq G] [Fintype G]
    (V : G → Type*) [∀ g, Zero (V g)]
    (c : I → ((g : G) → V g) → K)
    (hwitness : ∀ i, ∃ a, c i a ≠ 0)
    (hstep : ∀ g (a : I → ((g : G) → V g)),
      (∀ i, c i (a i) ≠ 0) → ∃ x : V g, ∀ i, c i (Function.update (a i) g x) ≠ 0) :
    ∃ a, ∀ i, c i a ≠ 0 := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h => exact ⟨fun _ => 0, fun i => isEmptyElim i⟩
  | inr h =>
    have progress (s : Finset G) :
        ∃ a : I → ((g : G) → V g),
          (∀ i, c i (a i) ≠ 0) ∧ (∀ g ∈ s, ∀ i j, a i g = a j g) := by
      induction s using Finset.induction_on with
      | empty =>
        choose a ha using hwitness
        exact ⟨a, ha, by simp⟩
      | @insert g s hgs ih =>
        obtain ⟨a,ha,hagree⟩ := ih
        obtain ⟨x,hx⟩ := hstep g a ha
        refine ⟨fun i => Function.update (a i) g x, hx, ?_⟩
        intro k hk i j
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simp
        · have hkg : k ≠ g := by intro he; exact hgs (he ▸ hk)
          simpa [Function.update_of_ne hkg] using hagree k hk i j
    obtain ⟨a,ha,hagree⟩ := progress Finset.univ
    let i₀ : I := Classical.choice h
    refine ⟨a i₀, fun i => ?_⟩
    have he : a i₀ = a i := funext fun g => hagree g (Finset.mem_univ _) i₀ i
    rw [he]
    exact ha i

/-- A family of constraints whose dependence on one parameter group is either
homogeneous linear or constant. This is the property used by determinants when
each group supplies at most one column. -/
def LinearOrConstantSlices {K G I : Type*} [DecidableEq G] [Field K]
    (V : G → Type*) [∀ g, AddCommGroup (V g)] [∀ g, Module K (V g)]
    (c : I → ((g : G) → V g) → K) : Prop :=
  ∀ i g a, (∃ l : V g →ₗ[K] K, ∀ x, c i (Function.update a g x) = l x) ∨
    (∀ x, c i (Function.update a g x) = c i a)

/-- Reconcile separately feasible homogeneous-linear-or-constant constraints.
This verifies the sequential group-selection argument, independently of the
matrix-to-slice representation. -/
theorem simultaneous_nonzero_of_slices
    {K G I : Type*} [DecidableEq G] [Field K] [Fintype K] [Fintype G] [Fintype I]
    (V : G → Type*) [∀ g, AddCommGroup (V g)] [∀ g, Module K (V g)]
    [∀ g, Fintype (V g)] [∀ g, FiniteDimensional K (V g)]
    (c : I → ((g : G) → V g) → K)
    (hslices : LinearOrConstantSlices V c)
    (hwitness : ∀ i, ∃ a, c i a ≠ 0)
    (hcount : Fintype.card I ≤ Fintype.card K) :
    ∃ a, ∀ i, c i a ≠ 0 := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h => exact ⟨fun _ => 0, fun i => isEmptyElim i⟩
  | inr h =>
    have progress (s : Finset G) :
        ∃ a : I → ((g : G) → V g),
          (∀ i, c i (a i) ≠ 0) ∧ (∀ g ∈ s, ∀ i j, a i g = a j g) := by
      induction s using Finset.induction_on with
      | empty =>
        choose a ha using hwitness
        exact ⟨a, ha, by simp⟩
      | @insert g s hgs ih =>
        obtain ⟨a, ha, hagree⟩ := ih
        let active : Set I := {i | ¬ ∀ x, c i (Function.update (a i) g x) = c i (a i)}
        have hl (i : active) :
            ∃ l : V g →ₗ[K] K, ∀ x, c i.1 (Function.update (a i.1) g x) = l x := by
          exact (hslices i.1 g (a i.1)).resolve_right i.2
        choose l hleq using hl
        have hlnz (i : active) : l i ≠ 0 := by
          intro hz
          have he := hleq i (a i.1 g)
          simp [hz] at he
          exact ha i.1 he
        have hcard : Fintype.card active ≤ Fintype.card K :=
          (Fintype.card_subtype_le _).trans hcount
        obtain ⟨x, hx⟩ := exists_forall_linearForm_ne_zero l hlnz hcard
        refine ⟨fun i => Function.update (a i) g x, ?_, ?_⟩
        · intro i
          by_cases hi : i ∈ active
          · rw [hleq ⟨i, hi⟩ x]
            exact hx ⟨i, hi⟩
          · have hc : ∀ y, c i (Function.update (a i) g y) = c i (a i) :=
              Classical.not_not.mp hi
            rw [hc x]
            exact ha i
        · intro k hk i j
          rcases Finset.mem_insert.mp hk with rfl | hk
          · simp
          · have hkg : k ≠ g := by intro he; exact hgs (he ▸ hk)
            simpa [Function.update_of_ne hkg] using hagree k hk i j
    obtain ⟨a, ha, hagree⟩ := progress Finset.univ
    let i₀ : I := Classical.choice h
    refine ⟨a i₀, fun i => ?_⟩
    have he : a i₀ = a i := funext fun g => hagree g (Finset.mem_univ _) i₀ i
    rw [he]
    exact ha i

/-- Faithful column-local form of the paper's homogeneous-column hypothesis:
updating a group either leaves the matrix unchanged or replaces one column
by a homogeneous linear image of that group. -/
def HomogeneousColumnGroups {K G I : Type*} [DecidableEq G] [Field K]
    (V : G → Type*) [∀ g, AddCommGroup (V g)] [∀ g, Module K (V g)]
    (N : I → Type*) [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)]
    (C : (i : I) → ((g : G) → V g) → Matrix (N i) (N i) K) : Prop :=
  ∀ i g a,
    (∀ x, C i (Function.update a g x) = C i a) ∨
    (∃ (j : N i) (l : V g →ₗ[K] (N i → K)),
      ∀ x, C i (Function.update a g x) = Matrix.updateCol (C i a) j (l x))

/-- Homogeneous column coordination (paper lemma `lem:column-reconciliation`),
existence component. Finite exhaustive search supplies a deterministic choice.
Square matrix sizes and parameter-group dimensions may vary. -/
theorem homogeneous_column_coordination
    {K G I : Type*} [DecidableEq G] [Field K] [Fintype K] [Fintype G] [Fintype I]
    (V : G → Type*) [∀ g, AddCommGroup (V g)] [∀ g, Module K (V g)]
    [∀ g, Fintype (V g)] [∀ g, FiniteDimensional K (V g)]
    (N : I → Type*) [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)]
    (C : (i : I) → ((g : G) → V g) → Matrix (N i) (N i) K)
    (hcolumns : HomogeneousColumnGroups V N C)
    (hwitness : ∀ i, ∃ a, (C i a).det ≠ 0)
    (hcount : Fintype.card I ≤ Fintype.card K) :
    ∃ a, ∀ i, (C i a).det ≠ 0 := by
  classical
  apply simultaneous_nonzero_of_slices V (fun i a => (C i a).det) ?_ hwitness hcount
  intro i g a
  rcases hcolumns i g a with hconstant | ⟨j, l, hcol⟩
  · exact Or.inr (fun x => congrArg Matrix.det (hconstant x))
  · refine Or.inl ⟨(LinearMap.proj j).comp ((Matrix.cramer (C i a)).comp l), ?_⟩
    intro x
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, Matrix.cramer_apply]
    rw [hcol x]

/-- Matrix-invertibility spelling of homogeneous column coordination. -/
theorem homogeneous_column_coordination_invertible
    {K G I : Type*} [DecidableEq G] [Field K] [Fintype K] [Fintype G] [Fintype I]
    (V : G → Type*) [∀ g, AddCommGroup (V g)] [∀ g, Module K (V g)]
    [∀ g, Fintype (V g)] [∀ g, FiniteDimensional K (V g)]
    (N : I → Type*) [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)]
    (C : (i : I) → ((g : G) → V g) → Matrix (N i) (N i) K)
    (hcolumns : HomogeneousColumnGroups V N C)
    (hwitness : ∀ i, ∃ a, IsUnit (C i a))
    (hcount : Fintype.card I ≤ Fintype.card K) :
    ∃ a, ∀ i, IsUnit (C i a) := by
  have hw : ∀ i, ∃ a, (C i a).det ≠ 0 := by
    intro i
    obtain ⟨a,ha⟩ := hwitness i
    exact ⟨a, ((Matrix.isUnit_iff_isUnit_det _).mp ha).ne_zero⟩
  obtain ⟨a,ha⟩ := homogeneous_column_coordination V N C hcolumns hw hcount
  exact ⟨a, fun i => (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (ha i))⟩

/-- Deterministic exhaustive search over a supplied complete finite enumeration. -/
def firstSatisfying {A : Type*} (xs : List A) (p : A → Prop) [DecidablePred p] : Option A :=
  xs.find? (fun a => decide (p a))

theorem firstSatisfying_sound {A : Type*} (xs : List A) (p : A → Prop)
    [DecidablePred p] {a : A} (h : firstSatisfying xs p = some a) : p a := by
  have hh : decide (p a) = true := List.find?_some (p := fun a => decide (p a)) h
  exact of_decide_eq_true hh

theorem firstSatisfying_complete {A : Type*} (xs : List A) (p : A → Prop)
    [DecidablePred p] (hcomplete : ∀ a, a ∈ xs) (hex : ∃ a, p a) :
    (firstSatisfying xs p).isSome := by
  obtain ⟨a, ha⟩ := hex
  apply List.find?_isSome.mpr
  exact ⟨a, hcomplete a, by simpa using ha⟩

/-- Complete deterministic search specialized to the paper's matrix constraints.
`xs` is any complete finite enumeration of the parameter assignments. -/
theorem homogeneous_column_search
    {K G I : Type*} [DecidableEq G] [Field K] [DecidableEq K]
    [Fintype K] [Fintype G] [Fintype I]
    (V : G → Type*) [∀ g, AddCommGroup (V g)] [∀ g, Module K (V g)]
    [∀ g, Fintype (V g)] [∀ g, FiniteDimensional K (V g)]
    (N : I → Type*) [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)]
    (C : (i : I) → ((g : G) → V g) → Matrix (N i) (N i) K)
    (hcolumns : HomogeneousColumnGroups V N C)
    (hwitness : ∀ i, ∃ a, (C i a).det ≠ 0)
    (hcount : Fintype.card I ≤ Fintype.card K)
    (xs : List ((g : G) → V g)) (hcomplete : ∀ a, a ∈ xs) :
    (firstSatisfying xs (fun a => ∀ i, (C i a).det ≠ 0)).isSome ∧
    (∀ a, firstSatisfying xs (fun a => ∀ i, (C i a).det ≠ 0) = some a →
      ∀ i, IsUnit (C i a)) := by
  constructor
  · apply firstSatisfying_complete xs _ hcomplete
    exact homogeneous_column_coordination V N C hcolumns hwitness hcount
  · intro a ha i
    exact (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (firstSatisfying_sound xs _ ha i))

end UploadBroadcast
