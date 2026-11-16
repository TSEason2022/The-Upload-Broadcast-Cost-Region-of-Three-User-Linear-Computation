import UploadBroadcast.FiniteRelayAssembly
import UploadBroadcast.IntegerMenuRealization
import UploadBroadcast.BinaryAugmentedAllocation

/-! Integer choices are converted to actual subspaces of finite product tasks.
The local menu hypothesis describes all geometric menu realizers; no selected
relay, final profile, or global optimality is an input. -/
namespace UploadBroadcast.GlobalMenuAssembly
open Module FiniteRelayAssembly
open scoped BigOperators
variable {K I : Type*} {F : I → Type*} [Field K] [Fintype I]
  [∀ t, AddCommGroup (F t)] [∀ t, Module K (F t)]
  [∀ t, FiniteDimensional K (F t)]

/-- A local geometric menu, with unchanged second-family entries encoded by
zero increments when appropriate. -/
def RealizesMenu {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : Task K V) (d : ℕ) {C : Type*}
    (inc : C → Profile.Index → ℝ) : Prop :=
  ∀ k, ∃ P : Submodule K V, ∃ hg : T.LocallyGenerated P,
    T.RelayFeasible P ∧ finrank K P=d ∧
    ∀ r, Profile.entry (T.inducedRelay P hg) r ≤ Profile.entry T r+inc k r

/-- Every genuine local menu selection gives a concrete global relay, exact
rank addition, and all fifteen profile bounds. -/
theorem assemble_choices (T : (t : I) → Task K (F t)) (C : I → Type*)
    (d : I → ℕ) (inc : (t : I) → C t → Profile.Index → ℝ)
    (hmenu : ∀ t, RealizesMenu (T t) (d t) (inc t))
    (choose : (t : I) → C t) (budget : Profile.Index → ℝ)
    (hbudget : ∀ r, Profile.entry (task T) r + (∑ t, inc t (choose t) r) ≤ budget r) :
    ∃ P : Submodule K (∀ t, F t), ∃ hg : (task T).LocallyGenerated P,
      (task T).RelayFeasible P ∧ finrank K P = ∑ t, d t ∧
      ∀ r, Profile.entry ((task T).inducedRelay P hg) r ≤ budget r := by
  classical
  choose P hg hf hd hp using fun t => hmenu t (choose t)
  refine ⟨space P,locally_generated T P hg,relay_feasible T P hf,?_,?_⟩
  · simp only [finrank_space,hd]
  · intro r
    rw [FiniteRelayAssembly.inducedRelay_entry]
    calc
      (∑ t, Profile.entry ((T t).inducedRelay (P t) (hg t)) r) ≤
          ∑ t, (Profile.entry (T t) r + inc t (choose t) r) :=
        Finset.sum_le_sum fun t _ => hp t r
      _ = Profile.entry (task T) r + (∑ t, inc t (choose t) r) := by
        rw [Finset.sum_add_distrib,entry_task]
      _ ≤ budget r := hbudget r

/-- Natural multiplicities are realized on actual, possibly nonisomorphic,
component tasks sharing the same local increment menu. -/
theorem assemble_nat_weights {C : Type*} [Fintype C]
    (T : (t : I) → Task K (F t)) (d : I → ℕ)
    (inc : C → Profile.Index → ℝ)
    (hmenu : ∀ t, RealizesMenu (T t) (d t) inc)
    (w : C → ℕ) (hw : ∑ k, w k = Fintype.card I)
    (budget : Profile.Index → ℝ)
    (hbudget : ∀ r, Profile.entry (task T) r + (∑ k, (w k : ℝ)*inc k r) ≤ budget r) :
    ∃ P : Submodule K (∀ t, F t), ∃ hg : (task T).LocallyGenerated P,
      (task T).RelayFeasible P ∧ finrank K P = ∑ t, d t ∧
      ∀ r, Profile.entry ((task T).inducedRelay P hg) r ≤ budget r := by
  obtain ⟨choose,hchoose⟩ := Allocation.realize_nat_menu (I := I) w hw
  exact assemble_choices T (fun _ => C) d (fun _ => inc) hmenu choose budget
    (fun r => by rw [hchoose (fun k => inc k r)]; exact hbudget r)

/-- Signed nonnegative integer weights also select one actual menu per copy. -/
theorem assemble_int_weights {C : Type*} [Fintype C]
    (T : (t : I) → Task K (F t)) (d : I → ℕ)
    (inc : C → Profile.Index → ℝ)
    (hmenu : ∀ t, RealizesMenu (T t) (d t) inc)
    (v : C → ℤ) (hv : ∀ k, 0 ≤ v k) (hvs : ∑ k, v k = Fintype.card I)
    (budget : Profile.Index → ℝ)
    (hbudget : ∀ r, Profile.entry (task T) r + (∑ k, (v k : ℝ)*inc k r) ≤ budget r) :
    ∃ P : Submodule K (∀ t, F t), ∃ hg : (task T).LocallyGenerated P,
      (task T).RelayFeasible P ∧ finrank K P = ∑ t, d t ∧
      ∀ r, Profile.entry ((task T).inducedRelay P hg) r ≤ budget r := by
  have he (k : C) : ((v k).toNat : ℤ) = v k := Int.toNat_of_nonneg (hv k)
  have hw : ∑ k, (v k).toNat = Fintype.card I := by
    have hh : ((∑ k, (v k).toNat : ℕ) : ℤ) = Fintype.card I := by
      simp only [Nat.cast_sum,he,hvs]
    exact_mod_cast hh
  apply assemble_nat_weights T d inc hmenu (fun k => (v k).toNat) hw budget
  intro r
  have her (k : C) : ((v k).toNat : ℝ) = (v k : ℝ) := by exact_mod_cast he k
  simpa only [her] using hbudget r

/-- Extend six first-entry costs by zero on the nine second entries. -/
def firstIncrement (inc : Fin 6 → ℤ) : Profile.Index → ℝ
  | .inl r => inc r
  | .inr _ => 0

/-- The integer reservation theorem now produces an actual relay, not merely
menu labels or weights. The assumptions on each menu are its local fitting
and local geometric realization, independent of the global budget. -/
theorem assemble_charged_menus (T : (t : I) → Task K (F t)) (C : I → Type*)
    (d : I → ℕ) (inc : (t : I) → C t → Fin 6 → ℤ) (q : I → Fin 3 → ℤ)
    (hq : ∀ t p, 0 ≤ q t p)
    (hfit : ∀ t (c : Fin 6 → ℤ), (∀ j, 0 ≤ c j) →
      (∀ p, q t p ≤ c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p)) →
      ∃ k, ∀ j, inc t k j ≤ c j)
    (hmenu : ∀ t, RealizesMenu (T t) (d t) (fun k => firstIncrement (inc t k)))
    (c : Fin 6 → ℤ) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ p, (∑ t, q t p) ≤ c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p))
    (D : ℝ)
    (hfirst : ∀ j, Profile.entry (task T) (.inl j)+(c j : ℝ) ≤ D)
    (hsecond : ∀ r : Three × Three, Profile.entry (task T) (.inr r) ≤ D) :
    ∃ P : Submodule K (∀ t, F t), ∃ hg : (task T).LocallyGenerated P,
      (task T).RelayFeasible P ∧ finrank K P = ∑ t, d t ∧
      ∀ r, Profile.entry ((task T).inducedRelay P hg) r ≤ D := by
  obtain ⟨choose,hchoose⟩ := BinaryAugmentedAllocation.integer_choice_aggregate C inc q hq hfit c hc hp
  apply assemble_choices T C d (fun t k => firstIncrement (inc t k)) hmenu choose (fun _ => D)
  intro r
  cases r with
  | inl r =>
    have h : (∑ t, (inc t (choose t) r : ℝ)) ≤ (c r : ℝ) := by exact_mod_cast hchoose r
    exact (add_le_add_left h _).trans (hfirst r)
  | inr r => simpa only [firstIncrement,Finset.sum_const_zero,add_zero] using hsecond r

/-- Finite assembly of prescribed actual repaired/profile-preserving menus. -/
theorem finite_fixed_realizes (T : (t : I) → Task K (F t)) (d : I → ℕ)
    (delta : I → Profile.Index → ℝ)
    (hmenu : ∀ t, RealizesMenu (T t) (d t) (fun (_ : Unit) => delta t)) :
    RealizesMenu (task T) (∑ t, d t) (fun (_ : Unit) r => ∑ t, delta t r) := by
  intro k
  exact assemble_choices T (fun _ => Unit) d (fun t _ => delta t) hmenu (fun _ => ())
    (fun r => Profile.entry (task T) r+(∑ t, delta t r)) (fun _ => le_rfl)

section FixedProduct
variable {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Actual fixed menus combine on an actual product task. -/
theorem product_fixed_realizes (T : Task K V) (S : Task K W) (d e : ℕ)
    (delta gamma : Profile.Index → ℝ)
    (hT : RealizesMenu T d (fun (_ : Unit) => delta))
    (hS : RealizesMenu S e (fun (_ : Unit) => gamma)) :
    RealizesMenu (Profile.directSum T S) (d+e) (fun (_ : Unit) r => delta r+gamma r) := by
  intro k
  obtain ⟨P,hPl,hPf,hPd,hPprof⟩ := hT ()
  obtain ⟨Q,hQl,hQf,hQd,hQprof⟩ := hS ()
  refine ⟨P.prod Q,OptimalRelaySeparation.product_locally_generated _ _ _ _ hPl hQl,
    OptimalRelaySeparation.product_relay_feasible _ _ _ _ hPf hQf,?_,?_⟩
  · rw [Profile.finrank_submodule_prod,hPd,hQd]
  · intro r
    rw [product_inducedRelay_entry T S P Q hPl hQl r,Profile.entry_directSum]
    have hh := add_le_add (hPprof r) (hQprof r)
    dsimp only at hh ⊢
    linarith only [hh]

end FixedProduct

end UploadBroadcast.GlobalMenuAssembly
