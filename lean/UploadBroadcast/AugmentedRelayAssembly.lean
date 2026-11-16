import UploadBroadcast.ResonantFiniteAssembly
import UploadBroadcast.NonzeroFiniteAssembly

namespace UploadBroadcast.AugmentedRelayAssembly
open Module FiniteRelayAssembly GlobalMenuAssembly
open scoped BigOperators
variable {K I R : Type*} {F : I → Type*} [Field K] [Fintype I] [Fintype R]
  [∀ t, AddCommGroup (F t)] [∀ t, Module K (F t)] [∀ t, FiniteDimensional K (F t)]

/-- Resonant-first integer allocation constructs one actual relay for the
whole finite task. The orientation inequalities and strengthened opposite-pair
inequalities are numerical preconditions; no relay choice or profile bound is
assumed for the resulting relay. -/
theorem resonant_charged_relay (n : R → ℕ) (T : (t : I) → Task K (F t))
    (C : I → Type*) (d : I → ℕ) (inc : (t : I) → C t → Fin 6 → ℤ)
    (q : I → Fin 3 → ℤ) (hq : ∀ t p, 0 ≤ q t p)
    (hfit : ∀ t (c : Fin 6 → ℤ), (∀ j, 0 ≤ c j) →
      (∀ p, q t p ≤ c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p)) →
      ∃ k, ∀ j, inc t k j ≤ c j)
    (hmenu : ∀ t, RealizesMenu (T t) (d t) (fun k => firstIncrement (inc t k)))
    (c : Fin 6 → ℤ) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ p, (Fintype.card R : ℤ)+(∑ t, q t p) ≤
      c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p))
    (hplus : (Fintype.card R : ℤ) ≤ c 0+c 3+c 4)
    (hminus : (Fintype.card R : ℤ) ≤ c 1+c 2+c 5)
    (D : ℝ)
    (hfirst : ∀ j, Profile.entry (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T))
      (.inl j)+(c j : ℝ) ≤ D)
    (hsecond : ∀ r : Three × Three,
      Profile.entry (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) (.inr r) ≤ D) :
    ∃ P : Submodule K (ResonantFiniteAssembly.Ambient (K := K) n × (∀ t, F t)),
      ∃ hg : (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)).LocallyGenerated P,
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)).RelayFeasible P ∧
      finrank K P = (∑ t, (3*(n t+1)+1))+(∑ t, d t) ∧
      ∀ r, Profile.entry ((Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)).inducedRelay P hg) r ≤ D := by
  obtain ⟨v,choose,hv,hvs,hcap⟩ := BinaryAugmentedAllocation.augmented_integer_choices
    C inc q hq hfit (Fintype.card R) c (Nat.cast_nonneg _) hc hp hplus hminus
  obtain ⟨P,hPg,hPf,hPd,hPprof⟩ := ResonantFiniteAssembly.exists_of_weights (K := K) n v hv hvs
  obtain ⟨Q,hQg,hQf,hQd,hQprof⟩ := assemble_choices T C d
    (fun t k => firstIncrement (inc t k)) hmenu choose
    (fun r => Profile.entry (task T) r+(∑ t, firstIncrement (inc t (choose t)) r))
    (fun _ => le_rfl)
  refine ⟨P.prod Q,OptimalRelaySeparation.product_locally_generated _ _ _ _ hPg hQg,
    OptimalRelaySeparation.product_relay_feasible _ _ _ _ hPf hQf,?_,?_⟩
  · rw [Profile.finrank_submodule_prod,hPd,hQd]
  · intro r
    rw [product_inducedRelay_entry]
    have hpr := add_le_add (hPprof r) (hQprof r)
    apply hpr.trans
    cases r with
    | inl r =>
      have hh : (BinaryAugmentedAllocation.resonantIncrement v r : ℝ)+
          (∑ t, (inc t (choose t) r : ℝ)) ≤ (c r : ℝ) := by exact_mod_cast hcap r
      have hb := hfirst r
      rw [Profile.entry_directSum] at hb
      simp only [firstIncrement]
      linarith
    | inr r =>
      simpa only [firstIncrement,Finset.sum_const_zero,add_zero,Profile.entry_directSum] using hsecond r

/-- Entry-dependent budget version, used when fixed repaired blocks or Ω
profiles are reserved before packing the remaining components. -/
theorem resonant_charged_relay_budget (n : R → ℕ) (T : (t : I) → Task K (F t))
    (C : I → Type*) (d : I → ℕ) (inc : (t : I) → C t → Fin 6 → ℤ)
    (q : I → Fin 3 → ℤ) (hq : ∀ t p, 0 ≤ q t p)
    (hfit : ∀ t (c : Fin 6 → ℤ), (∀ j, 0 ≤ c j) →
      (∀ p, q t p ≤ c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p)) →
      ∃ k, ∀ j, inc t k j ≤ c j)
    (hmenu : ∀ t, RealizesMenu (T t) (d t) (fun k => firstIncrement (inc t k)))
    (c : Fin 6 → ℤ) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ p, (Fintype.card R : ℤ)+(∑ t, q t p) ≤
      c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p))
    (hplus : (Fintype.card R : ℤ) ≤ c 0+c 3+c 4)
    (hminus : (Fintype.card R : ℤ) ≤ c 1+c 2+c 5)
    (budget : Profile.Index → ℝ)
    (hfirst : ∀ j, Profile.entry (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T))
      (.inl j)+(c j : ℝ) ≤ budget (.inl j))
    (hsecond : ∀ r : Three × Three,
      Profile.entry (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) (.inr r) ≤ budget (.inr r)) :
    ∃ P : Submodule K (ResonantFiniteAssembly.Ambient (K := K) n × (∀ t, F t)),
      ∃ hg : (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)).LocallyGenerated P,
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)).RelayFeasible P ∧
      finrank K P = (∑ t, (3*(n t+1)+1))+(∑ t, d t) ∧
      ∀ r, Profile.entry ((Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)).inducedRelay P hg) r ≤ budget r := by
  obtain ⟨v,choose,hv,hvs,hcap⟩ := BinaryAugmentedAllocation.augmented_integer_choices
    C inc q hq hfit (Fintype.card R) c (Nat.cast_nonneg _) hc hp hplus hminus
  obtain ⟨P,hPg,hPf,hPd,hPprof⟩ := ResonantFiniteAssembly.exists_of_weights (K := K) n v hv hvs
  obtain ⟨Q,hQg,hQf,hQd,hQprof⟩ := assemble_choices T C d
    (fun t k => firstIncrement (inc t k)) hmenu choose
    (fun r => Profile.entry (task T) r+(∑ t, firstIncrement (inc t (choose t)) r))
    (fun _ => le_rfl)
  refine ⟨P.prod Q,OptimalRelaySeparation.product_locally_generated _ _ _ _ hPg hQg,
    OptimalRelaySeparation.product_relay_feasible _ _ _ _ hPf hQf,?_,?_⟩
  · rw [Profile.finrank_submodule_prod,hPd,hQd]
  · intro r
    rw [product_inducedRelay_entry]
    have hpr := add_le_add (hPprof r) (hQprof r)
    apply hpr.trans
    cases r with
    | inl r =>
      have hh : (BinaryAugmentedAllocation.resonantIncrement v r : ℝ)+
          (∑ t, (inc t (choose t) r : ℝ)) ≤ (c r : ℝ) := by exact_mod_cast hcap r
      have hb := hfirst r
      rw [Profile.entry_directSum] at hb
      simp only [firstIncrement]
      linarith
    | inr r =>
      simpa only [firstIncrement,Finset.sum_const_zero,add_zero,Profile.entry_directSum] using hsecond r

section ConcreteNonzero
variable {K I R : Type} [Field K] [Fintype I] [Fintype R]
    {F : I → Type} [∀ t, AddCommGroup (F t)] [∀ t, Module K (F t)]
    [∀ t, FiniteDimensional K (F t)]

/-- A concrete classified resonant/nonzero-defect relay theorem. Every
local menu is supplied by the proved original-field family construction. -/
theorem resonant_nonzero_relay (nR : R → ℕ) (T : (t : I) → Task K (F t))
    (hT : ∀ t, TaskDecomposition.Indecomposable (EdgeExtraction.configuration (T t)).spaces ⊤)
    (g : I → NonzeroFiniteAssembly.Kind) (n : I → ℕ) (hn : ∀ t, 1 ≤ n t)
    (hdims : ∀ t, NonzeroFamilyRanks.Dimensions (T t) (NonzeroFiniteAssembly.family (g t)) (n t))
    (c : Fin 6 → ℤ) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ p, (Fintype.card R : ℤ)+(∑ t, NonzeroFiniteAssembly.charge (g t) p) ≤
      c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p))
    (hplus : (Fintype.card R : ℤ) ≤ c 0+c 3+c 4)
    (hminus : (Fintype.card R : ℤ) ≤ c 1+c 2+c 5)
    (D : ℤ)
    (hfirst : ∀ j, Profile.entry
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) nR) (task T)) (.inl j)+(c j : ℝ) ≤ D)
    (hsecond : ∀ r : Three × Three, Profile.entry
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) nR) (task T)) (.inr r) ≤ D) :
    ∃ P : Submodule K (ResonantFiniteAssembly.Ambient (K := K) nR × (∀ t, F t)),
      ∃ hg : (Profile.directSum (ResonantFiniteAssembly.task (K := K) nR) (task T)).LocallyGenerated P,
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) nR) (task T)).RelayFeasible P ∧
      finrank K P = (∑ t, (3*(nR t+1)+1))+(∑ t, NonzeroFiniteAssembly.rank (g t) (n t)) ∧
      ∀ r, Profile.entry ((Profile.directSum (ResonantFiniteAssembly.task (K := K) nR) (task T)).inducedRelay P hg) r ≤ D :=
  resonant_charged_relay nR T (fun _ => Fin 6)
    (fun t => NonzeroFiniteAssembly.rank (g t) (n t))
    (fun t => NonzeroFiniteAssembly.menu (g t))
    (fun t => NonzeroFiniteAssembly.charge (g t))
    (fun t p => NonzeroFiniteAssembly.charge_nonneg (g t) p)
    (fun t => NonzeroFiniteAssembly.menu_fits (g t))
    (fun t => NonzeroFiniteAssembly.realizes_menu (T t) (hT t) (g t) (n t) (hn t) (hdims t))
    c hc hp hplus hminus (D : ℝ) hfirst hsecond

end ConcreteNonzero

end UploadBroadcast.AugmentedRelayAssembly
