import UploadBroadcast.AugmentedRelayAssembly
import UploadBroadcast.OrientationRepairAllocation

namespace UploadBroadcast.RepairedGlobalMenuAssembly
open Module FiniteRelayAssembly GlobalMenuAssembly OrientationRepairAllocation
open scoped BigOperators
variable {K I R H : Type*} {F : I → Type*} {G : H → Type*}
  [Field K] [Fintype I] [Fintype R] [Fintype H]
  [∀ t, AddCommGroup (F t)] [∀ t, Module K (F t)] [∀ t, FiniteDimensional K (F t)]
  [∀ h, AddCommGroup (G h)] [∀ h, Module K (G h)] [∀ h, FiniteDimensional K (G h)]

/-- End-to-end geometric packing after an actual component partition and
physical cycle pairing. Integer repair counts are derived from the original
slacks, all remaining menu choices are constructed, and fixed actual repairs
are assembled. No selected global relay or final profile bound is an input. -/
theorem construct_repaired_relay (n : R → ℕ) (T : (t : I) → Task K (F t))
    (S : (h : H) → Task K (G h)) (C : I → Type*)
    (d : I → ℕ) (e : H → ℕ) (inc : (t : I) → C t → Fin 6 → ℤ)
    (q : I → Fin 3 → ℤ) (hq : ∀ t p, 0 ≤ q t p)
    (hfit : ∀ t (c : Fin 6 → ℤ), (∀ j, 0 ≤ c j) →
      (∀ p, q t p ≤ c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p)) →
      ∃ k, ∀ j, inc t k j ≤ c j)
    (hmenu : ∀ t, RealizesMenu (T t) (d t) (fun k => firstIncrement (inc t k)))
    (delta : H → Profile.Index → ℝ)
    (hfixed : ∀ h, RealizesMenu (S h) (e h) (fun (_ : Unit) => delta h))
    (m : ℤ) (hm : 0 ≤ m) (c : Fin 6 → ℤ) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ p, m+(∑ t, q t p) ≤ c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p))
    (hcount : (Fintype.card R : ℤ)=m-positiveCount m c-negativeCount m c)
    (hdelta_first : ∀ j, (∑ h, delta h (.inl j)) =
      (if j=1 then (positiveCount m c : ℝ) else 0)+
      (if j=3 then (negativeCount m c : ℝ) else 0))
    (hdelta_second : ∀ r : Three × Three, (∑ h, delta h (.inr r))=0)
    (D : ℝ)
    (hfirst : ∀ j, Profile.entry (Profile.directSum
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) (task S))
      (.inl j)+(c j : ℝ) ≤ D)
    (hsecond : ∀ r : Three × Three, Profile.entry (Profile.directSum
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) (task S)) (.inr r) ≤ D) :
    ∃ P : Submodule K ((ResonantFiniteAssembly.Ambient (K := K) n × (∀ t, F t)) × (∀ h, G h)),
      ∃ hg : (Profile.directSum
        (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) (task S)).LocallyGenerated P,
      (Profile.directSum (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) (task S)).RelayFeasible P ∧
      finrank K P = ((∑ r, (3*(n r+1)+1))+(∑ t, d t))+(∑ h, e h) ∧
      ∀ r, Profile.entry ((Profile.directSum
        (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) (task S)).inducedRelay P hg) r ≤ D := by
  have hqsum (p : Fin 3) : 0 ≤ ∑ t, q t p := Finset.sum_nonneg fun t _ => hq t p
  obtain ⟨_,_,_,_,hcap,hpair,hplus,hminus⟩ := repaired_capacities m (fun p => ∑ t, q t p) c
    hm hqsum hc hp (sum_capacity m (fun p => ∑ t, q t p) c hqsum hp)
  have hp' (p : Fin 3) : (Fintype.card R : ℤ)+(∑ t, q t p) ≤
      repaired m c (BinaryMenuAllocation.pairLeft p)+repaired m c (BinaryMenuAllocation.pairRight p) := by
    rw [hcount]
    exact hpair p
  have hplus' : (Fintype.card R : ℤ) ≤ plus (repaired m c) := hcount.trans_le hplus
  have hminus' : (Fintype.card R : ℤ) ≤ minus (repaired m c) := hcount.trans_le hminus
  have hreservation (j : Fin 6) : (repaired m c j : ℝ)+(∑ h, delta h (.inl j))=(c j : ℝ) := by
    rw [hdelta_first]
    have hh := repaired_add_reserved m c j
    have hc' : (repaired m c j : ℝ)+(if j=1 then (positiveCount m c : ℝ) else 0)+
      (if j=3 then (negativeCount m c : ℝ) else 0)=(c j : ℝ) := by exact_mod_cast hh
    linarith only [hc']
  obtain ⟨P,hPl,hPf,hPd,hPprof⟩ := AugmentedRelayAssembly.resonant_charged_relay_budget
    n T C d inc q hq hfit hmenu (repaired m c) hcap hp' hplus' hminus'
    (fun r => D-Profile.entry (task S) r-(∑ h, delta h r))
    (by
      intro j
      have hb := hfirst j
      rw [Profile.entry_directSum] at hb
      have hr := hreservation j
      dsimp only
      linarith only [hb,hr])
    (by
      intro r
      have hb := hsecond r
      rw [Profile.entry_directSum] at hb
      have hr := hdelta_second r
      dsimp only
      linarith only [hb,hr])
  obtain ⟨Q,hQl,hQf,hQd,hQprof⟩ := assemble_choices S (fun _ => Unit) e
    (fun h _ => delta h) hfixed (fun _ => ())
    (fun r => Profile.entry (task S) r+(∑ h, delta h r)) (fun _ => le_rfl)
  refine ⟨P.prod Q,OptimalRelaySeparation.product_locally_generated _ _ _ _ hPl hQl,
    OptimalRelaySeparation.product_relay_feasible _ _ _ _ hPf hQf,?_,?_⟩
  · rw [Profile.finrank_submodule_prod,hPd,hQd]
  · intro r
    rw [product_inducedRelay_entry]
    have hh := add_le_add (hPprof r) (hQprof r)
    linarith only [hh]

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The fixed-block version matches the physical pairing chart directly:
the block may itself be a product of repaired pairs and a zero-excess remainder. -/
theorem construct_repaired_relay_block (n : R → ℕ) (T : (t : I) → Task K (F t))
    (S : Task K V) (C : I → Type*)
    (d : I → ℕ) (e : ℕ) (inc : (t : I) → C t → Fin 6 → ℤ)
    (q : I → Fin 3 → ℤ) (hq : ∀ t p, 0 ≤ q t p)
    (hfit : ∀ t (c : Fin 6 → ℤ), (∀ j, 0 ≤ c j) →
      (∀ p, q t p ≤ c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p)) →
      ∃ k, ∀ j, inc t k j ≤ c j)
    (hmenu : ∀ t, RealizesMenu (T t) (d t) (fun k => firstIncrement (inc t k)))
    (delta : Profile.Index → ℝ)
    (hfixed : RealizesMenu S e (fun (_ : Unit) => delta))
    (m : ℤ) (hm : 0 ≤ m) (c : Fin 6 → ℤ) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ p, m+(∑ t, q t p) ≤ c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p))
    (hcount : (Fintype.card R : ℤ)=m-positiveCount m c-negativeCount m c)
    (hdelta_first : ∀ j, delta (.inl j) =
      (if j=1 then (positiveCount m c : ℝ) else 0)+
      (if j=3 then (negativeCount m c : ℝ) else 0))
    (hdelta_second : ∀ r : Three × Three, delta (.inr r)=0)
    (D : ℝ)
    (hfirst : ∀ j, Profile.entry (Profile.directSum
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) S)
      (.inl j)+(c j : ℝ) ≤ D)
    (hsecond : ∀ r : Three × Three, Profile.entry (Profile.directSum
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) S) (.inr r) ≤ D) :
    ∃ P : Submodule K ((ResonantFiniteAssembly.Ambient (K := K) n × (∀ t, F t)) × V),
      ∃ hg : (Profile.directSum
        (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) S).LocallyGenerated P,
      (Profile.directSum (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) S).RelayFeasible P ∧
      finrank K P = ((∑ r, (3*(n r+1)+1))+(∑ t, d t))+e ∧
      ∀ r, Profile.entry ((Profile.directSum
        (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) S).inducedRelay P hg) r ≤ D := by
  have hqsum (p : Fin 3) : 0 ≤ ∑ t, q t p := Finset.sum_nonneg fun t _ => hq t p
  obtain ⟨_,_,_,_,hcap,hpair,hplus,hminus⟩ := repaired_capacities m (fun p => ∑ t, q t p) c
    hm hqsum hc hp (sum_capacity m (fun p => ∑ t, q t p) c hqsum hp)
  have hp' (p : Fin 3) : (Fintype.card R : ℤ)+(∑ t, q t p) ≤
      repaired m c (BinaryMenuAllocation.pairLeft p)+repaired m c (BinaryMenuAllocation.pairRight p) := by
    rw [hcount]
    exact hpair p
  have hplus' : (Fintype.card R : ℤ) ≤ plus (repaired m c) := hcount.trans_le hplus
  have hminus' : (Fintype.card R : ℤ) ≤ minus (repaired m c) := hcount.trans_le hminus
  have hreservation (j : Fin 6) : (repaired m c j : ℝ)+delta (.inl j)=(c j : ℝ) := by
    rw [hdelta_first]
    have hh := repaired_add_reserved m c j
    have hc' : (repaired m c j : ℝ)+(if j=1 then (positiveCount m c : ℝ) else 0)+
      (if j=3 then (negativeCount m c : ℝ) else 0)=(c j : ℝ) := by exact_mod_cast hh
    linarith only [hc']
  obtain ⟨P,hPl,hPf,hPd,hPprof⟩ := AugmentedRelayAssembly.resonant_charged_relay_budget
    n T C d inc q hq hfit hmenu (repaired m c) hcap hp' hplus' hminus'
    (fun r => D-Profile.entry S r-delta r)
    (by
      intro j
      have hb := hfirst j
      rw [Profile.entry_directSum] at hb
      have hr := hreservation j
      dsimp only
      linarith only [hb,hr])
    (by
      intro r
      have hb := hsecond r
      rw [Profile.entry_directSum] at hb
      have hr := hdelta_second r
      dsimp only
      linarith only [hb,hr])
  obtain ⟨Q,hQl,hQf,hQd,hQprof⟩ := hfixed ()
  refine ⟨P.prod Q,OptimalRelaySeparation.product_locally_generated _ _ _ _ hPl hQl,
    OptimalRelaySeparation.product_relay_feasible _ _ _ _ hPf hQf,?_,?_⟩
  · rw [Profile.finrank_submodule_prod,hPd,hQd]
  · intro r
    rw [product_inducedRelay_entry]
    have hh := add_le_add (hPprof r) (hQprof r)
    linarith only [hh]

/-- Profile-budget form keeps the untouched Ω profile outside residual relay
selection, preserving the factorization needed for binary separation. -/
theorem construct_repaired_relay_profile_budget (n : R → ℕ) (T : (t : I) → Task K (F t))
    (S : Task K V) (C : I → Type*)
    (d : I → ℕ) (e : ℕ) (inc : (t : I) → C t → Fin 6 → ℤ)
    (q : I → Fin 3 → ℤ) (hq : ∀ t p, 0 ≤ q t p)
    (hfit : ∀ t (c : Fin 6 → ℤ), (∀ j, 0 ≤ c j) →
      (∀ p, q t p ≤ c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p)) →
      ∃ k, ∀ j, inc t k j ≤ c j)
    (hmenu : ∀ t, RealizesMenu (T t) (d t) (fun k => firstIncrement (inc t k)))
    (delta : Profile.Index → ℝ)
    (hfixed : RealizesMenu S e (fun (_ : Unit) => delta))
    (m : ℤ) (hm : 0 ≤ m) (c : Fin 6 → ℤ) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ p, m+(∑ t, q t p) ≤ c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p))
    (hcount : (Fintype.card R : ℤ)=m-positiveCount m c-negativeCount m c)
    (hdelta_first : ∀ j, delta (.inl j) =
      (if j=1 then (positiveCount m c : ℝ) else 0)+
      (if j=3 then (negativeCount m c : ℝ) else 0))
    (hdelta_second : ∀ r : Three × Three, delta (.inr r)=0)
    (budget : Profile.Index → ℝ)
    (hfirst : ∀ j, Profile.entry (Profile.directSum
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) S)
      (.inl j)+(c j : ℝ) ≤ budget (.inl j))
    (hsecond : ∀ r : Three × Three, Profile.entry (Profile.directSum
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) S) (.inr r) ≤ budget (.inr r)) :
    ∃ P : Submodule K ((ResonantFiniteAssembly.Ambient (K := K) n × (∀ t, F t)) × V),
      ∃ hg : (Profile.directSum
        (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) S).LocallyGenerated P,
      (Profile.directSum (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) S).RelayFeasible P ∧
      finrank K P = ((∑ r, (3*(n r+1)+1))+(∑ t, d t))+e ∧
      ∀ r, Profile.entry ((Profile.directSum
        (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (task T)) S).inducedRelay P hg) r ≤ budget r := by
  have hqsum (p : Fin 3) : 0 ≤ ∑ t, q t p := Finset.sum_nonneg fun t _ => hq t p
  obtain ⟨_,_,_,_,hcap,hpair,hplus,hminus⟩ := repaired_capacities m (fun p => ∑ t, q t p) c
    hm hqsum hc hp (sum_capacity m (fun p => ∑ t, q t p) c hqsum hp)
  have hp' (p : Fin 3) : (Fintype.card R : ℤ)+(∑ t, q t p) ≤
      repaired m c (BinaryMenuAllocation.pairLeft p)+repaired m c (BinaryMenuAllocation.pairRight p) := by
    rw [hcount]
    exact hpair p
  have hplus' : (Fintype.card R : ℤ) ≤ plus (repaired m c) := hcount.trans_le hplus
  have hminus' : (Fintype.card R : ℤ) ≤ minus (repaired m c) := hcount.trans_le hminus
  have hreservation (j : Fin 6) : (repaired m c j : ℝ)+delta (.inl j)=(c j : ℝ) := by
    rw [hdelta_first]
    have hh := repaired_add_reserved m c j
    have hc' : (repaired m c j : ℝ)+(if j=1 then (positiveCount m c : ℝ) else 0)+
      (if j=3 then (negativeCount m c : ℝ) else 0)=(c j : ℝ) := by exact_mod_cast hh
    linarith only [hc']
  obtain ⟨P,hPl,hPf,hPd,hPprof⟩ := AugmentedRelayAssembly.resonant_charged_relay_budget
    n T C d inc q hq hfit hmenu (repaired m c) hcap hp' hplus' hminus'
    (fun r => budget r-Profile.entry S r-delta r)
    (by
      intro j
      have hb := hfirst j
      rw [Profile.entry_directSum] at hb
      have hr := hreservation j
      dsimp only
      linarith only [hb,hr])
    (by
      intro r
      have hb := hsecond r
      rw [Profile.entry_directSum] at hb
      have hr := hdelta_second r
      dsimp only
      linarith only [hb,hr])
  obtain ⟨Q,hQl,hQf,hQd,hQprof⟩ := hfixed ()
  refine ⟨P.prod Q,OptimalRelaySeparation.product_locally_generated _ _ _ _ hPl hQl,
    OptimalRelaySeparation.product_relay_feasible _ _ _ _ hPf hQf,?_,?_⟩
  · rw [Profile.finrank_submodule_prod,hPd,hQd]
  · intro r
    rw [product_inducedRelay_entry]
    have hh := add_le_add (hPprof r) (hQprof r)
    linarith only [hh]

end UploadBroadcast.RepairedGlobalMenuAssembly
