import UploadBroadcast.BinaryMenuAllocation

/-! Integer allocation with the strengthened pair charges, after any cycle
repair. These are genuine integral menu selections; no fractional weights are
silently interpreted as scalar choices. -/
namespace UploadBroadcast.BinaryAugmentedAllocation
open scoped BigOperators
open BinaryMenuAllocation
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

/-- Reserve all three opposite pairs for arbitrary finite integer menus. -/
theorem integer_choice_aggregate {I : Type*} [Fintype I] (C : I → Type*)
    (inc : (t : I) → C t → Fin 6 → ℤ) (q : I → Fin 3 → ℤ)
    (hq : ∀ t p, 0 ≤ q t p)
    (hfit : ∀ t (c : Fin 6 → ℤ), (∀ j, 0 ≤ c j) →
      (∀ p, q t p ≤ c (pairLeft p)+c (pairRight p)) → ∃ k, ∀ j, inc t k j ≤ c j)
    (c : Fin 6 → ℤ) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ p, (∑ t, q t p) ≤ c (pairLeft p)+c (pairRight p)) :
    ∃ k : (t : I) → C t, ∀ j, (∑ t, inc t (k t) j) ≤ c j := by
  classical
  obtain ⟨x₀,y₀,hxy₀,hx₀,hy₀⟩ := Allocation.pair_reservations Finset.univ
    (fun t => q t 0) (c 0) (c 5) (hc 0) (hc 5) (fun t _ => hq t 0) (hp 0)
  obtain ⟨x₁,y₁,hxy₁,hx₁,hy₁⟩ := Allocation.pair_reservations Finset.univ
    (fun t => q t 1) (c 1) (c 3) (hc 1) (hc 3) (fun t _ => hq t 1) (hp 1)
  obtain ⟨x₂,y₂,hxy₂,hx₂,hy₂⟩ := Allocation.pair_reservations Finset.univ
    (fun t => q t 2) (c 2) (c 4) (hc 2) (hc 4) (fun t _ => hq t 2) (hp 2)
  let r : I → Fin 6 → ℤ := fun t => ![x₀ t,x₁ t,x₂ t,y₁ t,y₂ t,y₀ t]
  have hr (t : I) : ∀ j, 0 ≤ r t j := by
    have h₀ := hxy₀ t (Finset.mem_univ t)
    have h₁ := hxy₁ t (Finset.mem_univ t)
    have h₂ := hxy₂ t (Finset.mem_univ t)
    intro j; fin_cases j <;> simp [r] <;> omega
  have hp' (t : I) : ∀ p, q t p ≤ r t (pairLeft p)+r t (pairRight p) := by
    have h₀ := hxy₀ t (Finset.mem_univ t)
    have h₁ := hxy₁ t (Finset.mem_univ t)
    have h₂ := hxy₂ t (Finset.mem_univ t)
    intro p; fin_cases p <;> simp [r,pairLeft,pairRight] <;> omega
  choose k hk using fun t => hfit t (r t) (hr t) (hp' t)
  refine ⟨k,fun j => (Finset.sum_le_sum (fun t _ => hk t j)).trans ?_⟩
  fin_cases j <;> simp [r] <;> assumption

/-- Resonant consumption in the manuscript's original coordinate order. -/
def resonantIncrement (v : Fin 3 → ℤ) : Fin 6 → ℤ := ![v 0,v 1,v 0,v 2,v 1,v 2]

/-- Resonant choices are allocated first. Every leftover opposite pair
still pays all reserved menu charges, exactly as required after cycle repair. -/
theorem resonant_reserve_charges (m : ℤ) (q : Fin 3 → ℤ) (c : Fin 6 → ℤ)
    (hm : 0 ≤ m) (hq : ∀ p, 0 ≤ q p) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ p, m+q p ≤ c (pairLeft p)+c (pairRight p))
    (hplus : m ≤ c 0+c 3+c 4) (hminus : m ≤ c 1+c 2+c 5) :
    ∃ v : Fin 3 → ℤ, (∀ i, 0 ≤ v i) ∧ (∑ i, v i)=m ∧
      (∀ j, 0 ≤ c j-resonantIncrement v j) ∧
      ∀ p, q p ≤ (c (pairLeft p)-resonantIncrement v (pairLeft p))+
        (c (pairRight p)-resonantIncrement v (pairRight p)) := by
  have hp₀ : m+q 0 ≤ c 0+c 5 := hp 0
  have hp₁ : m+q 1 ≤ c 1+c 3 := hp 1
  have hp₂ : m+q 2 ≤ c 2+c 4 := hp 2
  obtain ⟨x,y,z,hx,hy,hz,hxc,hyc,hzc,he⟩ :=
    Allocation.resonant_allocation m (c 0) (c 3) (c 4) (c 5) (c 1) (c 2)
      hm (hc 0) (hc 3) (hc 4) (hc 5) (hc 1) (hc 2)
      (by linarith only [hp₀,hq 0]) (by linarith only [hp₁,hq 1])
      (by linarith only [hp₂,hq 2]) hplus (by linarith only [hminus])
  have hx0 := le_trans hxc (min_le_left _ _)
  have hx2 := le_trans hxc (min_le_right _ _)
  have hy4 := le_trans hyc (min_le_left _ _)
  have hy1 := le_trans hyc (min_le_right _ _)
  have hz3 := le_trans hzc (min_le_left _ _)
  have hz5 := le_trans hzc (min_le_right _ _)
  refine ⟨![x,y,z],?_,?_,?_,?_⟩
  · intro i; fin_cases i <;> simp <;> assumption
  · simpa [Fin.sum_univ_succ,add_assoc] using he
  · intro j; fin_cases j <;> simp [resonantIncrement] <;> omega
  · intro p; fin_cases p <;> simp [resonantIncrement,pairLeft,pairRight] <;> omega

/-- Full integer assembly of resonant weights and arbitrary charged scalar
menus. The two orientation constraints and strengthened pair constraints are
exactly the repaired constraints in `lem:binary-integer-relay`. -/
theorem augmented_integer_choices {I : Type*} [Fintype I] (C : I → Type*)
    (inc : (t : I) → C t → Fin 6 → ℤ) (q : I → Fin 3 → ℤ)
    (hq : ∀ t p, 0 ≤ q t p)
    (hfit : ∀ t (c : Fin 6 → ℤ), (∀ j, 0 ≤ c j) →
      (∀ p, q t p ≤ c (pairLeft p)+c (pairRight p)) → ∃ k, ∀ j, inc t k j ≤ c j)
    (m : ℤ) (c : Fin 6 → ℤ) (hm : 0 ≤ m) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ p, m+(∑ t, q t p) ≤ c (pairLeft p)+c (pairRight p))
    (hplus : m ≤ c 0+c 3+c 4) (hminus : m ≤ c 1+c 2+c 5) :
    ∃ v : Fin 3 → ℤ, ∃ k : (t : I) → C t,
      (∀ i, 0 ≤ v i) ∧ (∑ i, v i)=m ∧
      ∀ j, resonantIncrement v j+(∑ t, inc t (k t) j) ≤ c j := by
  obtain ⟨v,hv,hvm,hd,hdp⟩ := resonant_reserve_charges m (fun p => ∑ t, q t p) c
    hm (fun p => Finset.sum_nonneg (fun t _ => hq t p)) hc hp hplus hminus
  obtain ⟨k,hk⟩ := integer_choice_aggregate C inc q hq hfit
    (fun j => c j-resonantIncrement v j) hd hdp
  refine ⟨v,k,hv,hvm,fun j => ?_⟩
  have hh := hk j
  omega

end UploadBroadcast.BinaryAugmentedAllocation
