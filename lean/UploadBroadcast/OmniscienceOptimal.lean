import UploadBroadcast.OmniscienceCode
import UploadBroadcast.AllocationOmniscience
import Mathlib.FieldTheory.Finiteness

/-! Exact attainable-alphabet costs and original-field one/two-instance
optimality for the omniscience component. -/
namespace UploadBroadcast.Omniscience

variable {K V X₁ X₂ X₃ : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup X₁] [Module K X₁]
  [AddCommGroup X₂] [Module K X₂]
  [AddCommGroup X₃] [Module K X₃]
  [FiniteDimensional K V] [FiniteDimensional K X₁]
  [FiniteDimensional K X₂] [FiniteDimensional K X₃]

/-- The numerical optimum with the three actual missing dimensions. -/
noncomputable def optimum : ℝ := Allocation.omniscienceValue
  (Module.finrank K V + Module.finrank K X₁)
  (Module.finrank K V + Module.finrank K X₂)
  (Module.finrank K V + Module.finrank K X₃)

namespace Code
variable {r₁ r₂ r₃ : ℕ}

/-- Total rank of the three attained linear upload alphabets. -/
noncomputable def totalRank (c : Code K V X₁ X₂ X₃ r₁ r₂ r₃) : ℕ :=
  Module.finrank K (LinearMap.range c.encode₁) +
  Module.finrank K (LinearMap.range c.encode₂) +
  Module.finrank K (LinearMap.range c.encode₃)

/-- Attainable-alphabet communication cost, in q-ary units for this block. -/
noncomputable def alphabetCost [Finite K] (c : Code K V X₁ X₂ X₃ r₁ r₂ r₃) : ℝ :=
  Real.logb (Nat.card K) (Nat.card (Set.range c.encode₁)) +
  Real.logb (Nat.card K) (Nat.card (Set.range c.encode₂)) +
  Real.logb (Nat.card K) (Nat.card (Set.range c.encode₃))

omit [FiniteDimensional K V] [FiniteDimensional K X₁]
  [FiniteDimensional K X₂] [FiniteDimensional K X₃] in
/-- Padded output positions do not count as attainable upload symbols. -/
theorem totalRank_le (c : Code K V X₁ X₂ X₃ r₁ r₂ r₃) : c.totalRank ≤ r₁+r₂+r₃ := by
  have h₁ := (LinearMap.range c.encode₁).finrank_le
  have h₂ := (LinearMap.range c.encode₂).finrank_le
  have h₃ := (LinearMap.range c.encode₃).finrank_le
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h₁ h₂ h₃
  unfold totalRank
  omega

/-- Converse stated for the true attained ranks, not the output capacities. -/
theorem optimum_le_totalRank (c : Code K V X₁ X₂ X₃ r₁ r₂ r₃) :
    optimum (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) ≤ c.totalRank := by
  obtain ⟨h₁,h₂,h₃⟩ := c.rank_deficits
  have hf : Allocation.OmniscienceFeasible
      (Module.finrank K V + Module.finrank K X₁)
      (Module.finrank K V + Module.finrank K X₂)
      (Module.finrank K V + Module.finrank K X₃)
      (Module.finrank K (LinearMap.range c.encode₁))
      (Module.finrank K (LinearMap.range c.encode₂))
      (Module.finrank K (LinearMap.range c.encode₃)) := by
    refine ⟨by positivity, by positivity, by positivity, ?_, ?_, ?_⟩
    · exact_mod_cast h₁
    · exact_mod_cast h₂
    · exact_mod_cast h₃
  simpa only [optimum, totalRank, Nat.cast_add] using Allocation.omniscience_lower_bound hf

end Code

section Alphabet
variable {E H : Type*} [AddCommGroup E] [Module K E]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H] [Finite K]

/-- Finite-field cardinality/rank dictionary for any linear upload. -/
theorem log_card_range (f : E →ₗ[K] H) :
    Real.logb (Nat.card K) (Nat.card (Set.range f)) =
      Module.finrank K (LinearMap.range f) := by
  have hc := Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.range f)
  change Real.logb (Nat.card K) (Nat.card (LinearMap.range f)) = _
  rw [hc, Nat.cast_pow, Real.logb_pow, Real.logb_self_eq_one, mul_one]
  letI := Fintype.ofFinite K
  have hk : 1 < Nat.card K := by
    simpa only [Nat.card_eq_fintype_card] using (Fintype.one_lt_card : 1 < Fintype.card K)
  exact_mod_cast hk

end Alphabet

namespace Code
variable {r₁ r₂ r₃ : ℕ} [Finite K]

omit [FiniteDimensional K V] [FiniteDimensional K X₁]
  [FiniteDimensional K X₂] [FiniteDimensional K X₃] in
theorem alphabetCost_eq_totalRank (c : Code K V X₁ X₂ X₃ r₁ r₂ r₃) :
    c.alphabetCost = c.totalRank := by
  simp only [alphabetCost, totalRank, log_card_range, Nat.cast_add]

theorem optimum_le_alphabetCost (c : Code K V X₁ X₂ X₃ r₁ r₂ r₃) :
    optimum (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) ≤ c.alphabetCost := by
  rw [c.alphabetCost_eq_totalRank]
  exact c.optimum_le_totalRank

end Code

/-- If the optimum is integral, it is attained by a one-instance code.
The equality charges the attained alphabets, not padded message vectors. -/
theorem exists_scalar_optimal [Finite K] (n : ℕ)
    (hn : (n : ℝ) = optimum (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)) :
    ∃ (r₁ r₂ r₃ : ℕ) (c : Code K V X₁ X₂ X₃ r₁ r₂ r₃),
      c.alphabetCost = optimum (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) := by
  obtain ⟨r₁,r₂,r₃,hf,he⟩ := Allocation.omniscience_integral_optimizer_nat
    (Module.finrank K V + Module.finrank K X₁)
    (Module.finrank K V + Module.finrank K X₂)
    (Module.finrank K V + Module.finrank K X₃) n (by simpa only [optimum, Nat.cast_add] using hn)
  obtain ⟨c⟩ := exists_code (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)
    r₁ r₂ r₃ (by exact_mod_cast hf.2.2.2.1) (by exact_mod_cast hf.2.2.2.2.1)
      (by exact_mod_cast hf.2.2.2.2.2)
  refine ⟨r₁,r₂,r₃,c,le_antisymm ?_ c.optimum_le_alphabetCost⟩
  rw [c.alphabetCost_eq_totalRank]
  have hc : (c.totalRank : ℝ) ≤ (r₁ : ℝ)+r₂+r₃ := by exact_mod_cast c.totalRank_le
  exact hc.trans_eq (by simpa only [optimum, Nat.cast_add] using he)

/-- Doubling all coordinate blocks doubles the numerical optimum. -/
theorem optimum_prod_self :
    optimum (K := K) (V := V × V) (X₁ := X₁ × X₁) (X₂ := X₂ × X₂) (X₃ := X₃ × X₃) =
      2 * optimum (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) := by
  unfold optimum Allocation.omniscienceValue
  simp only [Module.finrank_prod, Nat.cast_add,
    mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  congr 2 <;> ring

/-- Every omniscience component has an optimal two-instance linear upload
code over the original field. Product coordinate blocks group the two
instances; the normalized alphabet cost is divided by two. -/
theorem exists_two_instance_optimal [Finite K] :
    ∃ (r₁ r₂ r₃ : ℕ)
      (c : Code K (V × V) (X₁ × X₁) (X₂ × X₂) (X₃ × X₃) r₁ r₂ r₃),
      c.alphabetCost / 2 = optimum (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) := by
  obtain ⟨r₁,r₂,r₃,hf,he⟩ := Allocation.omniscience_half_integral_nat
    (Module.finrank K V + Module.finrank K X₁)
    (Module.finrank K V + Module.finrank K X₂)
    (Module.finrank K V + Module.finrank K X₃)
  have hn₁ : 2 * (Module.finrank K V + Module.finrank K X₁) ≤ r₂+r₃ := by
    have h : 2 * ((Module.finrank K V + Module.finrank K X₁ : ℕ) : ℝ) ≤
        (r₂ : ℝ)+r₃ := by linarith [hf.2.2.2.1]
    exact_mod_cast h
  have hn₂ : 2 * (Module.finrank K V + Module.finrank K X₂) ≤ r₁+r₃ := by
    have h : 2 * ((Module.finrank K V + Module.finrank K X₂ : ℕ) : ℝ) ≤
        (r₁ : ℝ)+r₃ := by linarith [hf.2.2.2.2.1]
    exact_mod_cast h
  have hn₃ : 2 * (Module.finrank K V + Module.finrank K X₃) ≤ r₁+r₂ := by
    have h : 2 * ((Module.finrank K V + Module.finrank K X₃ : ℕ) : ℝ) ≤
        (r₁ : ℝ)+r₂ := by linarith [hf.2.2.2.2.2]
    exact_mod_cast h
  obtain ⟨c⟩ := exists_code (K := K) (V := V × V)
    (X₁ := X₁ × X₁) (X₂ := X₂ × X₂) (X₃ := X₃ × X₃) r₁ r₂ r₃
    (by simp only [Module.finrank_prod]; omega)
    (by simp only [Module.finrank_prod]; omega)
    (by simp only [Module.finrank_prod]; omega)
  refine ⟨r₁,r₂,r₃,c,?_⟩
  have hl := c.optimum_le_alphabetCost
  rw [optimum_prod_self] at hl
  have hu : c.alphabetCost ≤ (r₁ : ℝ)+r₂+r₃ := by
    rw [c.alphabetCost_eq_totalRank]
    exact_mod_cast c.totalRank_le
  have he' : (r₁ : ℝ)/2 + (r₂ : ℝ)/2 + (r₃ : ℝ)/2 =
      optimum (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) := by
    simpa only [optimum, Nat.cast_add] using he
  linarith

/-- The LP value is positively homogeneous. -/
theorem value_scale (t a b c : ℝ) (ht : 0 ≤ t) :
    Allocation.omniscienceValue (t*a) (t*b) (t*c) =
      t * Allocation.omniscienceValue a b c := by
  unfold Allocation.omniscienceValue
  simp only [mul_max_of_nonneg _ _ ht]
  congr 2; ring

/-- Coordinate blocks for L instances multiply the optimum by L. -/
theorem optimum_block (L : ℕ) :
    optimum (K := K) (V := Fin L → V) (X₁ := Fin L → X₁)
      (X₂ := Fin L → X₂) (X₃ := Fin L → X₃) =
      L * optimum (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) := by
  unfold optimum
  simpa [Module.finrank_pi_fintype, Nat.cast_mul, mul_add] using
    value_scale (L : ℝ)
      (Module.finrank K V + Module.finrank K X₁)
      (Module.finrank K V + Module.finrank K X₂)
      (Module.finrank K V + Module.finrank K X₃) (by positivity)

/-- The attained-alphabet lower bound holds at every positive blocklength,
not only for scalar uploads. -/
theorem block_cost_lower [Finite K] (L : ℕ) (hL : 0 < L) {r₁ r₂ r₃ : ℕ}
    (c : Code K (Fin L → V) (Fin L → X₁) (Fin L → X₂) (Fin L → X₃) r₁ r₂ r₃) :
    optimum (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) ≤ c.alphabetCost / L := by
  have h := c.optimum_le_alphabetCost
  rw [optimum_block] at h
  apply (le_div_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)).mpr
  simpa only [mul_comm] using h

omit [FiniteDimensional K V] [FiniteDimensional K X₁]
  [FiniteDimensional K X₂] [FiniteDimensional K X₃] in
/-- A nonintegral optimum cannot be attained by a scalar linear code,
since each finite-field linear image has integral q-ary logarithmic size. -/
theorem no_scalar_optimum_of_nonintegral [Finite K]
    (h : ∀ n : ℕ, (n : ℝ) ≠ optimum (K := K) (V := V)
      (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)) :
    ¬ ∃ (r₁ r₂ r₃ : ℕ) (c : Code K V X₁ X₂ X₃ r₁ r₂ r₃),
      c.alphabetCost = optimum (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) := by
  rintro ⟨r₁,r₂,r₃,c,hc⟩
  exact h c.totalRank (c.alphabetCost_eq_totalRank.symm.trans hc)

end UploadBroadcast.Omniscience
