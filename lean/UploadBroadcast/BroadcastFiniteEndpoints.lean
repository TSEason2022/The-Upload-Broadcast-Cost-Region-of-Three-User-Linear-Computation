import UploadBroadcast.ScalarPaperEndpoints

/-! Unconditional finite-block endpoints for the fully informed problem.
These do not assert simultaneous minimum-upload coding. In the unrestricted
binary branch the already constructed extension code is restricted to four
original-field source instances, with its actual finite alphabet retained. -/
namespace UploadBroadcast
variable {K F : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Over q≥3, an integral operational fully informed optimum is attained
at one original-field instance and otherwise at two. The exact finite
alphabet cost survives the canonical alphabet relabeling. -/
theorem fullyInformed_one_or_two (A U : Three → Submodule K F)
    (hAU : ∀ i, A i ≤ U i) (hq : 3 ≤ Nat.card K) :
    ∃ L n, ∃ c : BlockBroadcastCode A U L (Fin n),
      (L = 1 ∨ L = 2) ∧
      ((∃ z : ℤ, broadcastOptimum A U = z) ↔ L = 1) ∧
      c.cost = broadcastOptimum A U := by
  classical
  by_cases hi : ∃ z : ℤ, broadcastOptimum A U = z
  · obtain ⟨z,hz⟩ := hi
    obtain ⟨b,c,hn,hc⟩ := scalar_at_operational_ceiling A U hAU hq
    have hnz : (b : ℤ) = z := by simpa only [hz,Int.ceil_intCast] using hn
    have hbr : (b : ℝ) = broadcastOptimum A U := by
      rw [hz]
      exact_mod_cast hnz
    obtain ⟨n,d,hd⟩ := c.toBlockOne.finite_relabel
    refine ⟨1,n,d,Or.inl rfl,⟨fun _ => rfl,fun _ => ⟨z,hz⟩⟩,?_⟩
    rw [hd,c.toBlockOne_cost,hc,hbr]
  · obtain ⟨b,c,hc⟩ := block_profile_exact A U hAU hq
    obtain ⟨n,d,hd⟩ := c.finite_relabel
    refine ⟨2,n,d,Or.inr rfl,?_,?_⟩
    · simp only [hi,false_iff]
      decide
    · rw [hd,hc,general_broadcastOptimum_eq_rankBound A U hAU]

/-- Fully informed operational attainment with an explicit member of
{1,2,4}; positivity and the field-dependent bounds are part of the result.
This is not the source's upload--broadcast joint L≤2 theorem. -/
theorem fullyInformed_one_two_or_four (A U : Three → Submodule K F)
    (hAU : ∀ i, A i ≤ U i) :
    ∃ L n, ∃ c : BlockBroadcastCode A U L (Fin n),
      (L = 1 ∨ L = 2 ∨ L = 4) ∧ 0 < L ∧
      (3 ≤ Nat.card K → L ≤ 2) ∧ c.cost = broadcastOptimum A U := by
  by_cases hq : 3 ≤ Nat.card K
  · obtain ⟨L,n,c,hL,_,hc⟩ := fullyInformed_one_or_two A U hAU hq
    refine ⟨L,n,c,?_,?_,?_,hc⟩
    · rcases hL with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases hL with rfl | rfl <;> decide
    · intro _
      rcases hL with rfl | rfl <;> decide
  · letI := Fintype.ofFinite K
    have htwo : Fintype.card K = 2 := by
      have h := Finite.one_lt_card (α := K)
      rw [Nat.card_eq_fintype_card] at h hq
      omega
    obtain ⟨b,c,hc⟩ := card_two_general_block_profile_exact htwo A U hAU
    obtain ⟨n,d,hd⟩ := c.finite_relabel
    refine ⟨4,n,d,Or.inr (Or.inr rfl),by decide,fun h => False.elim (hq h),?_⟩
    rw [hd,hc,general_broadcastOptimum_eq_rankBound A U hAU]

end UploadBroadcast
