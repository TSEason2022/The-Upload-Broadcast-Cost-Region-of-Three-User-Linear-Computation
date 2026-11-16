import UploadBroadcast.BlockBroadcast
import UploadBroadcast.ScalarEndpoints
import UploadBroadcast.RawProfileScaling
import UploadBroadcast.BinaryFieldTransport
import UploadBroadcast.RawBroadcastConverse

namespace UploadBroadcast
variable {K F : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Costs of actual positive-blocklength, finite-alphabet fully informed codes.
Using `Fin n` loses no generality, by `BlockBroadcastCode.finite_relabel`. -/
def broadcastCosts (A U : Three → Submodule K F) : Set ℝ :=
  {r | ∃ L n, ∃ c : BlockBroadcastCode A U L (Fin n), 0 < L ∧ c.cost = r}

/-- The operational optimum over all nonlinear zero-error finite-alphabet block codes. -/
noncomputable def broadcastOptimum (A U : Three → Submodule K F) : ℝ :=
  sInf (broadcastCosts A U)

omit [Finite K] [FiniteDimensional K F] in
theorem BlockBroadcastCode.cost_mem {A U : Three → Submodule K F}
    {L : ℕ} {S : Type*} [Finite S] (c : BlockBroadcastCode A U L S) (hL : 0 < L) :
    c.cost ∈ broadcastCosts A U := by
  obtain ⟨n,d,hd⟩ := c.finite_relabel
  exact ⟨L,n,d,hL,hd⟩

omit [Finite K] in
theorem double_length_eq {A U : Three → Submodule K F} {n : ℕ}
    (hn : (n : ℤ) = ⌈Allocation.rawRankBound (fun i => (A i).prod (A i))
      (fun i => (U i).prod (U i))⌉) :
    (n : ℝ) / 2 = Allocation.rawRankBound A U := by
  obtain ⟨z,hz⟩ := Allocation.rawRankBound_halfInteger A U
  rw [Allocation.rawRankBound_double, hz] at hn
  have he : 2 * ((z : ℝ) / 2) = z := by ring
  rw [he, Int.ceil_intCast] at hn
  have hc : (n : ℝ) = z := by exact_mod_cast hn
  rw [hc,hz]

/-- An actual length-two code attains the converse bound over every field with q ≥ 3. -/
theorem block_profile_achievability
    (A U : Three → Submodule K F) (hAU : ∀ i, A i ≤ U i) (hq : 3 ≤ Nat.card K) :
    ∃ n, ∃ c : BlockBroadcastCode A U 2 (Fin n → K),
      c.cost ≤ Allocation.rawRankBound A U := by
  obtain ⟨n,hn,⟨c⟩⟩ := scalar_profile_achievability
    (fun i => (A i).prod (A i)) (fun i => (U i).prod (U i))
    (fun i => Submodule.prod_mono (hAU i) (hAU i)) hq
  exact ⟨n,c.toBlockDouble, (c.toBlockDouble_cost_le).trans_eq (double_length_eq hn)⟩

theorem BlockBroadcastCode.rankBound_le_cost {A U : Three → Submodule K F}
    {L : ℕ} {S : Type*} [Finite S] (c : BlockBroadcastCode A U L S)
    (hAU : ∀ i, A i ≤ U i) (hL : 0 < L) :
    Allocation.rawRankBound A U ≤ c.cost := by
  letI : MeasurableSpace S := ⊤
  letI : DiscreteMeasurableSpace S := ⟨fun _ => trivial⟩
  exact BroadcastOperational.rawRankBound_le_cost hL c.encode A U hAU c.decode c.zero_error

/-- Operational equality follows from an actual attaining code and the universal converse. -/
theorem broadcastOptimum_eq_of_code (A U : Three → Submodule K F)
    (hAU : ∀ i, A i ≤ U i) {L : ℕ} {S : Type*} [Finite S]
    (c : BlockBroadcastCode A U L S) (hL : 0 < L)
    (hc : c.cost ≤ Allocation.rawRankBound A U) :
    broadcastOptimum A U = Allocation.rawRankBound A U := by
  have hl : ∀ r ∈ broadcastCosts A U, Allocation.rawRankBound A U ≤ r := by
    rintro r ⟨L,n,d,hL,rfl⟩
    exact d.rankBound_le_cost hAU hL
  have hm := c.cost_mem hL
  apply le_antisymm
  · exact (csInf_le ⟨Allocation.rawRankBound A U,hl⟩ hm).trans hc
  · exact le_csInf ⟨c.cost,hm⟩ hl

/-- Exact fully informed LCBC optimum for arbitrary side-information subspaces
on every finite field of at least three elements. -/
theorem broadcastOptimum_eq_rankBound
    (A U : Three → Submodule K F) (hAU : ∀ i, A i ≤ U i) (hq : 3 ≤ Nat.card K) :
    broadcastOptimum A U = Allocation.rawRankBound A U := by
  obtain ⟨n,c,hc⟩ := block_profile_achievability A U hAU hq
  exact broadcastOptimum_eq_of_code A U hAU c (by norm_num) hc

/-- The infimum is attained already at blocklength two. -/
theorem block_profile_exact
    (A U : Three → Submodule K F) (hAU : ∀ i, A i ≤ U i) (hq : 3 ≤ Nat.card K) :
    ∃ n, ∃ c : BlockBroadcastCode A U 2 (Fin n → K),
      c.cost = Allocation.rawRankBound A U := by
  obtain ⟨n,c,hc⟩ := block_profile_achievability A U hAU hq
  exact ⟨n,c,le_antisymm hc (c.rankBound_le_cost hAU (by norm_num))⟩

/-- Task specialization uses the paper's original fifteen-entry profile. -/
theorem task_broadcastOptimum_eq_rankBound (T : Task K F) (hq : 3 ≤ Nat.card K) :
    broadcastOptimum T.A T.U = Profile.rankBound T := by
  rw [broadcastOptimum_eq_rankBound T.A T.U T.side_le_signal hq,
    Allocation.rawRankBound_eq_rankBound]

/-- Two-symbol achievability on an arbitrary presentation of the two-element field. -/
theorem card_two_block_profile_achievability [Fintype K] (hK : Fintype.card K = 2)
    (A U : Three → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥) :
    ∃ n, ∃ c : BlockBroadcastCode A U 2 (Fin n → K),
      c.cost ≤ Allocation.rawRankBound A U := by
  have hspan' : (⨆ i, (A i).prod (A i)) = ⊤ := by
    rw [Profile.three_iSup] at hspan ⊢
    rw [Submodule.prod_sup_prod, Submodule.prod_sup_prod, hspan]
    exact Submodule.prod_top
  have hsep' : (A 0).prod (A 0) ⊓ ((A 1).prod (A 1) ⊔ (A 2).prod (A 2)) = ⊥ := by
    rw [Submodule.prod_sup_prod, Submodule.prod_inf_prod, hsep]
    exact Submodule.prod_bot
  obtain ⟨n,hn,⟨c⟩⟩ := card_two_scalar_lcbc_achievability hK
    (fun i => (A i).prod (A i)) (fun i => (U i).prod (U i))
    (fun i => Submodule.prod_mono (hAU i) (hAU i)) hspan' hsep'
  rw [Allocation.actualNumericLP_eq_rawRankBound] at hn
  exact ⟨n,c.toBlockDouble, (c.toBlockDouble_cost_le).trans_eq (double_length_eq hn)⟩

/-- Operational equality over any two-element field, retaining the geometric hypotheses. -/
theorem card_two_broadcastOptimum_eq_rankBound [Fintype K] (hK : Fintype.card K = 2)
    (A U : Three → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥) :
    broadcastOptimum A U = Allocation.rawRankBound A U := by
  obtain ⟨n,c,hc⟩ := card_two_block_profile_achievability hK A U hAU hspan hsep
  exact broadcastOptimum_eq_of_code A U hAU c (by norm_num) hc

/-- Unified original-field result for spanning, separated-side tasks over every finite field. -/
theorem separated_broadcastOptimum_eq_rankBound
    (A U : Three → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥) :
    broadcastOptimum A U = Allocation.rawRankBound A U := by
  by_cases hq : 3 ≤ Nat.card K
  · exact broadcastOptimum_eq_rankBound A U hAU hq
  · letI := Fintype.ofFinite K
    have htwo : Fintype.card K = 2 := by
      have hh := Finite.one_lt_card (α := K)
      rw [Nat.card_eq_fintype_card] at hh hq
      omega
    exact card_two_broadcastOptimum_eq_rankBound htwo A U hAU hspan hsep

theorem task_separated_broadcastOptimum_eq_rankBound (T : Task K F)
    (hspan : T.Spanning) (hsep : T.A 0 ⊓ (T.A 1 ⊔ T.A 2) = ⊥) :
    broadcastOptimum T.A T.U = Profile.rankBound T := by
  rw [separated_broadcastOptimum_eq_rankBound T.A T.U T.side_le_signal hspan hsep,
    Allocation.rawRankBound_eq_rankBound]

section Binary
variable {B : Type*} [AddCommGroup B] [Module (ZMod 2) B]
  [FiniteDimensional (ZMod 2) B]

theorem block_binary_profile_achievability
    (A U : Three → Submodule (ZMod 2) B) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥) :
    ∃ n, ∃ c : BlockBroadcastCode A U 2 (Fin n → ZMod 2),
      c.cost ≤ Allocation.rawRankBound A U := by
  have hspan' : (⨆ i, (A i).prod (A i)) = ⊤ := by
    rw [Profile.three_iSup] at hspan ⊢
    rw [Submodule.prod_sup_prod, Submodule.prod_sup_prod, hspan]
    exact Submodule.prod_top
  have hsep' : (A 0).prod (A 0) ⊓ ((A 1).prod (A 1) ⊔ (A 2).prod (A 2)) = ⊥ := by
    rw [Submodule.prod_sup_prod, Submodule.prod_inf_prod, hsep]
    exact Submodule.prod_bot
  obtain ⟨n,hn,⟨c⟩⟩ := binary_scalar_profile_achievability
    (fun i => (A i).prod (A i)) (fun i => (U i).prod (U i))
    (fun i => Submodule.prod_mono (hAU i) (hAU i)) hspan' hsep'
  exact ⟨n,c.toBlockDouble, (c.toBlockDouble_cost_le).trans_eq (double_length_eq hn)⟩

/-- Exact binary optimum under the stated spanning and separated-side hypotheses. -/
theorem binary_broadcastOptimum_eq_rankBound
    (A U : Three → Submodule (ZMod 2) B) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥) :
    broadcastOptimum A U = Allocation.rawRankBound A U := by
  obtain ⟨n,c,hc⟩ := block_binary_profile_achievability A U hAU hspan hsep
  exact broadcastOptimum_eq_of_code A U hAU c (by norm_num) hc
end Binary

end UploadBroadcast
