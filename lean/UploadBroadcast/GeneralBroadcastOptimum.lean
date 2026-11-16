import UploadBroadcast.ExtensionBlockCode
import UploadBroadcast.BaseChangeProfile

/-! Fully informed LCBC operational optimum over every finite field.
The binary case uses an actual four-symbol ground-field code obtained by
restricting an actual two-symbol code over its quadratic extension. -/
namespace UploadBroadcast

 theorem binary_general_block_profile_exact
    {F : Type*} [AddCommGroup F] [Module (ZMod 2) F]
    [FiniteDimensional (ZMod 2) F]
    (A U : Three → Submodule (ZMod 2) F) (hAU : ∀ i, A i ≤ U i) :
    ∃ n, ∃ c : BlockBroadcastCode A U 4 (Fin n → BinaryExtension.F4),
      c.cost = Allocation.rawRankBound A U := by
  exact extension_block_profile_achievability BinaryExtension.basis A U hAU
    (by rw [BinaryExtension.card]; decide)
    (by rw [BinaryExtension.card]; norm_num [Nat.card_eq_fintype_card])
    (rawRankBound_baseChange BinaryExtension.basis A U)

theorem binary_general_broadcastOptimum_eq_rankBound
    {F : Type*} [AddCommGroup F] [Module (ZMod 2) F]
    [FiniteDimensional (ZMod 2) F]
    (A U : Three → Submodule (ZMod 2) F) (hAU : ∀ i, A i ≤ U i) :
    broadcastOptimum A U = Allocation.rawRankBound A U := by
  obtain ⟨n,c,hc⟩ := binary_general_block_profile_exact A U hAU
  exact broadcastOptimum_eq_of_code A U hAU c (by decide) hc.le

/-- Arbitrary presentations of the binary field also admit an actual four-symbol code. -/
theorem card_two_general_block_profile_exact
    {K F : Type*} [Field K] [Fintype K] [AddCommGroup F] [Module K F]
    [FiniteDimensional K F] (hK : Fintype.card K = 2)
    (A U : Three → Submodule K F) (hAU : ∀ i, A i ≤ U i) :
    ∃ n, ∃ c : BlockBroadcastCode A U 4 (Fin n → BinaryExtension.F4),
      c.cost = Allocation.rawRankBound A U := by
  letI : Algebra K BinaryExtension.F4 := Algebra.compHom BinaryExtension.F4
    (BinaryFieldTransport.fieldEquiv hK).symm.toRingHom
  letI : Fintype BinaryExtension.F4 := Fintype.ofFinite _
  letI : FiniteDimensional K BinaryExtension.F4 := Module.Finite.of_finite
  have hd : Module.finrank K BinaryExtension.F4 = 2 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have h := Module.card_eq_pow_finrank (K := K) (V := BinaryExtension.F4)
    rw [hK] at h
    have h4 : Fintype.card BinaryExtension.F4 = 4 := by
      rw [← Nat.card_eq_fintype_card, BinaryExtension.card]
    rw [h4] at h
    exact h.symm
  let b : Basis (Fin 2) K BinaryExtension.F4 :=
    (Module.finBasis K BinaryExtension.F4).reindex (finCongr hd)
  exact extension_block_profile_achievability b A U hAU
    (by rw [BinaryExtension.card]; decide)
    (by rw [BinaryExtension.card, Nat.card_eq_fintype_card, hK]; decide)
    (rawRankBound_baseChange b A U)

/-- Exact optimum for every finite field and arbitrary nested side-information
and signal subspaces. There is no separation or spanning premise. -/
theorem general_broadcastOptimum_eq_rankBound
    {K F : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
    [FiniteDimensional K F]
    (A U : Three → Submodule K F) (hAU : ∀ i, A i ≤ U i) :
    broadcastOptimum A U = Allocation.rawRankBound A U := by
  by_cases hq : 3 ≤ Nat.card K
  · exact broadcastOptimum_eq_rankBound A U hAU hq
  · letI := Fintype.ofFinite K
    have htwo : Fintype.card K = 2 := by
      have hh := Finite.one_lt_card (α := K)
      rw [Nat.card_eq_fintype_card] at hh hq
      omega
    obtain ⟨n,c,hc⟩ := card_two_general_block_profile_exact htwo A U hAU
    exact broadcastOptimum_eq_of_code A U hAU c (by decide) hc.le

/-- The operational optimum is attained with at most four source symbols,
using a genuinely finite alphabet relabeled as `Fin n`. -/
theorem general_block_profile_attained
    {K F : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
    [FiniteDimensional K F]
    (A U : Three → Submodule K F) (hAU : ∀ i, A i ≤ U i) :
    ∃ L n, ∃ c : BlockBroadcastCode A U L (Fin n),
      0 < L ∧ L ≤ 4 ∧ c.cost = Allocation.rawRankBound A U := by
  by_cases hq : 3 ≤ Nat.card K
  · obtain ⟨n,c,hc⟩ := block_profile_exact A U hAU hq
    obtain ⟨k,e,he⟩ := c.finite_relabel
    exact ⟨2,k,e,by decide,by decide,he.trans hc⟩
  · letI := Fintype.ofFinite K
    have htwo : Fintype.card K = 2 := by
      have hh := Finite.one_lt_card (α := K)
      rw [Nat.card_eq_fintype_card] at hh hq
      omega
    obtain ⟨n,c,hc⟩ := card_two_general_block_profile_exact htwo A U hAU
    obtain ⟨k,e,he⟩ := c.finite_relabel
    exact ⟨4,k,e,by decide,by decide,he.trans hc⟩

/-- The original fifteen-entry task profile is the operational optimum over
all nonlinear finite-alphabet, positive-blocklength, zero-error codes. -/
theorem task_general_broadcastOptimum_eq_rankBound
    {K F : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
    [FiniteDimensional K F] (T : Task K F) :
    broadcastOptimum T.A T.U = Profile.rankBound T := by
  rw [general_broadcastOptimum_eq_rankBound T.A T.U T.side_le_signal,
    Allocation.rawRankBound_eq_rankBound]

end UploadBroadcast
