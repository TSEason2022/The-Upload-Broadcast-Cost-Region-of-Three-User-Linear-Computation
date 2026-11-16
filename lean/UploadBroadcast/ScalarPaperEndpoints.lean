import UploadBroadcast.GeneralBroadcastOptimum
import UploadBroadcast.ScalarEndpoints

/-! Exact attained scalar costs at the ceiling of the operational optimum.
This includes the scalar-to-one-symbol model bridge, so nominal message length
is not substituted for attained-alphabet cost. -/
namespace UploadBroadcast
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

def sourceOneEquiv : Source K F 1 ≃ₗ[K] (F →ₗ[K] K) where
  toFun x := (LinearMap.proj 0).comp x
  invFun x := LinearMap.pi (fun _ : Fin 1 => x)
  left_inv x := by ext v i; fin_cases i; rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sourceOne_observe (A : Submodule K F) (x : Source K F 1) :
    sourceOneEquiv (observe K F A x) = dualObserve A (sourceOneEquiv x) := rfl

def ScalarBroadcastCode.toBlockOne {A U : Three → Submodule K F} {n : ℕ}
    (c : ScalarBroadcastCode A U n) : BlockBroadcastCode A U 1 (Fin n → K) where
  encode x := c.encode (sourceOneEquiv x)
  decode i s a := sourceOneEquiv.symm (c.decode i (s, sourceOneEquiv a))
  zero_error x i := by
    apply (sourceOneEquiv (K := K) (F := U i)).injective
    simp only [LinearEquiv.apply_symm_apply, sourceOne_observe]
    exact c.zero_error (sourceOneEquiv x) i

theorem ScalarBroadcastCode.toBlockOne_cost {A U : Three → Submodule K F} {n : ℕ}
    (c : ScalarBroadcastCode A U n) :
    c.toBlockOne.cost = Real.logb (Nat.card K) (Nat.card (Set.range c.encode)) := by
  have hr : Set.range c.toBlockOne.encode = Set.range c.encode := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨sourceOneEquiv x,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨sourceOneEquiv.symm x, by simp [toBlockOne]⟩
  simp [BlockBroadcastCode.cost, hr]

variable [Finite K] [FiniteDimensional K F]

/-- An actual scalar linear code with ceiling-length alphabet coordinates
must attain that ceiling exactly, by integrality and the nonlinear converse. -/
theorem ScalarBroadcastCode.cost_eq_ceiling {A U : Three → Submodule K F} {n : ℕ}
    (c : ScalarBroadcastCode A U n) (hAU : ∀ i, A i ≤ U i)
    (hn : (n : ℤ) = ⌈Allocation.rawRankBound A U⌉) :
    Real.logb (Nat.card K) (Nat.card (Set.range c.encode)) = (n : ℝ) := by
  have hl := c.toBlockOne.rankBound_le_cost hAU (by decide : 0 < 1)
  rw [c.toBlockOne_cost, linear_alphabet_log] at hl
  have hu := scalarBroadcastCode_cost_le c
  rw [linear_alphabet_log] at hu
  have hz : (n : ℤ) ≤ (Module.finrank K (LinearMap.range c.encode) : ℤ) := by
    rw [hn]
    exact Int.ceil_le.mpr (by simpa using hl)
  have hnle : n ≤ Module.finrank K (LinearMap.range c.encode) := by exact_mod_cast hz
  have hnge : Module.finrank K (LinearMap.range c.encode) ≤ n := by exact_mod_cast hu
  rw [linear_alphabet_log, Nat.le_antisymm hnge hnle]

/-- Source proposition: scalar LCBC at ceil D* for fields of size at least three,
with D* defined operationally over arbitrary nonlinear finite block codes. -/
theorem scalar_at_operational_ceiling (A U : Three → Submodule K F)
    (hAU : ∀ i, A i ≤ U i) (hq : 3 ≤ Nat.card K) :
    ∃ (n : ℕ) (c : ScalarBroadcastCode A U n),
      (n : ℤ) = ⌈broadcastOptimum A U⌉ ∧
      Real.logb (Nat.card K) (Nat.card (Set.range c.encode)) = (n : ℝ) := by
  obtain ⟨n,hn,⟨c⟩⟩ := scalar_profile_achievability A U hAU hq
  exact ⟨n,c,by simpa [general_broadcastOptimum_eq_rankBound A U hAU] using hn,
    c.cost_eq_ceiling hAU hn⟩

/-- Binary version, with explicit original spanning and separation hypotheses. -/
theorem binary_at_operational_ceiling [Fintype K] (hK : Fintype.card K = 2)
    (A U : Three → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥) :
    ∃ (n : ℕ) (c : ScalarBroadcastCode A U n),
      (n : ℤ) = ⌈broadcastOptimum A U⌉ ∧
      Real.logb (Nat.card K) (Nat.card (Set.range c.encode)) = (n : ℝ) := by
  obtain ⟨n,c,hn,_⟩ := card_two_scalar_profile_achievability_cost hK A U hAU hspan hsep
  exact ⟨n,c,by simpa [general_broadcastOptimum_eq_rankBound A U hAU] using hn,
    c.cost_eq_ceiling hAU hn⟩

/-- Exact source integer-allocation lemma with the optimal value interpreted
operationally, rather than assumed equal to a numerical rank program. -/
theorem integer_allocation_at_operational_optimum
    (A U : Three → Submodule K F) (hAU : ∀ i, A i ≤ U i) :
    ∃ s : ScalarAllocation A U,
      s.r = Allocation.commonRank A U ∧ (s.length : ℤ) = ⌈broadcastOptimum A U⌉ := by
  simpa only [general_broadcastOptimum_eq_rankBound A U hAU] using
    Allocation.actual_nat_profile_allocation A U

end UploadBroadcast
