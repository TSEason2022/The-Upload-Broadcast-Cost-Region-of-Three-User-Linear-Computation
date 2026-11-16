import UploadBroadcast.ScalarBroadcast
import UploadBroadcast.Profile

namespace UploadBroadcast
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Fully informed zero-error block broadcast. The encoder and decoders may be nonlinear. -/
structure BlockBroadcastCode (A U : Three → Submodule K F) (L : ℕ) (S : Type*) where
  encode : Source K F L → S
  decode : ∀ i, S → Source K (A i) L → Source K (U i) L
  zero_error : ∀ x i, decode i (encode x) (observe K F (A i) x) = observe K F (U i) x

/-- Actual attained-alphabet cost per source symbol. -/
noncomputable def BlockBroadcastCode.cost {A U : Three → Submodule K F}
    {L : ℕ} {S : Type*} (c : BlockBroadcastCode A U L S) : ℝ :=
  Real.logb (Nat.card K) (Nat.card (Set.range c.encode)) / L

/-- A two-column source is exactly a scalar covector on the doubled coefficient space. -/
def sourceDoubleEquiv : Source K F 2 ≃ₗ[K] ((F × F) →ₗ[K] K) where
  toFun x := ((LinearMap.proj 0).comp x).coprod ((LinearMap.proj 1).comp x)
  invFun x := LinearMap.pi ![x.comp (LinearMap.inl K F F), x.comp (LinearMap.inr K F F)]
  left_inv x := by ext v i; fin_cases i <;> simp
  right_inv x := by
    apply LinearMap.ext
    intro v
    change x (v.1,0) + x (0,v.2) = x v
    rw [← map_add]
    simp
  map_add' x y := by
    apply LinearMap.ext
    intro v
    change (x v.1 0 + y v.1 0) + (x v.2 1 + y v.2 1) = _
    change _ = (x v.1 0 + x v.2 1) + (y v.1 0 + y v.2 1)
    abel
  map_smul' c x := by
    apply LinearMap.ext
    intro v
    change c • x v.1 0 + c • x v.2 1 = c • (x v.1 0 + x v.2 1)
    exact (smul_add _ _ _).symm

/-- The same coordinate equivalence for an observed subspace. -/
def observedDoubleEquiv (A : Submodule K F) :
    Source K A 2 ≃ₗ[K] (A.prod A →ₗ[K] K) :=
  sourceDoubleEquiv.trans
    (LinearEquiv.arrowCongr (Profile.submoduleProdEquiv A A).symm (LinearEquiv.refl K K))

theorem observedDouble_observe (A : Submodule K F) (x : Source K F 2) :
    observedDoubleEquiv A (observe K F A x) =
      dualObserve (A.prod A) (sourceDoubleEquiv x) := by
  ext a
  rfl

/-- Turn a scalar code on the doubled coefficient space into an actual length-two code. -/
def ScalarBroadcastCode.toBlockDouble {A U : Three → Submodule K F} {n : ℕ}
    (c : ScalarBroadcastCode (fun i => (A i).prod (A i))
      (fun i => (U i).prod (U i)) n) : BlockBroadcastCode A U 2 (Fin n → K) where
  encode x := c.encode (sourceDoubleEquiv x)
  decode i s a := (observedDoubleEquiv (U i)).symm (c.decode i (s, observedDoubleEquiv (A i) a))
  zero_error x i := by
    apply (observedDoubleEquiv (U i)).injective
    simp only [LinearEquiv.apply_symm_apply, observedDouble_observe]
    exact c.zero_error _ i

theorem ScalarBroadcastCode.toBlockDouble_cost_le [Finite K] [FiniteDimensional K F]
    {A U : Three → Submodule K F} {n : ℕ}
    (c : ScalarBroadcastCode (fun i => (A i).prod (A i))
      (fun i => (U i).prod (U i)) n) :
    c.toBlockDouble.cost ≤ (n : ℝ) / 2 := by
  have hr : Set.range c.toBlockDouble.encode = Set.range c.encode := by
    change Set.range (c.encode ∘ sourceDoubleEquiv) = Set.range c.encode
    rw [Set.range_comp, EquivLike.range_eq_univ sourceDoubleEquiv]
    exact Set.image_univ
  unfold BlockBroadcastCode.cost
  rw [hr]
  exact div_le_div_of_nonneg_right (scalarBroadcastCode_cost_le c) (by norm_num)

/-- Relabel a finite broadcast alphabet without changing its operational meaning. -/
def BlockBroadcastCode.relabel {A U : Three → Submodule K F}
    {L : ℕ} {S V : Type*} (c : BlockBroadcastCode A U L S) (e : S ≃ V) :
    BlockBroadcastCode A U L V where
  encode x := e (c.encode x)
  decode i s a := c.decode i (e.symm s) a
  zero_error x i := by simp only [Equiv.symm_apply_apply]; exact c.zero_error x i

theorem BlockBroadcastCode.relabel_cost {A U : Three → Submodule K F}
    {L : ℕ} {S V : Type*} (c : BlockBroadcastCode A U L S) (e : S ≃ V) :
    (c.relabel e).cost = c.cost := by
  unfold BlockBroadcastCode.cost
  have h : Set.range (c.relabel e).encode = e '' Set.range c.encode := Set.range_comp e c.encode
  rw [h, Nat.card_image_of_injective e.injective]

/-- Every finite-alphabet code has an equivalent code with alphabet `Fin n`. -/
theorem BlockBroadcastCode.finite_relabel {A U : Three → Submodule K F}
    {L : ℕ} {S : Type*} [Finite S] (c : BlockBroadcastCode A U L S) :
    ∃ n, ∃ (d : BlockBroadcastCode A U L (Fin n)), d.cost = c.cost := by
  letI := Fintype.ofFinite S
  exact ⟨Fintype.card S, c.relabel (Fintype.equivFin S), c.relabel_cost _⟩

end UploadBroadcast
