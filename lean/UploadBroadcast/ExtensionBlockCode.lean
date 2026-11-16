import UploadBroadcast.BroadcastOptimum
import UploadBroadcast.ScalarExtensionConfiguration

noncomputable section
open scoped TensorProduct
namespace UploadBroadcast
open TaskDecomposition
variable {K E F : Type*} [Field K] [Field E] [Algebra K E]
  [AddCommGroup F] [Module K F]
variable {d m N : ℕ} (b : Basis (Fin d) K E)

/-- The actual tensor extension of a subspace, identified with its image. -/
def extendedSubspaceEquiv (P : Submodule K F) :
    (E ⊗[K] P) ≃ₗ[E] P.baseChange E :=
  (LinearEquiv.ofInjective (P.subtype.baseChange E)
    (baseChange_injective b P.subtype P.subtype_injective)).trans
    (LinearEquiv.ofEq _ _ (baseChange_eq_range P).symm)

/-- Expand the output coordinates and then use the tensor universal property. -/
def extensionSourceEquiv (e : (Fin N → K) ≃ₗ[K] (Fin m → E)) :
    Source K F N ≃ Source E (E ⊗[K] F) m :=
  (LinearEquiv.arrowCongr (LinearEquiv.refl K F) e).toEquiv.trans
    (LinearMap.liftBaseChangeEquiv E).toEquiv

/-- The same actual source equivalence for each observed subspace. -/
def extensionObservedEquiv (e : (Fin N → K) ≃ₗ[K] (Fin m → E))
    (P : Submodule K F) : Source K P N ≃ Source E (P.baseChange E) m :=
  (extensionSourceEquiv e).trans
    (LinearEquiv.arrowCongr (extendedSubspaceEquiv b P)
      (LinearEquiv.refl E (Fin m → E))).toEquiv

@[simp] theorem extendedSubspaceEquiv_coe (P : Submodule K F) (x : E ⊗[K] P) :
    ((extendedSubspaceEquiv b P x : P.baseChange E) : E ⊗[K] F) =
      P.subtype.baseChange E x := rfl

@[simp] theorem extensionSourceEquiv_tmul
    (e : (Fin N → K) ≃ₗ[K] (Fin m → E)) (x : Source K F N) (a : E) (v : F) :
    extensionSourceEquiv e x (a ⊗ₜ[K] v) = a • e (x v) := rfl

theorem extensionObserved_observe
    (e : (Fin N → K) ≃ₗ[K] (Fin m → E)) (P : Submodule K F) (x : Source K F N) :
    extensionObservedEquiv b e P (observe K F P x) =
      observe E (E ⊗[K] F) (P.baseChange E) (extensionSourceEquiv e x) := by
  apply LinearMap.ext
  intro y
  obtain ⟨z,rfl⟩ := (extendedSubspaceEquiv b P).surjective y
  change extensionSourceEquiv e (observe K F P x)
      ((extendedSubspaceEquiv b P).symm (extendedSubspaceEquiv b P z)) = _
  rw [LinearEquiv.symm_apply_apply]
  change extensionSourceEquiv e (observe K F P x) z =
    extensionSourceEquiv e x (P.subtype.baseChange E z)
  induction z with
  | zero => simp
  | tmul a v => simp [observe]
  | add z w hz hw => simp [hz, hw]

/-- Restrict a genuine extension-field block code using actual field coordinates. -/
def BlockBroadcastCode.restrictExtension
    (e : (Fin N → K) ≃ₗ[K] (Fin m → E)) {A U : Three → Submodule K F} {S : Type*}
    (c : BlockBroadcastCode (fun i => (A i).baseChange E)
      (fun i => (U i).baseChange E) m S) : BlockBroadcastCode A U N S where
  encode x := c.encode (extensionSourceEquiv e x)
  decode i s a := (extensionObservedEquiv b e (U i)).symm
    (c.decode i s (extensionObservedEquiv b e (A i) a))
  zero_error x i := by
    apply (extensionObservedEquiv b e (U i)).injective
    simp only [Equiv.apply_symm_apply, extensionObserved_observe]
    exact c.zero_error _ i

/-- Restriction preserves the attained alphabet exactly, even for nonlinear encoders. -/
theorem BlockBroadcastCode.restrictExtension_range
    (e : (Fin N → K) ≃ₗ[K] (Fin m → E)) {A U : Three → Submodule K F} {S : Type*}
    (c : BlockBroadcastCode (fun i => (A i).baseChange E)
      (fun i => (U i).baseChange E) m S) :
    Set.range (c.restrictExtension b e).encode = Set.range c.encode := by
  change Set.range (c.encode ∘ extensionSourceEquiv e) = Set.range c.encode
  rw [Set.range_comp, EquivLike.range_eq_univ (extensionSourceEquiv e), Set.image_univ]

/-- Pack exactly `d` ground-field coordinates into each extension-field symbol. -/
def extensionSymbolEquiv : (Fin (m * d) → K) ≃ₗ[K] (Fin m → E) :=
  (LinearEquiv.funCongrLeft K K finProdFinEquiv).trans
    ((LinearEquiv.curry K K (Fin m) (Fin d)).trans
      (LinearEquiv.piCongrRight (fun _ : Fin m => b.equivFun.symm)))

/-- Exact normalized cost, using the actual attained alphabet, is unchanged. -/
theorem BlockBroadcastCode.restrictExtension_cost
    {A U : Three → Submodule K F} {S : Type*}
    (c : BlockBroadcastCode (fun i => (A i).baseChange E)
      (fun i => (U i).baseChange E) m S)
    (hcard : Nat.card E = Nat.card K ^ d) :
    (c.restrictExtension b (extensionSymbolEquiv b)).cost = c.cost := by
  unfold BlockBroadcastCode.cost
  rw [c.restrictExtension_range b, hcard, Nat.cast_pow, Nat.cast_mul]
  simp only [Real.logb, Real.log_pow]
  ring

/-- An actual attaining extension-field code gives an actual ground-field code,
with blocklength multiplied by the extension degree and exactly the same cost. -/
theorem extension_block_profile_achievability
    (b : Basis (Fin d) K E)
    [Finite K] [Finite E] [FiniteDimensional K F]
    (A U : Three → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (hq : 3 ≤ Nat.card E) (hcard : Nat.card E = Nat.card K ^ d)
    (hr : Allocation.rawRankBound (fun i => (A i).baseChange E)
      (fun i => (U i).baseChange E) = Allocation.rawRankBound A U) :
    ∃ n, ∃ c : BlockBroadcastCode A U (2 * d) (Fin n → E),
      c.cost = Allocation.rawRankBound A U := by
  obtain ⟨n,c,hc⟩ := block_profile_exact (fun i => (A i).baseChange E)
    (fun i => (U i).baseChange E) (fun i => baseChange_mono (hAU i)) hq
  refine ⟨n,c.restrictExtension b (extensionSymbolEquiv b), ?_⟩
  rw [c.restrictExtension_cost b hcard, hc, hr]

end UploadBroadcast
