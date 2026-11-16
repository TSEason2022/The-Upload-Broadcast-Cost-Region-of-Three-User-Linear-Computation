import UploadBroadcast.ScalarEndReflection
import UploadBroadcast.ScalarExtensionConfiguration

/-! Scalar stable endomorphisms remain scalar over arbitrary field extensions. -/
noncomputable section
open scoped TensorProduct
namespace UploadBroadcast.TaskDecomposition

variable {K L V ι J : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V] [DecidableEq J]

/-- A coefficient of a tensor with respect to an arbitrary (possibly infinite) field basis. -/
def tensorCoefficient (b : Basis J K L) (j : J) : (L ⊗[K] V) →ₗ[K] V :=
  (Finsupp.lapply j).comp (TensorProduct.equivFinsuppOfBasisLeft b).toLinearMap

@[simp] theorem tensorCoefficient_tmul (b : Basis J K L) (j : J) (a : L) (v : V) :
    tensorCoefficient b j (a ⊗ₜ[K] v) = b.repr a j • v :=
  TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply b a v j

/-- Every tensor coefficient of an extended subspace lies in the original subspace. -/
theorem tensorCoefficient_mem (b : Basis J K L) (j : J) (P : Submodule K V)
    {z : L ⊗[K] V} (hz : z ∈ P.baseChange L) : tensorCoefficient b j z ∈ P := by
  rw [baseChange_eq_range] at hz
  obtain ⟨y, rfl⟩ := hz
  induction y with
  | zero => simp
  | tmul a x =>
    simpa using P.smul_mem (b.repr a j) x.property
  | add x y hx hy => simpa using P.add_mem hx hy

/-- Extend a linear functional and identify the scalar tensor factor with the extension field. -/
def tensorEvaluate (ell : V →ₗ[K] K) : (L ⊗[K] V) →ₗ[L] L :=
  (TensorProduct.AlgebraTensorModule.rid K L L).toLinearMap.comp (ell.baseChange L)

@[simp] theorem tensorEvaluate_tmul (ell : V →ₗ[K] K) (a : L) (v : V) :
    tensorEvaluate (L := L) ell (a ⊗ₜ[K] v) = algebraMap K L (ell v) * a := by
  simp [tensorEvaluate, Algebra.smul_def]

/-- Coefficient extraction commutes with evaluating the vector component. -/
theorem tensorEvaluate_coefficient (b : Basis J K L) (ell : V →ₗ[K] K)
    (j : J) (z : L ⊗[K] V) :
    b.repr (tensorEvaluate ell z) j = ell (tensorCoefficient b j z) := by
  induction z with
  | zero => simp
  | tmul a v =>
    rw [tensorEvaluate_tmul, tensorCoefficient_tmul, ← Algebra.smul_def, map_smul, map_smul]
    simp [Finsupp.smul_apply, smul_eq_mul, mul_comm]
  | add x y hx hy => simp [hx, hy]

/-- A coefficient of an extension-field preserving map is an original-field
preserving map. This uses actual subspace membership, not a dimension count. -/
def coefficientEnd (b : Basis J K L) (j : J) (f : (L ⊗[K] V) →ₗ[L] (L ⊗[K] V)) : V →ₗ[K] V :=
  (tensorCoefficient b j).comp ((f.restrictScalars K).comp (TensorProduct.mk K L V 1))

theorem coefficientEnd_stable (b : Basis J K L) (j : J) (S : ι → Submodule K V)
    (f : (L ⊗[K] V) →ₗ[L] (L ⊗[K] V)) (hf : Stable (extendConfiguration (L := L) S) f) :
    Stable S (coefficientEnd b j f) := by
  intro i x hx
  exact tensorCoefficient_mem b j (S i)
    (hf i (1 ⊗ₜ[K] x) (Submodule.tmul_mem_baseChange_of_mem 1 hx))

/-- Scalarity ascends along every field extension. The witness functional is
used only to read the scalar from the image of one nonzero vector. -/
theorem scalarEnd_baseChange_with_witness (S : ι → Submodule K V)
    (hS : ∀ f : V →ₗ[K] V, Stable S f → ∃ c : K, f = c • LinearMap.id)
    (v₀ : V) (ell : V →ₗ[K] K) (hell : ell v₀ = 1)
    (f : (L ⊗[K] V) →ₗ[L] (L ⊗[K] V)) (hf : Stable (extendConfiguration (L := L) S) f) :
    ∃ c : L, f = c • LinearMap.id := by
  classical
  let b := Basis.ofVectorSpace K L
  choose c hc using fun j => hS (coefficientEnd b j f) (coefficientEnd_stable b j S f hf)
  have hcoeff (j) (v : V) : tensorCoefficient b j (f (1 ⊗ₜ[K] v)) = c j • v :=
    LinearMap.congr_fun (hc j) v
  let a : L := tensorEvaluate ell (f (1 ⊗ₜ[K] v₀))
  have ha (j) : b.repr a j = c j := by
    rw [tensorEvaluate_coefficient, hcoeff, map_smul, hell, smul_eq_mul, mul_one]
  have hpure (v : V) : f (1 ⊗ₜ[K] v) = a ⊗ₜ[K] v := by
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext j
    change tensorCoefficient b j (f (1 ⊗ₜ[K] v)) = tensorCoefficient b j (a ⊗ₜ[K] v)
    rw [hcoeff, tensorCoefficient_tmul, ha]
  refine ⟨a, ?_⟩
  apply LinearMap.ext
  intro z
  change f z = a • z
  induction z with
  | zero => simp
  | tmul c v =>
    have hh : c ⊗ₜ[K] v = c • (1 ⊗ₜ[K] v) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hh, map_smul, hpure]
    simp [TensorProduct.smul_tmul', smul_smul, mul_comm]
  | add x y hx hy => simp [hx, hy, smul_add]

/-- A nonzero vector space admits a vector and a normalized linear functional. -/
theorem exists_normalized_functional [Nontrivial V] :
    ∃ (v₀ : V) (ell : V →ₗ[K] K), ell v₀ = 1 := by
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨ell, hell⟩ := (LinearMap.toSpanSingleton K V v₀).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (smul_left_injective K hv₀))
  exact ⟨v₀, ell, by simpa using LinearMap.congr_fun hell 1⟩

theorem scalarEnd_baseChange [Nontrivial V] (S : ι → Submodule K V)
    (hS : ∀ f : V →ₗ[K] V, Stable S f → ∃ c : K, f = c • LinearMap.id)
    (f : (L ⊗[K] V) →ₗ[L] (L ⊗[K] V)) (hf : Stable (extendConfiguration (L := L) S) f) :
    ∃ c : L, f = c • LinearMap.id := by
  obtain ⟨v₀, ell, hell⟩ := exists_normalized_functional (K := K) (V := V)
  exact scalarEnd_baseChange_with_witness S hS v₀ ell hell f hf

/-- Nonzero pure tensors are verified by evaluating a normalized functional. -/
theorem scalarExtension_nontrivial [Nontrivial V] : Nontrivial (L ⊗[K] V) := by
  obtain ⟨v₀, ell, hell⟩ := exists_normalized_functional (K := K) (V := V)
  apply nontrivial_of_ne (1 ⊗ₜ[K] v₀) 0
  intro h
  have hh := congrArg (tensorEvaluate (L := L) ell) h
  simp [hell] at hh

/-- Scalar stable endomorphisms rule out every nontrivial simultaneous split. -/
theorem indecomposable_of_scalarEnd [Nontrivial V] (S : ι → Submodule K V)
    (hS : ∀ f : V →ₗ[K] V, Stable S f → ∃ c : K, f = c • LinearMap.id) :
    Indecomposable S ⊤ := by
  refine ⟨top_ne_bot, ?_⟩
  intro P Q h
  obtain ⟨p, hp, hpp, hpP, hpQ⟩ := h.exists_stable_projection
  obtain ⟨c, hc⟩ := hS p hp
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hcc : c*c = c := by
    apply smul_left_injective K hx
    have hh := hpp x
    rw [hc] at hh
    simpa [smul_smul] using hh
  have hc01 : c = 0 ∨ c = 1 := by
    have hh : c * (c-1) = 0 := by rw [mul_sub, mul_one, hcc, sub_self]
    exact (mul_eq_zero.mp hh).imp_right sub_eq_zero.mp
  rcases hc01 with hc0 | hc1
  · left
    have hp0 : p = 0 := by simp [hc, hc0]
    apply bot_unique
    intro y hy
    have hh := hpP y hy
    rw [hp0, LinearMap.zero_apply] at hh
    exact hh.symm
  · right
    have hp1 : p = LinearMap.id := by simp [hc, hc1]
    apply bot_unique
    intro y hy
    have hh := hpQ y hy
    rw [hp1, LinearMap.id_apply] at hh
    exact hh

/-- Absolute indecomposability follows from scalar stable endomorphisms, over
arbitrary extensions and without an algebraic-closure or finite-extension assumption. -/
theorem scalarEnd_baseChange_indec [Nontrivial V] (S : ι → Submodule K V)
    (hS : ∀ f : V →ₗ[K] V, Stable S f → ∃ c : K, f = c • LinearMap.id) :
    Indecomposable (extendConfiguration (L := L) S) ⊤ := by
  letI := scalarExtension_nontrivial (K := K) (L := L) (V := V)
  exact indecomposable_of_scalarEnd _ (scalarEnd_baseChange S hS)

/-- The manuscript's nonzero-defect base-field component remains indecomposable
under every field extension. The result is for the actual six extended subspaces. -/
theorem Task.nonzero_defect_extend_indec {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Task K V) (hT : Indecomposable T.spaces ⊤)
    (hd : ReflectionReduction.defect T.dimensionVector ≠ 0)
    (L : Type*) [Field L] [Algebra K L] : Indecomposable (T.extend (L := L)).spaces ⊤ := by
  have hn : Nontrivial V := by
    rcases subsingleton_or_nontrivial V with hz | hn
    · letI := hz
      exact False.elim (hT.1 (by apply bot_unique; intro x _; exact Subsingleton.elim x 0))
    · exact hn
  letI := hn
  have heq : (T.extend (L := L)).spaces = extendConfiguration (L := L) T.spaces := by
    funext i
    rcases i with ⟨i, b⟩
    cases b <;> rfl
  rw [heq]
  exact scalarEnd_baseChange_indec T.spaces (T.nonzero_defect_end_scalar hT hd)

end UploadBroadcast.TaskDecomposition
