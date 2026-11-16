import UploadBroadcast.TaskDecomposition
import UploadBroadcast.FiniteMonoidPower
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.Pi

namespace UploadBroadcast.TaskDecomposition
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Ring of simultaneous endomorphisms of a subspace configuration. -/
def stableEnd (S : ι → Submodule K V) : Subring (Module.End K V) where
  carrier := {f | Stable S f}
  zero_mem' := by intro i x hx; exact (S i).zero_mem
  one_mem' := by intro i x hx; exact hx
  add_mem' := by intro f g hf hg i x hx; exact (S i).add_mem (hf i x hx) (hg i x hx)
  neg_mem' := by intro f hf i x hx; exact (S i).neg_mem (hf i x hx)
  mul_mem' := by intro f g hf hg i x hx; exact hf i (g x) (hg i x hx)

lemma stableEnd.idempotent_eq_zero_or_one {S : ι → Submodule K V}
    (h : Indecomposable S ⊤) (f : stableEnd S) (hf : f * f = f) :
    f = 0 ∨ f = 1 := by
  have hid (x : V) : (f : Module.End K V) ((f : Module.End K V) x) = (f : Module.End K V) x := by
    exact congrArg (fun a : stableEnd S => (a : Module.End K V) x) hf
  obtain hz | ho := h.projection_eq_zero_or_id f f.property hid
  · exact Or.inl (Subtype.ext hz)
  · exact Or.inr (Subtype.ext ho)

/-- Finite-dimensional configurations over finite fields have finite
endomorphism rings. -/
instance stableEnd.finite [Finite K] [FiniteDimensional K V]
    (S : ι → Submodule K V) : Finite (stableEnd S) := by
  letI : Finite V := Module.finite_of_finite K
  letI : Finite (Module.End K V) := Finite.of_injective
    (fun f : Module.End K V => (f : V → V)) DFunLike.coe_injective
  exact Finite.of_injective (fun f : stableEnd S => (f : Module.End K V)) Subtype.val_injective

/-- The noncommutative version of the local-ring unit-sum lemma. -/
theorem local_isUnit_or_isUnit_of_add {R : Type*} [Ring R] [IsLocalRing R]
    {a b : R} (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b := by
  obtain ⟨u, hu⟩ := h
  have he : (↑u⁻¹ : R) * a + (↑u⁻¹ : R) * b = 1 := by
    rw [← mul_add, ← hu, Units.inv_mul]
  obtain ha | hb := IsLocalRing.isUnit_or_isUnit_of_add_one he
  · left
    have hh := u.isUnit.mul ha
    simpa only [← mul_assoc, Units.mul_inv, one_mul] using hh
  · right
    have hh := u.isUnit.mul hb
    simpa only [← mul_assoc, Units.mul_inv, one_mul] using hh

/-- A finite sum which is a unit in a possibly noncommutative local ring has a
unit summand. -/
theorem local_exists_isUnit_of_sum {R J : Type*} [Ring R] [IsLocalRing R]
    (s : Finset J) (f : J → R) (h : IsUnit (∑ j ∈ s, f j)) :
    ∃ j ∈ s, IsUnit (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at h
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj] at h
    obtain hu | hu := local_isUnit_or_isUnit_of_add h
    · exact ⟨j, Finset.mem_insert_self _ _, hu⟩
    · obtain ⟨k, hk, hu⟩ := ih hu
      exact ⟨k, Finset.mem_insert_of_mem hk, hu⟩

/-- Every simultaneous endomorphism of an indecomposable finite-field task is
nilpotent or invertible in the simultaneous endomorphism ring itself. -/
theorem stableEnd.nilpotent_or_unit [Finite K] [FiniteDimensional K V]
    {S : ι → Submodule K V} (h : Indecomposable S ⊤) (f : stableEnd S) :
    IsNilpotent f ∨ IsUnit f := by
  obtain ⟨n, hn, he⟩ := FiniteMonoidPower.exists_pos_pow_add_eq f
  have hi : f ^ n * f ^ n = f ^ n := by rwa [← pow_add]
  obtain hz | ho := stableEnd.idempotent_eq_zero_or_one h (f ^ n) hi
  · exact Or.inl ⟨n, hz⟩
  · exact Or.inr (IsUnit.of_pow_eq_one ho (Nat.ne_of_gt hn))

/-- The stable endomorphism ring of a nonzero indecomposable finite-field
configuration is local. No Krull–Schmidt or Fitting theorem is assumed. -/
theorem stableEnd.isLocalRing [Finite K] [FiniteDimensional K V]
    {S : ι → Submodule K V} (h : Indecomposable S ⊤) : IsLocalRing (stableEnd S) := by
  have hn : (0 : stableEnd S) ≠ 1 := by
    intro he
    apply h.1
    apply le_antisymm _ bot_le
    intro x _
    have hx := congrArg (fun f : stableEnd S => (f : Module.End K V) x) he
    exact hx.symm
  letI : Nontrivial (stableEnd S) := nontrivial_of_ne 0 1 hn
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  obtain hn | hu := stableEnd.nilpotent_or_unit h f
  · exact Or.inr hn.isUnit_one_sub
  · exact Or.inl hu

/-- Maps preserving all labeled spaces between two configurations. -/
def Preserves {W : Type*} [AddCommGroup W] [Module K W]
    (S : ι → Submodule K V) (T : ι → Submodule K W) (f : V →ₗ[K] W) : Prop :=
  ∀ i x, x ∈ S i → f x ∈ T i

/-- Isomorphism preserving the labels in both directions. -/
def ConfigurationIso {W : Type*} [AddCommGroup W] [Module K W]
    (S : ι → Submodule K V) (T : ι → Submodule K W) : Prop :=
  ∃ e : V ≃ₗ[K] W, Preserves S T e.toLinearMap ∧ Preserves T S e.symm.toLinearMap

/-- A nonzero retract of an indecomposable configuration is the whole
configuration. This statement does not require a finite ground field. -/
theorem iso_of_retraction {W : Type*} [AddCommGroup W] [Module K W]
    {S : ι → Submodule K V} {T : ι → Submodule K W}
    (hS : (⊤ : Submodule K V) ≠ ⊥) (hT : Indecomposable T ⊤)
    (f : V →ₗ[K] W) (g : W →ₗ[K] V)
    (hf : Preserves S T f) (hg : Preserves T S g) (hgf : ∀ x, g (f x) = x) :
    ConfigurationIso S T := by
  have hp : Stable T (f.comp g) := fun i x hx => hf i (g x) (hg i x hx)
  have hid (x : W) : (f.comp g) ((f.comp g) x) = (f.comp g) x := by
    simp only [LinearMap.comp_apply, hgf]
  obtain hz | ho := hT.projection_eq_zero_or_id (f.comp g) hp hid
  · exfalso
    apply hS
    apply le_antisymm _ bot_le
    intro x _
    have hfx : f x = 0 := by
      calc
        f x = (f.comp g) (f x) := by simp only [LinearMap.comp_apply, hgf]
        _ = 0 := by rw [hz]; rfl
    have hx := congrArg g hfx
    simpa only [hgf, map_zero] using hx
  · have hfg (x : W) : f (g x) = x := congrArg (fun p : W →ₗ[K] W => p x) ho
    let e : V ≃ₗ[K] W :=
      { f with invFun := g, left_inv := hgf, right_inv := hfg }
    exact ⟨e, hf, hg⟩

/-- The exact finite-copy Krull–Schmidt step needed in descent: if the identity
of an indecomposable configuration is a finite sum of factorizations through
one indecomposable configuration, the two configurations are isomorphic.
The factorization identity is precisely the coordinate form of being a retract
of a finite direct sum of copies. -/
theorem iso_of_sum_factorizations [Finite K] [FiniteDimensional K V]
    {W J : Type*} [AddCommGroup W] [Module K W]
    {S : ι → Submodule K V} {T : ι → Submodule K W}
    (hS : Indecomposable S ⊤) (hT : Indecomposable T ⊤)
    (s : Finset J) (f : J → V →ₗ[K] W) (g : J → W →ₗ[K] V)
    (hf : ∀ j, Preserves S T (f j)) (hg : ∀ j, Preserves T S (g j))
    (hsum : (∑ j ∈ s, (g j).comp (f j)) = LinearMap.id) :
    ConfigurationIso S T := by
  classical
  let a : J → stableEnd S := fun j =>
    ⟨(g j).comp (f j), fun i x hx => hg j i (f j x) (hf j i x hx)⟩
  letI : IsLocalRing (stableEnd S) := stableEnd.isLocalRing hS
  have ha : (∑ j ∈ s, a j) = 1 := by
    apply Subtype.ext
    change (stableEnd S).subtype (∑ j ∈ s, a j) = LinearMap.id
    rw [map_sum]
    exact hsum
  have hu : IsUnit (∑ j ∈ s, a j) := ha ▸ isUnit_one
  obtain ⟨j, _, hj⟩ := local_exists_isUnit_of_sum s a hu
  obtain ⟨u, hu⟩ := hj
  let b : stableEnd S := ↑u⁻¹
  have hb : b * a j = 1 := by
    rw [← hu]
    exact Units.inv_mul u
  let g' : W →ₗ[K] V := (b : Module.End K V).comp (g j)
  apply iso_of_retraction hS.1 hT (f j) g' (hf j)
  · intro i x hx
    exact b.property i (g j x) (hg j i x hx)
  · intro x
    exact congrArg (fun c : stableEnd S => (c : Module.End K V) x) hb

/-- The finite direct sum of copies, expressed as a finite product. -/
def copies {W : Type*} [AddCommGroup W] [Module K W]
    (J : Type*) (T : ι → Submodule K W) : ι → Submodule K (J → W) :=
  fun i => Submodule.pi Set.univ (fun _ : J => T i)

/-- Special Krull–Schmidt descent in its direct-summand form: a nonzero
indecomposable retract of finitely many copies of one indecomposable
configuration is isomorphic to that configuration. -/
theorem iso_of_retract_copies [Finite K] [FiniteDimensional K V]
    {W J : Type*} [AddCommGroup W] [Module K W] [Fintype J]
    {S : ι → Submodule K V} {T : ι → Submodule K W}
    (hS : Indecomposable S ⊤) (hT : Indecomposable T ⊤)
    (f : V →ₗ[K] (J → W)) (g : (J → W) →ₗ[K] V)
    (hf : Preserves S (copies J T) f) (hg : Preserves (copies J T) S g)
    (hgf : ∀ x, g (f x) = x) : ConfigurationIso S T := by
  classical
  apply iso_of_sum_factorizations hS hT Finset.univ
    (fun j => (LinearMap.proj j).comp f)
    (fun j => g.comp (LinearMap.single K (fun _ : J => W) j))
  · intro j i x hx
    have hh := hf i x hx
    exact hh j (Set.mem_univ j)
  · intro j i x hx
    apply hg i
    intro k _
    by_cases hk : k = j
    · subst k
      simpa using hx
    · simp [LinearMap.single_apply, Pi.single_eq_of_ne hk]
  · ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [← map_sum]
    simpa only [LinearMap.single_apply, Finset.univ_sum_single, LinearMap.id_apply] using hgf x

end UploadBroadcast.TaskDecomposition
