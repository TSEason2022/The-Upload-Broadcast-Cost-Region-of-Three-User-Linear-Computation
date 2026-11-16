import UploadBroadcast.TaskDecomposition
import Mathlib.LinearAlgebra.Projection

/-! # Indecomposability from stable idempotents over any field -/
namespace UploadBroadcast.TaskDecomposition
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A nonzero configuration is indecomposable if all its stable projections
are trivial. No finiteness assumption on the field or ambient space is needed. -/
theorem indecomposable_of_projection_eq_zero_or_id
    {S : ι → Submodule K V} (hne : (⊤ : Submodule K V) ≠ ⊥)
    (h : ∀ f : V →ₗ[K] V, Stable S f → (∀ x, f (f x) = f x) →
      f = 0 ∨ f = LinearMap.id) : Indecomposable S ⊤ := by
  classical
  refine ⟨hne, ?_⟩
  intro P Q hs
  have hc : IsCompl P Q := ⟨hs.disjoint, codisjoint_iff.mpr hs.sup_eq⟩
  let g : V →ₗ[K] P := P.linearProjOfIsCompl Q hc
  let f : V →ₗ[K] V := P.subtype.comp g
  have hl (x : P) : g x = x := Submodule.linearProjOfIsCompl_apply_left hc x
  have hr (x : V) (hx : x ∈ Q) : g x = 0 :=
    Submodule.linearProjOfIsCompl_apply_right' hc x hx
  have hf : Stable S f := by
    intro i x hx
    have hh : x ∈ (S i ⊓ P) ⊔ (S i ⊓ Q) := by
      rw [← hs.compatible i]
      exact ⟨hx, Submodule.mem_top⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hh
    change ((g (y + z) : P) : V) ∈ S i
    rw [map_add, hr z hz.2, add_zero]
    have hy' := hl (⟨y, hy.2⟩ : P)
    change g y = (⟨y, hy.2⟩ : P) at hy'
    rw [hy']
    exact hy.1
  have hi (x : V) : f (f x) = f x := by
    change ((g (g x) : P) : V) = ((g x : P) : V)
    rw [hl]
  obtain hz | ho := h f hf hi
  · left
    apply eq_bot_iff.mpr
    intro x hx
    have he : f x = x := congrArg Subtype.val (hl (⟨x, hx⟩ : P))
    rw [hz] at he
    exact he.symm
  · right
    apply eq_bot_iff.mpr
    intro x hx
    have he : f x = 0 := congrArg Subtype.val (hr x hx)
    rw [ho] at he
    exact he

/-- Characterization by stable idempotent endomorphisms. -/
theorem indecomposable_iff_projection_eq_zero_or_id
    {S : ι → Submodule K V} :
    Indecomposable S ⊤ ↔ (⊤ : Submodule K V) ≠ ⊥ ∧
      ∀ f : V →ₗ[K] V, Stable S f → (∀ x, f (f x) = f x) →
        f = 0 ∨ f = LinearMap.id := by
  constructor
  · intro h
    exact ⟨h.1, h.projection_eq_zero_or_id⟩
  · rintro ⟨hne, h⟩
    exact indecomposable_of_projection_eq_zero_or_id hne h

end UploadBroadcast.TaskDecomposition
