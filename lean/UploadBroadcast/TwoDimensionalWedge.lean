import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Push

/-!
# A nonzero cross wedge from two jointly separating families

No lower bound on the field cardinality is used. The families need not themselves
be linearly parameterized; only their values are linear functionals.
-/
namespace UploadBroadcast.TwoDimensionalWedge

variable {K V X Y : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- If two nonzero families jointly separate a space of dimension at least two,
one functional from each family has a nonzero two-vector determinant. -/
theorem exists_cross_wedge (f : X → V →ₗ[K] K) (g : Y → V →ₗ[K] K)
    (hf : ∃ x, f x ≠ 0) (hg : ∃ y, g y ≠ 0)
    (hsep : ∀ v, (∀ x, f x v = 0) → (∀ y, g y v = 0) → v = 0)
    (hdim : 2 ≤ Module.finrank K V) :
    ∃ x y r w, g y r * f x w - g y w * f x r ≠ 0 := by
  classical
  by_contra! hdet
  obtain ⟨x₀, hx₀⟩ := hf
  obtain ⟨y₀, hy₀⟩ := hg
  have hxf : ∃ w, f x₀ w ≠ 0 := by
    by_contra! hh
    apply hx₀
    ext w
    exact hh w
  have hyg : ∃ r, g y₀ r ≠ 0 := by
    by_contra! hh
    apply hy₀
    ext r
    exact hh r
  obtain ⟨w₀, hw₀⟩ := hxf
  obtain ⟨r₀, hr₀⟩ := hyg
  have hk (v : V) (hv : f x₀ v = 0) : v = 0 := by
    have hgv (y : Y) : g y v = 0 := by
      have hh := hdet x₀ y v w₀
      rw [hv, mul_zero, sub_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_right hw₀
    have hfv (x : X) : f x v = 0 := by
      have hh := hdet x y₀ r₀ v
      rw [hgv y₀, zero_mul, sub_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left hr₀
    exact hsep v hfv hgv
  have hinj : Function.Injective (f x₀) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro v hv
    exact hk v hv
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_self] at hle
  exact (by decide : ¬ (2 ≤ 1)) (hdim.trans hle)

/-- The same result with the conventional row-ordered determinant. -/
theorem exists_cross_determinant (f : X → V →ₗ[K] K) (g : Y → V →ₗ[K] K)
    (hf : ∃ x, f x ≠ 0) (hg : ∃ y, g y ≠ 0)
    (hsep : ∀ v, (∀ x, f x v = 0) → (∀ y, g y v = 0) → v = 0)
    (hdim : 2 ≤ Module.finrank K V) :
    ∃ x y r w, f x r * g y w - f x w * g y r ≠ 0 := by
  obtain ⟨x, y, r, w, h⟩ := exists_cross_wedge f g hf hg hsep hdim
  exact ⟨x, y, w, r, by simpa only [mul_comm] using h⟩

/-- Exact two-dimensional specialization for the R2 relation space. -/
theorem exists_cross_wedge_finrank_two (f : X → V →ₗ[K] K) (g : Y → V →ₗ[K] K)
    (hf : ∃ x, f x ≠ 0) (hg : ∃ y, g y ≠ 0)
    (hsep : ∀ v, (∀ x, f x v = 0) → (∀ y, g y v = 0) → v = 0)
    (hdim : Module.finrank K V = 2) :
    ∃ x y r w, g y r * f x w - g y w * f x r ≠ 0 :=
  exists_cross_wedge f g hf hg hsep hdim.ge

/-- Direct interface for the linear restriction maps used by the relay construction. -/
theorem exists_cross_wedge_of_ne_zero [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    (f : X →ₗ[K] (V →ₗ[K] K)) (g : Y →ₗ[K] (V →ₗ[K] K)) (hf : f ≠ 0) (hg : g ≠ 0)
    (hsep : ∀ v, (∀ x, f x v = 0) → (∀ y, g y v = 0) → v = 0)
    (hdim : 2 ≤ Module.finrank K V) :
    ∃ x y r w, g y r * f x w - g y w * f x r ≠ 0 := by
  apply exists_cross_wedge f g _ _ hsep hdim
  · by_contra! h
    apply hf
    apply LinearMap.ext
    intro x
    exact h x
  · by_contra! h
    apply hg
    apply LinearMap.ext
    intro y
    exact h y

end UploadBroadcast.TwoDimensionalWedge
