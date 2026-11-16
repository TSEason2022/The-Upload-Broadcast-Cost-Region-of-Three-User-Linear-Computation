import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Arithmetic of the manuscript's affine E6 Tits form

These are unconditional arithmetic lemmas, not a formalization of Kac's theorem,
quiver indecomposability, residual decomposition, or the communication theorem.
All dimensions are integers: the polynomial identity must not be interpreted
as an inequality inside the finite source field.
-/
namespace UploadBroadcast.Structural

def tits (f u₁ u₂ u₃ a₁ a₂ a₃ : ℤ) : ℤ :=
  f ^ 2 - f * (u₁ + u₂ + u₃) +
    (a₁ ^ 2 - a₁ * u₁ + u₁ ^ 2) +
    (a₂ ^ 2 - a₂ * u₂ + u₂ ^ 2) +
    (a₃ ^ 2 - a₃ * u₃ + u₃ ^ 2)

def excess (f a₁ a₂ a₃ : ℤ) : ℤ := a₁ + a₂ + a₃ - f

/-- Denominator-free version of equation `tits-squares`. -/
theorem tits_squares (f u₁ u₂ u₃ a₁ a₂ a₃ : ℤ) :
    4 * tits f u₁ u₂ u₃ a₁ a₂ a₃ =
      (2 * u₁ - f - a₁) ^ 2 + (2 * u₂ - f - a₂) ^ 2 +
      (2 * u₃ - f - a₃) ^ 2 + (a₁ - a₂) ^ 2 +
      (a₁ - a₃) ^ 2 + (a₂ - a₃) ^ 2 + excess f a₁ a₂ a₃ ^ 2 := by
  unfold tits excess
  ring

/-- The dimension-side excess bound requires a separate proof of `tits ≤ 1`. -/
theorem excess_sq_le_four_tits (f u₁ u₂ u₃ a₁ a₂ a₃ : ℤ) :
    excess f a₁ a₂ a₃ ^ 2 ≤ 4 * tits f u₁ u₂ u₃ a₁ a₂ a₃ := by
  have h := tits_squares f u₁ u₂ u₃ a₁ a₂ a₃
  nlinarith [sq_nonneg (2 * u₁ - f - a₁), sq_nonneg (2 * u₂ - f - a₂),
    sq_nonneg (2 * u₃ - f - a₃), sq_nonneg (a₁ - a₂),
    sq_nonneg (a₁ - a₃), sq_nonneg (a₂ - a₃)]

theorem positive_excess_one_or_two (f u₁ u₂ u₃ a₁ a₂ a₃ : ℤ)
    (hq : tits f u₁ u₂ u₃ a₁ a₂ a₃ ≤ 1)
    (hpos : 0 < excess f a₁ a₂ a₃) :
    excess f a₁ a₂ a₃ = 1 ∨ excess f a₁ a₂ a₃ = 2 := by
  have h := excess_sq_le_four_tits f u₁ u₂ u₃ a₁ a₂ a₃
  have hupper : excess f a₁ a₂ a₃ ≤ 2 := by nlinarith
  omega

/-- Imaginary-root excess vanishes once `tits = 0` has been established. -/
theorem zero_tits_zero_excess (f u₁ u₂ u₃ a₁ a₂ a₃ : ℤ)
    (hq : tits f u₁ u₂ u₃ a₁ a₂ a₃ = 0) :
    excess f a₁ a₂ a₃ = 0 := by
  have h := excess_sq_le_four_tits f u₁ u₂ u₃ a₁ a₂ a₃
  nlinarith [sq_nonneg (excess f a₁ a₂ a₃)]

/-- Equality in the excess-two bound forces all six remaining squares to vanish. -/
theorem excess_two_rigidity (f u₁ u₂ u₃ a₁ a₂ a₃ : ℤ)
    (hq : tits f u₁ u₂ u₃ a₁ a₂ a₃ = 1)
    (hchi : excess f a₁ a₂ a₃ = 2) :
    a₁ = a₂ ∧ a₁ = a₃ ∧ 2 * u₁ = f + a₁ ∧
      2 * u₂ = f + a₂ ∧ 2 * u₃ = f + a₃ := by
  have h := tits_squares f u₁ u₂ u₃ a₁ a₂ a₃
  rw [hq, hchi] at h
  have h₁ := sq_nonneg (2 * u₁ - f - a₁)
  have h₂ := sq_nonneg (2 * u₂ - f - a₂)
  have h₃ := sq_nonneg (2 * u₃ - f - a₃)
  have h₄ := sq_nonneg (a₁ - a₂)
  have h₅ := sq_nonneg (a₁ - a₃)
  have h₆ := sq_nonneg (a₂ - a₃)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- A useful first step of the real-root residue enumeration. -/
theorem excess_one_near_dimensions (f u₁ u₂ u₃ a₁ a₂ a₃ : ℤ)
    (hq : tits f u₁ u₂ u₃ a₁ a₂ a₃ = 1)
    (hchi : excess f a₁ a₂ a₃ = 1) :
    -1 ≤ a₁ - a₂ ∧ a₁ - a₂ ≤ 1 ∧
      -1 ≤ a₁ - a₃ ∧ a₁ - a₃ ≤ 1 ∧
      -1 ≤ a₂ - a₃ ∧ a₂ - a₃ ≤ 1 ∧
      -1 ≤ 2 * u₁ - f - a₁ ∧ 2 * u₁ - f - a₁ ≤ 1 ∧
      -1 ≤ 2 * u₂ - f - a₂ ∧ 2 * u₂ - f - a₂ ≤ 1 ∧
      -1 ≤ 2 * u₃ - f - a₃ ∧ 2 * u₃ - f - a₃ ≤ 1 := by
  have h := tits_squares f u₁ u₂ u₃ a₁ a₂ a₃
  rw [hq, hchi] at h
  have h₁ := sq_nonneg (2 * u₁ - f - a₁)
  have h₂ := sq_nonneg (2 * u₂ - f - a₂)
  have h₃ := sq_nonneg (2 * u₃ - f - a₃)
  have h₄ := sq_nonneg (a₁ - a₂)
  have h₅ := sq_nonneg (a₁ - a₃)
  have h₆ := sq_nonneg (a₂ - a₃)
  have bound (x : ℤ) (hx : x ^ 2 ≤ 3) : -1 ≤ x ∧ x ≤ 1 := by
    constructor <;> nlinarith
  have b₁ := bound (2 * u₁ - f - a₁) (by nlinarith)
  have b₂ := bound (2 * u₂ - f - a₂) (by nlinarith)
  have b₃ := bound (2 * u₃ - f - a₃) (by nlinarith)
  have b₄ := bound (a₁ - a₂) (by nlinarith)
  have b₅ := bound (a₁ - a₃) (by nlinarith)
  have b₆ := bound (a₂ - a₃) (by nlinarith)
  exact ⟨b₄.1, b₄.2, b₅.1, b₅.2, b₆.1, b₆.2,
    b₁.1, b₁.2, b₂.1, b₂.2, b₃.1, b₃.2⟩

end UploadBroadcast.Structural
