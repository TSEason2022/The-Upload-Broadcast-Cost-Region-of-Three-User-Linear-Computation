import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

/-! Exact attainable alphabets of linear maps and their integral scalar
communication costs. These are elementary supporting claims in the proof
of the minimum-linear-blocklength statement, not a proof of achievability. -/
namespace UploadBroadcast
open Module

variable {K V W : Type*} [Field K] [Finite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]

/-- Count the actual range of a linear encoder over the original finite field. -/
theorem linear_alphabet_card (f : V →ₗ[K] W) :
    Nat.card (Set.range f) = Nat.card K ^ finrank K (LinearMap.range f) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Finite (LinearMap.range f) := Module.finite_of_finite K
  letI : Fintype (LinearMap.range f) := Fintype.ofFinite _
  change Nat.card (LinearMap.range f) = _
  simpa only [Fintype.card_eq_nat_card] using
    (Module.card_eq_pow_finrank (K := K) (V := LinearMap.range f))

/-- The logarithm of an attained linear alphabet is precisely its rank. -/
theorem linear_alphabet_log (f : V →ₗ[K] W) :
    Real.logb (Nat.card K) (Nat.card (Set.range f)) =
      (finrank K (LinearMap.range f) : ℝ) := by
  rw [linear_alphabet_card, Nat.cast_pow, Real.logb_pow]
  have hq : (1:ℝ) < Nat.card K := by
    exact_mod_cast (Finite.one_lt_card (α := K))
  rw [Real.logb_self_eq_one hq, mul_one]

/-- Scalar linear alphabet costs are integers, even if the encoder uses
redundant output coordinates. -/
theorem linear_scalar_cost_integer (f : V →ₗ[K] W) :
    ∃ z : ℤ, Real.logb (Nat.card K) (Nat.card (Set.range f)) = z := by
  refine ⟨(finrank K (LinearMap.range f) : ℤ), ?_⟩
  simpa using linear_alphabet_log f

end UploadBroadcast
