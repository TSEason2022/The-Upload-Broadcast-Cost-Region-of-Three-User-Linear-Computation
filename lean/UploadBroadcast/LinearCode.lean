import UploadBroadcast.Model
import UploadBroadcast.LinearCosts
import Mathlib.LinearAlgebra.Pi

/-! A genuinely linear specialization of the operational code model, with
rank formulas for the attained alphabets. Nominal transmission lengths do not
replace actual range ranks. -/
namespace UploadBroadcast
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Observation as a linear map on the block-source space. -/
def observeLinear (L : ℕ) (A : Submodule K F) :
    Source K F L →ₗ[K] (A →ₗ[K] (Fin L → K)) where
  toFun := observe K F A
  map_add' _ _ := by ext a; rfl
  map_smul' _ _ := by ext a; rfl

namespace Task
variable (T : Task K F)

structure LinearCode (L : ℕ) (r : Three → ℕ) (s : ℕ) where
  encode : ∀ i, (T.A i →ₗ[K] (Fin L → K)) →ₗ[K] (Fin (r i) → K)
  broadcast : (∀ i, Fin (r i) → K) →ₗ[K] (Fin s → K)
  decode : ∀ i, ((Fin s → K) × (T.A i →ₗ[K] (Fin L → K))) →ₗ[K]
    (T.U i →ₗ[K] (Fin L → K))
  zero_error : ∀ (x : Source K F L) i,
    decode i (broadcast (fun j => encode j (observe K F (T.A j) x)),
      observe K F (T.A i) x) = observe K F (T.U i) x

namespace LinearCode
variable {T} {L : ℕ} {r : Three → ℕ} {s : ℕ}

def toCode (c : T.LinearCode L r s) : T.Code L (fun i => Fin (r i) → K) (Fin s → K) where
  encode i := c.encode i
  broadcast := c.broadcast
  decode i b a := c.decode i (b,a)
  zero_error := c.zero_error

def transmittedLinear (c : T.LinearCode L r s) : Source K F L →ₗ[K] (Fin s → K) :=
  c.broadcast.comp (LinearMap.pi fun i => (c.encode i).comp (observeLinear L (T.A i)))

theorem transmittedLinear_eq (c : T.LinearCode L r s) :
    (c.transmittedLinear : Source K F L → (Fin s → K)) = c.toCode.transmitted := rfl

variable [Finite K] [FiniteDimensional K F]

theorem uploadCost_eq_rank (c : T.LinearCode L r s) :
    c.toCode.uploadCost = (∑ i, (Module.finrank K (LinearMap.range (c.encode i)) : ℝ)) / L := by
  unfold Code.uploadCost
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact linear_alphabet_log (c.encode i)

theorem broadcastCost_eq_rank (c : T.LinearCode L r s) :
    c.toCode.broadcastCost = (Module.finrank K (LinearMap.range c.transmittedLinear) : ℝ) / L := by
  unfold Code.broadcastCost
  rw [← c.transmittedLinear_eq, linear_alphabet_log]

theorem scalar_costs_integral (c : T.LinearCode 1 r s) :
    (∃ u : ℤ, c.toCode.uploadCost = u) ∧ (∃ d : ℤ, c.toCode.broadcastCost = d) := by
  constructor
  · refine ⟨∑ i, (Module.finrank K (LinearMap.range (c.encode i)) : ℤ), ?_⟩
    simp [uploadCost_eq_rank]
  · refine ⟨(Module.finrank K (LinearMap.range c.transmittedLinear) : ℤ), ?_⟩
    simp [broadcastCost_eq_rank]

/-- A nonintegral corner cannot be attained by any scalar linear code,
regardless of redundant nominal message coordinates. -/
theorem no_scalar_at_nonintegral_corner (u d : ℝ)
    (hnon : (¬ ∃ z : ℤ, u = z) ∨ (¬ ∃ z : ℤ, d = z))
    (c : T.LinearCode 1 r s)
    (hu : c.toCode.uploadCost = u) (hd : c.toCode.broadcastCost = d) : False := by
  obtain ⟨hU,hD⟩ := c.scalar_costs_integral
  rcases hnon with h | h
  · exact h (hu ▸ hU)
  · exact h (hd ▸ hD)

end LinearCode
end Task
end UploadBroadcast
