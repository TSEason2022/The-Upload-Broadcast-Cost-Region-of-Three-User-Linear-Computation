import UploadBroadcast.PassiveCode
import UploadBroadcast.LinearCode

namespace UploadBroadcast
variable {K F V : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup V] [Module K V]

def precomposeSource (L : ℕ) (f : F →ₗ[K] V) : Source K V L →ₗ[K] Source K F L where
  toFun x := x.comp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

namespace PassiveRetraction
variable {T : Task K F} {R : Task K V} (r : PassiveRetraction T R)
  {L : ℕ} {a : Three → ℕ} {b : ℕ}

/-- Passive deletion preserves linearity at exactly the original blocklength. -/
def deleteLinear (c : T.LinearCode L a b) : R.LinearCode L a b where
  encode i := (c.encode i).comp (precomposeSource L (r.sideProject i))
  broadcast := c.broadcast
  decode i := (precomposeSource L (r.signalInclude i)).comp
    ((c.decode i).comp ((LinearMap.id : (Fin b → K) →ₗ[K] (Fin b → K)).prodMap
      (precomposeSource L (r.sideProject i))))
  zero_error x i := (r.delete c.toCode).zero_error x i

/-- Restoring passive coefficients uses only linear local observations. -/
def restoreLinear (c : R.LinearCode L a b) : T.LinearCode L a b where
  encode i := (c.encode i).comp (precomposeSource L (r.sideInclude i))
  broadcast := c.broadcast
  decode i := (precomposeSource L (r.signalProject i)).comp
    ((c.decode i).comp ((LinearMap.id : (Fin b → K) →ₗ[K] (Fin b → K)).prodMap
      (precomposeSource L (r.sideInclude i)))) +
    (precomposeSource L (r.localPart i)).comp (LinearMap.snd K _ _)
  zero_error x i := (r.restore c.toCode).zero_error x i

@[simp] theorem deleteLinear_toCode (c : T.LinearCode L a b) :
    (r.deleteLinear c).toCode = r.delete c.toCode := rfl

@[simp] theorem restoreLinear_toCode (c : R.LinearCode L a b) :
    (r.restoreLinear c).toCode = r.restore c.toCode := rfl

variable [Finite K] [FiniteDimensional K F] [FiniteDimensional K V]

theorem deleteLinear_costs (c : T.LinearCode L a b) :
    (r.deleteLinear c).toCode.uploadCost ≤ c.toCode.uploadCost ∧
    (r.deleteLinear c).toCode.broadcastCost ≤ c.toCode.broadcastCost := by
  constructor
  · rw [Task.LinearCode.uploadCost_eq_rank,Task.LinearCode.uploadCost_eq_rank]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro i _
    have h : LinearMap.range ((r.deleteLinear c).encode i) ≤ LinearMap.range (c.encode i) :=
      r.delete_upload_range c.toCode i
    exact_mod_cast Submodule.finrank_mono h
  · rw [Task.LinearCode.broadcastCost_eq_rank,Task.LinearCode.broadcastCost_eq_rank]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have h : LinearMap.range (r.deleteLinear c).transmittedLinear ≤
        LinearMap.range c.transmittedLinear := r.delete_broadcast_range c.toCode
    exact_mod_cast Submodule.finrank_mono h

theorem restoreLinear_costs (c : R.LinearCode L a b) :
    (r.restoreLinear c).toCode.uploadCost ≤ c.toCode.uploadCost ∧
    (r.restoreLinear c).toCode.broadcastCost ≤ c.toCode.broadcastCost := by
  constructor
  · rw [Task.LinearCode.uploadCost_eq_rank,Task.LinearCode.uploadCost_eq_rank]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro i _
    have h : LinearMap.range ((r.restoreLinear c).encode i) ≤ LinearMap.range (c.encode i) :=
      r.restore_upload_range c.toCode i
    exact_mod_cast Submodule.finrank_mono h
  · rw [Task.LinearCode.broadcastCost_eq_rank,Task.LinearCode.broadcastCost_eq_rank]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have h : LinearMap.range (r.restoreLinear c).transmittedLinear ≤
        LinearMap.range c.transmittedLinear := r.restore_broadcast_range c.toCode
    exact_mod_cast Submodule.finrank_mono h

end PassiveRetraction
end UploadBroadcast
