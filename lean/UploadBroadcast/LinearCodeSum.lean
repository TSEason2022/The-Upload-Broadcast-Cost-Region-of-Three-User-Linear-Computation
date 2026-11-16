import UploadBroadcast.PassiveLinearCode
import UploadBroadcast.CodeAlphabet
import UploadBroadcast.BlockLinearCode

namespace UploadBroadcast
variable {K F V : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup V] [Module K V]

def sourceProdEquiv (L : ℕ) : Source K (F × V) L ≃ₗ[K] (Source K F L × Source K V L) where
  toFun x := (x.comp (LinearMap.inl K F V),x.comp (LinearMap.inr K F V))
  invFun x := x.1.coprod x.2
  left_inv x := by
    apply LinearMap.ext
    intro z
    change x (z.1,0) + x (0,z.2) = x z
    rw [← map_add]
    simp
  right_inv x := by ext z j <;> simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def observedProdEquiv (L : ℕ) (A : Submodule K F) (B : Submodule K V) :
    Source K (A.prod B) L ≃ₗ[K] (Source K A L × Source K B L) :=
  (LinearEquiv.arrowCongr (Profile.submoduleProdEquiv A B)
    (LinearEquiv.refl K (Fin L → K))).trans (sourceProdEquiv L)

theorem observedProd_observe {L : ℕ} (A : Submodule K F) (B : Submodule K V)
    (x : Source K (F × V) L) :
    observedProdEquiv L A B (observe K (F × V) (A.prod B) x) =
      (observe K F A (sourceProdEquiv L x).1,observe K V B (sourceProdEquiv L x).2) := by
  rfl

def concatEquiv (a b : ℕ) : ((Fin a → K) × (Fin b → K)) ≃ₗ[K] (Fin (a+b) → K) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) K K).symm.trans
    (LinearEquiv.funCongrLeft K K finSumFinEquiv.symm)

private def shuffle {A B C D : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    [AddCommGroup D] [Module K D] : ((A × B) × (C × D)) →ₗ[K] ((A × C) × (B × D)) where
  toFun x := ((x.1.1,x.2.1),(x.1.2,x.2.2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def splitMessages (a b : Three → ℕ) :
    (∀ i, Fin (a i+b i) → K) →ₗ[K] ((∀ i, Fin (a i) → K) × (∀ i, Fin (b i) → K)) where
  toFun m := (fun i => ((concatEquiv (a i) (b i)).symm (m i)).1,
    fun i => ((concatEquiv (a i) (b i)).symm (m i)).2)
  map_add' x y := by ext i j <;> simp
  map_smul' c x := by ext i j <;> simp

namespace Task.LinearCode
variable {T : Task K F} {R : Task K V} {L : ℕ} {a b : Three → ℕ} {s t : ℕ}

/-- Direct-sum linear coding uses the same field and blocklength. -/
def directSum (c : T.LinearCode L a s) (d : R.LinearCode L b t) :
    (Profile.directSum T R).LinearCode L (fun i => a i+b i) (s+t) where
  encode i := (concatEquiv (a i) (b i)).toLinearMap.comp
    (((c.encode i).prodMap (d.encode i)).comp (observedProdEquiv L (T.A i) (R.A i)).toLinearMap)
  broadcast := (concatEquiv s t).toLinearMap.comp
    ((c.broadcast.prodMap d.broadcast).comp (splitMessages a b))
  decode i := (observedProdEquiv L (T.U i) (R.U i)).symm.toLinearMap.comp
    (((c.decode i).prodMap (d.decode i)).comp (shuffle.comp
      ((concatEquiv s t).symm.toLinearMap.prodMap
        (observedProdEquiv L (T.A i) (R.A i)).toLinearMap)))
  zero_error x i := by
    apply (observedProdEquiv L (T.U i) (R.U i)).injective
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
      LinearMap.prodMap_apply,LinearEquiv.symm_apply_apply,observedProd_observe,
      splitMessages,shuffle,Profile.directSum]
    simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearEquiv.symm_apply_apply]
    change (c.decode i (c.broadcast (fun j => c.encode j
      (observe K F (T.A j) (sourceProdEquiv L x).1)),
      observe K F (T.A i) (sourceProdEquiv L x).1),
      d.decode i (d.broadcast (fun j => d.encode j
      (observe K V (R.A j) (sourceProdEquiv L x).2)),
      observe K V (R.A i) (sourceProdEquiv L x).2)) = _
    rw [c.zero_error,d.zero_error]

variable [Finite K] [FiniteDimensional K F] [FiniteDimensional K V]

/-- Nominal coordinate bounds for the composed code, without assuming that
individual encoders use every nominal coordinate. -/
theorem directSum_cost_bounds (c : T.LinearCode L a s) (d : R.LinearCode L b t) :
    (c.directSum d).toCode.uploadCost ≤ (∑ i, ((a i+b i : ℕ) : ℝ)) / L ∧
    (c.directSum d).toCode.broadcastCost ≤ ((s+t : ℕ) : ℝ) / L := by
  rw [uploadCost_eq_rank,broadcastCost_eq_rank]
  constructor
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro i _
    exact_mod_cast (LinearMap.range ((c.directSum d).encode i)).finrank_le.trans_eq (by simp)
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (LinearMap.range (c.directSum d).transmittedLinear).finrank_le.trans_eq (by simp)

/-- Repeat a scalar linear code independently on two instances. -/
def repeatScalar (c : T.LinearCode 1 a s) : T.LinearCode 2 (fun i => a i+a i) (s+s) :=
  (c.directSum c).toBlockDouble

theorem repeatScalar_cost_bounds (c : T.LinearCode 1 a s) :
    c.repeatScalar.toCode.uploadCost ≤ ∑ i, (a i : ℝ) ∧
    c.repeatScalar.toCode.broadcastCost ≤ s := by
  have h := c.directSum_cost_bounds c
  simp only [Nat.cast_one,div_one,Nat.cast_add] at h
  change (c.directSum c).toBlockDouble.toCode.uploadCost ≤ _ ∧
    (c.directSum c).toBlockDouble.toCode.broadcastCost ≤ _
  rw [toBlockDouble_uploadCost,toBlockDouble_broadcastCost]
  constructor
  · have hh := div_le_div_of_nonneg_right h.1 (by norm_num : (0:ℝ) ≤ 2)
    simpa only [Finset.sum_add_distrib,add_self_div_two] using hh
  · exact (div_le_div_of_nonneg_right h.2 (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)

end Task.LinearCode
end UploadBroadcast
