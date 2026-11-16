import UploadBroadcast.LinearCode
import UploadBroadcast.ScalarPaperEndpoints

namespace UploadBroadcast
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

def sourceDoubleBlockEquiv : Source K F 2 ≃ₗ[K] Source K (F × F) 1 :=
  sourceDoubleEquiv.trans sourceOneEquiv.symm

def observedDoubleBlockEquiv (A : Submodule K F) :
    Source K A 2 ≃ₗ[K] Source K (A.prod A) 1 :=
  (observedDoubleEquiv A).trans sourceOneEquiv.symm

theorem observedDoubleBlock_observe (A : Submodule K F) (x : Source K F 2) :
    observedDoubleBlockEquiv A (observe K F A x) =
      observe K (F × F) (A.prod A) (sourceDoubleBlockEquiv x) := by
  ext a j
  fin_cases j
  rfl

namespace Task.LinearCode
variable {T : Task K F} {r : Three → ℕ} {s : ℕ}

/-- Same-field scalar coding on two task copies is a genuine length-two
linear code on the original task. No extension field or alphabet surrogate. -/
def toBlockDouble (c : (Profile.directSum T T).LinearCode 1 r s) : T.LinearCode 2 r s where
  encode i := (c.encode i).comp (observedDoubleBlockEquiv (T.A i)).toLinearMap
  broadcast := c.broadcast
  decode i := (observedDoubleBlockEquiv (T.U i)).symm.toLinearMap.comp
    ((c.decode i).comp ((LinearMap.id : (Fin s → K) →ₗ[K] (Fin s → K)).prodMap
      (observedDoubleBlockEquiv (T.A i)).toLinearMap))
  zero_error x i := by
    apply (observedDoubleBlockEquiv (T.U i)).injective
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
      LinearMap.prodMap_apply,LinearMap.id_apply,observedDoubleBlock_observe]
    exact c.zero_error (sourceDoubleBlockEquiv x) i

theorem toBlockDouble_encode_range (c : (Profile.directSum T T).LinearCode 1 r s) (i : Three) :
    Set.range (c.toBlockDouble.encode i) = Set.range (c.encode i) := by
  change Set.range ((c.encode i) ∘ observedDoubleBlockEquiv (T.A i)) = _
  rw [Set.range_comp,EquivLike.range_eq_univ (observedDoubleBlockEquiv (T.A i)),Set.image_univ]

theorem toBlockDouble_transmitted (c : (Profile.directSum T T).LinearCode 1 r s)
    (x : Source K F 2) :
    c.toBlockDouble.toCode.transmitted x = c.toCode.transmitted (sourceDoubleBlockEquiv x) := by
  simp only [Task.Code.transmitted,toCode,toBlockDouble,LinearMap.comp_apply,
    LinearEquiv.coe_coe,observedDoubleBlock_observe]
  rfl

theorem toBlockDouble_transmitted_range (c : (Profile.directSum T T).LinearCode 1 r s) :
    Set.range c.toBlockDouble.toCode.transmitted = Set.range c.toCode.transmitted := by
  have h : c.toBlockDouble.toCode.transmitted = c.toCode.transmitted ∘ sourceDoubleBlockEquiv := by
    funext x
    exact c.toBlockDouble_transmitted x
  rw [h,Set.range_comp,EquivLike.range_eq_univ sourceDoubleBlockEquiv,Set.image_univ]

variable [Finite K] [FiniteDimensional K F]

theorem toBlockDouble_uploadCost (c : (Profile.directSum T T).LinearCode 1 r s) :
    c.toBlockDouble.toCode.uploadCost = c.toCode.uploadCost / 2 := by
  simp only [Task.Code.uploadCost,toCode,toBlockDouble_encode_range,Nat.cast_ofNat,
    Nat.cast_one,div_one]

theorem toBlockDouble_broadcastCost (c : (Profile.directSum T T).LinearCode 1 r s) :
    c.toBlockDouble.toCode.broadcastCost = c.toCode.broadcastCost / 2 := by
  simp only [Task.Code.broadcastCost,toBlockDouble_transmitted_range,Nat.cast_ofNat,
    Nat.cast_one,div_one]

end Task.LinearCode
end UploadBroadcast
