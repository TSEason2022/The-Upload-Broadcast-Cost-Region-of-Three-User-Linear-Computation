import UploadBroadcast.CodeAlphabet
import UploadBroadcast.ProfileTransport

namespace UploadBroadcast
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Coordinate product of a coefficient subspace. -/
def blockSubmodule (m : ℕ) (A : Submodule K F) : Submodule K (Fin m → F) :=
  Submodule.pi Set.univ (fun _ => A)

def blockSubmoduleEquiv (m : ℕ) (A : Submodule K F) :
    blockSubmodule m A ≃ₗ[K] (Fin m → A) where
  toFun x i := ⟨x.val i,x.property i trivial⟩
  invFun x := ⟨fun i => (x i : F),fun i _ => (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Repackage m*n source columns into m groups of n columns. -/
def sourceGroupsEquiv (m n : ℕ) : Source K F (m*n) ≃ₗ[K] (Fin m → Source K F n) where
  toFun x i :=
    { toFun := fun v j => x v (finProdFinEquiv (i,j))
      map_add' := by intros; ext j; simp
      map_smul' := by intros; ext j; simp }
  invFun x :=
    { toFun := fun v j => x (finProdFinEquiv.symm j).1 v (finProdFinEquiv.symm j).2
      map_add' := by intros; ext j; simp
      map_smul' := by intros; ext j; simp }
  left_inv x := by
    ext v j
    change x v (finProdFinEquiv (finProdFinEquiv.symm j)) = x v j
    rw [Equiv.apply_symm_apply]
  right_inv x := by
    ext i v j
    change x (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1 v
      (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 = x i v j
    rw [Equiv.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- m grouped coefficient copies with n instances are exactly mn original instances. -/
noncomputable def sourceBlockEquiv (m n : ℕ) :
    Source K F (m*n) ≃ₗ[K] Source K (Fin m → F) n :=
  (sourceGroupsEquiv m n).trans (LinearMap.lsum K (fun _ : Fin m => F) K)

noncomputable def observedBlockEquiv (m n : ℕ) (A : Submodule K F) :
    Source K A (m*n) ≃ₗ[K] Source K (blockSubmodule m A) n :=
  (sourceBlockEquiv m n).trans (LinearEquiv.arrowCongr
    (blockSubmoduleEquiv m A).symm (LinearEquiv.refl K (Fin n → K)))

theorem observedBlock_observe (m n : ℕ) (A : Submodule K F) (x : Source K F (m*n)) :
    observedBlockEquiv m n A (observe K F A x) =
      observe K (Fin m → F) (blockSubmodule m A) (sourceBlockEquiv m n x) := by
  classical
  ext a j
  simp [observedBlockEquiv,sourceBlockEquiv,sourceGroupsEquiv,blockSubmoduleEquiv,
    LinearMap.lsum_apply,observe,LinearMap.sum_apply]

namespace Task

def blockPower (T : Task K F) (m : ℕ) : Task K (Fin m → F) where
  A i := blockSubmodule m (T.A i)
  U i := blockSubmodule m (T.U i)
  side_le_signal i := Submodule.pi_mono (fun _ _ => T.side_le_signal i)
  feasible i := by
    classical
    intro x hx
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro j _
    have hm : (⨆ k, T.A k).map (LinearMap.single K (fun _ : Fin m => F) j) ≤
        ⨆ k, blockSubmodule m (T.A k) := by
      rw [Submodule.map_iSup]
      apply iSup_le
      intro k
      apply le_iSup_of_le k
      exact Submodule.map_le_iff_le_comap.mpr (Submodule.le_comap_single_pi (fun _ => T.A k))
    exact hm ⟨x j,T.feasible i (hx j trivial),rfl⟩

namespace Code
variable {T : Task K F} {m n : ℕ} {M : Three → Type*} {S : Type*}

noncomputable def flatten (c : (T.blockPower m).Code n M S) : T.Code (m*n) M S where
  encode i a := c.encode i (observedBlockEquiv m n (T.A i) a)
  broadcast := c.broadcast
  decode i b a := (observedBlockEquiv m n (T.U i)).symm
    (c.decode i b (observedBlockEquiv m n (T.A i) a))
  zero_error x i := by
    apply (observedBlockEquiv m n (T.U i)).injective
    simp only [LinearEquiv.apply_symm_apply,observedBlock_observe]
    exact c.zero_error (sourceBlockEquiv m n x) i

theorem flatten_upload_range (c : (T.blockPower m).Code n M S) (i : Three) :
    Set.range (c.flatten.encode i) = Set.range (c.encode i) := by
  change Set.range ((c.encode i) ∘ observedBlockEquiv m n (T.A i)) = _
  rw [Set.range_comp,EquivLike.range_eq_univ (observedBlockEquiv m n (T.A i)),Set.image_univ]

theorem flatten_transmitted (c : (T.blockPower m).Code n M S) :
    c.flatten.transmitted = c.transmitted ∘ sourceBlockEquiv m n := by
  funext x
  simp only [transmitted,flatten,observedBlock_observe,Function.comp_apply,blockPower]

theorem flatten_transmitted_range (c : (T.blockPower m).Code n M S) :
    Set.range c.flatten.transmitted = Set.range c.transmitted := by
  rw [flatten_transmitted,Set.range_comp,EquivLike.range_eq_univ (sourceBlockEquiv m n),Set.image_univ]

variable [Finite K] [FiniteDimensional K F]

theorem flatten_costs (c : (T.blockPower m).Code n M S) :
    c.flatten.uploadCost = c.uploadCost / m ∧ c.flatten.broadcastCost = c.broadcastCost / m := by
  constructor
  · simp only [uploadCost,flatten_upload_range,Nat.cast_mul,div_div,mul_comm]
  · simp only [broadcastCost,flatten_transmitted_range,Nat.cast_mul,div_div,mul_comm]

end Code
end Task
end UploadBroadcast
