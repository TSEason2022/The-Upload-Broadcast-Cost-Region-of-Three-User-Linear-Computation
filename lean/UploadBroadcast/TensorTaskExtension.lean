import UploadBroadcast.TaskComponentBridge

/-! The tensor-at-every-vertex representation is explicitly isomorphic to the
configuration obtained by extending each actual nested subspace. -/
noncomputable section
open scoped TensorProduct
namespace UploadBroadcast.TaskDecomposition
open QuiverRepresentation
variable {K L V W : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Tensoring an injective vector-space map stays injective over any extension
field: extend an actual linear left inverse. No finite-degree hypothesis. -/
theorem baseChange_injective_arbitrary (f : V →ₗ[K] W) (hf : Function.Injective f) :
    Function.Injective (f.baseChange L) := by
  obtain ⟨g,hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  have he : (g.baseChange L).comp (f.baseChange L) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp,hg,LinearMap.baseChange_id]
  exact Function.LeftInverse.injective (fun x => LinearMap.congr_fun he x)

/-- Each extended subspace really is the tensor product of the original
subspace, with the inclusion equal to the tensor-extended inclusion. -/
def subspaceTensorEquiv (P : Submodule K V) : (L ⊗[K] P) ≃ₗ[L] P.baseChange L :=
  (LinearEquiv.ofInjective (P.subtype.baseChange L)
    (baseChange_injective_arbitrary P.subtype Subtype.val_injective)).trans
    (LinearEquiv.ofEq _ _ (baseChange_eq_range P).symm)

@[simp] theorem subspaceTensorEquiv_coe (P : Submodule K V) (x : L ⊗[K] P) :
    (subspaceTensorEquiv P x : L ⊗[K] V) = P.subtype.baseChange L x := rfl

section Tasks
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  (T : Task K V) (L : Type*) [Field L] [Algebra K L]

/-- Scalar extension of the representation in the literal vertexwise sense:
every vertex module is tensored, and every arrow is tensored. -/
def Task.tensorRep : Rep L inwardE6 where
  space v := L ⊗[K] T.toRep.space v
  add _ := inferInstance
  module _ := inferInstance
  arrow e := (T.toRep.arrow e).baseChange L

/-- Explicit arrow-commuting isomorphism from the tensor-at-every-vertex
representation to the six actual extended subspaces. -/
def Task.tensorRepIso : Iso (T.tensorRep L) (T.extend (L := L)).toRep where
  map
    | .center => LinearEquiv.refl L _
    | .middle i => subspaceTensorEquiv (T.U i)
    | .outer i => subspaceTensorEquiv (T.A i)
  comm e := by
    cases e with
    | inner i => rfl
    | outer i =>
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change (T.U i).subtype.baseChange L
        ((Submodule.inclusion (T.nested i)).baseChange L x) =
        (T.A i).subtype.baseChange L x
      change L ⊗[K] ↥(T.A i) at x
      induction x with
      | zero => simp
      | tmul a x => rfl
      | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

/-- Exact identification of the two absolute-indecomposability formulations. -/
theorem Task.tensorRep_indec_iff :
    QuiverRepresentation.Indecomposable (T.tensorRep L) ↔
      QuiverRepresentation.Indecomposable (T.extend (L := L)).toRep :=
  by
    constructor
    · intro hi
      refine ⟨?_,?_⟩
      · intro hz
        apply hi.1
        intro v x
        apply ((T.tensorRepIso L).map v).injective
        simpa only [map_zero] using hz v ((T.tensorRepIso L).map v x)
      · intro A B h
        exact hi.2 A B ((T.tensorRepIso L).trans h)
    · intro hi
      refine ⟨?_,?_⟩
      · intro hz
        apply hi.1
        intro v x
        apply ((T.tensorRepIso L).symm.map v).injective
        simpa only [map_zero] using hz v ((T.tensorRepIso L).symm.map v x)
      · intro A B h
        exact hi.2 A B ((T.tensorRepIso L).symm.trans h)

end Tasks
end UploadBroadcast.TaskDecomposition
