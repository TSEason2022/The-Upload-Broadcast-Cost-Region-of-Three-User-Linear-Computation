import UploadBroadcast.CoboundaryExtensionClosure

/-! Concrete finite extension generation, without an assumed abelian-category
or tube decomposition theorem. -/
namespace UploadBroadcast.QuiverRepresentation
universe u
variable {K V E : Type u} [Field K] {Q : Orientation V E}

/-- The finite closure of actual representations under zero, a specified atom
class, block extensions, and actual arrow-preserving isomorphisms. -/
inductive ExtensionGenerated (C : Rep K Q → Prop) : Rep K Q → Prop where
  | zero (R : Rep K Q) (hR : IsZero R) : ExtensionGenerated C R
  | atom (R : Rep K Q) (hR : C R) : ExtensionGenerated C R
  | extension (R S : Rep K Q) (z : ArrowMaps S R)
      (hR : ExtensionGenerated C R) (hS : ExtensionGenerated C S) :
      ExtensionGenerated C (QuiverRepresentation.extension R S z)
  | iso {R S : Rep K Q} (e : Iso R S) (hR : ExtensionGenerated C R) :
      ExtensionGenerated C S

/-- A zero source has no coboundary obstruction. -/
theorem coboundary_surjective_zero_source (R S : Rep K Q) (hR : IsZero R) :
    Function.Surjective (coboundary R S) := by
  intro w
  refine ⟨0,?_⟩
  funext a
  apply LinearMap.ext
  intro x
  rw [hR _ x]
  simp

/-- A zero target has no coboundary obstruction. -/
theorem coboundary_surjective_zero_target (R S : Rep K Q) (hS : IsZero S) :
    Function.Surjective (coboundary R S) := by
  intro w
  refine ⟨0,?_⟩
  funext a
  apply LinearMap.ext
  intro x
  exact (hS _ _).trans (hS _ _).symm

/-- Pairwise vanishing between two atom classes propagates to all of their
finite extension closures. This is proved directly on the coboundary maps. -/
theorem ExtensionGenerated.coboundary_surjective {C D : Rep K Q → Prop}
    (hpair : ∀ R S, C R → D S → Function.Surjective (coboundary R S))
    {R S : Rep K Q} (hR : ExtensionGenerated C R) (hS : ExtensionGenerated D S) :
    Function.Surjective (coboundary R S) := by
  induction hR with
  | zero R hzero => exact coboundary_surjective_zero_source R S hzero
  | atom R hatom =>
    induction hS with
    | zero S hzero => exact coboundary_surjective_zero_target R S hzero
    | atom S hS => exact hpair R S hatom hS
    | extension A B z _ _ ihA ihB => exact coboundary_surjective_extension_target R A B z ihA ihB
    | iso e _ ih => exact coboundary_surjective_iso_target e ih
  | extension A B z _ _ ihA ihB => exact coboundary_surjective_extension_source A B S z ihA ihB
  | iso e _ ih => exact coboundary_surjective_iso_source e ih

/-- Enlarging an atom class enlarges its actual finite extension closure. -/
theorem ExtensionGenerated.mono {C D : Rep K Q → Prop}
    (hCD : ∀ R, C R → D R) {R : Rep K Q} (hR : ExtensionGenerated C R) :
    ExtensionGenerated D R := by
  induction hR with
  | zero R hz => exact .zero R hz
  | atom R hc => exact .atom R (hCD R hc)
  | extension R S z _ _ ihR ihS => exact .extension R S z ihR ihS
  | iso e _ ih => exact .iso e ih

/-- A concrete zero representation in the same universe. -/
def zeroRepresentation : Rep K Q where
  space _ := Fin 0 → K
  arrow _ := 0

theorem zeroRepresentation_isZero : IsZero (zeroRepresentation (K:=K) (Q:=Q)) := by
  intro v x
  funext i
  exact Fin.elim0 i

/-- An actual zero summand can be removed on the right. -/
def isoProdZeroRight (R S : Rep K Q) (hS : IsZero S) : Iso (R.prod S) R where
  map v :=
    { toFun := fun x => x.1
      invFun := fun x => (x,0)
      left_inv := fun x => Prod.ext rfl (hS v x.2).symm
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  comm _ := rfl

/-- An actual zero summand can be removed on the left. -/
def isoProdZeroLeft (R S : Rep K Q) (hR : IsZero R) : Iso (R.prod S) S where
  map v :=
    { toFun := fun x => x.2
      invFun := fun x => (0,x)
      left_inv := fun x => Prod.ext (hR v x.1).symm rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  comm _ := rfl

end UploadBroadcast.QuiverRepresentation
