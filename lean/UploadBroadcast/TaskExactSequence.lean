import UploadBroadcast.SemistableMorphisms

/-! The actual pointwise exact sequence of an induced task and its quotient. -/
namespace UploadBroadcast.TaskDecomposition
open QuiverRepresentation
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

/-- Inclusion of a designated space intersected with an actual subobject. -/
def restrictedSubtype (A P : Submodule K V) : A.comap P.subtype →ₗ[K] A where
  toFun x := ⟨x.val.val,x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Quotient map on one actual designated space. -/
def restrictedQuotient (A P : Submodule K V) : A →ₗ[K] A.map P.mkQ where
  toFun x := ⟨P.mkQ x.val,⟨x.val,x.property,rfl⟩⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem restrictedSubtype_injective (A P : Submodule K V) :
    Function.Injective (restrictedSubtype A P) := by
  intro x y h
  have hh : x.val.val=y.val.val := congrArg (fun z : A => z.val) h
  exact Subtype.ext (Subtype.ext hh)

theorem restrictedQuotient_surjective (A P : Submodule K V) :
    Function.Surjective (restrictedQuotient A P) := by
  intro q
  obtain ⟨a,ha,he⟩ := q.property
  exact ⟨⟨a,ha⟩,Subtype.ext he⟩

theorem restrictedQuotient_exact (A P : Submodule K V) :
    LinearMap.ker (restrictedQuotient A P)=LinearMap.range (restrictedSubtype A P) := by
  ext a
  constructor
  · intro ha
    have hz : P.mkQ a.val=0 := congrArg Subtype.val ha
    have hp : a.val∈P := (Submodule.Quotient.mk_eq_zero P).mp hz
    exact ⟨⟨⟨a.val,hp⟩,a.property⟩,rfl⟩
  · rintro ⟨b,rfl⟩
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero P).mpr b.val.property

/-- The induced-subobject inclusion at all seven actual quiver vertices. -/
def Task.componentInclusion (T : Task K V) (P : Submodule K V) :
    Hom (T.onComponent P).toRep T.toRep where
  map
    | .center => P.subtype
    | .middle i => restrictedSubtype (T.U i) P
    | .outer i => restrictedSubtype (T.A i) P
  comm e := by cases e <;> rfl

/-- The quotient projection at all seven actual quiver vertices. -/
def Task.quotientProjection (T : Task K V) (P : Submodule K V) :
    Hom T.toRep (T.quotientBy P).toRep where
  map
    | .center => P.mkQ
    | .middle i => restrictedQuotient (T.U i) P
    | .outer i => restrictedQuotient (T.A i) P
  comm e := by cases e <;> rfl

theorem Task.componentInclusion_injective (T : Task K V) (P : Submodule K V)
    (v : E6Vertex) : Function.Injective ((T.componentInclusion P).map v) := by
  cases v with
  | center => exact Subtype.val_injective
  | middle i => exact restrictedSubtype_injective (T.U i) P
  | outer i => exact restrictedSubtype_injective (T.A i) P

theorem Task.quotientProjection_surjective (T : Task K V) (P : Submodule K V)
    (v : E6Vertex) : Function.Surjective ((T.quotientProjection P).map v) := by
  cases v with
  | center => exact Submodule.mkQ_surjective P
  | middle i => exact restrictedQuotient_surjective (T.U i) P
  | outer i => exact restrictedQuotient_surjective (T.A i) P

/-- The task quotient is genuinely exact at every quiver vertex, not just
at the ambient center or at the level of its dimension vector. -/
theorem Task.component_quotient_exact (T : Task K V) (P : Submodule K V)
    (v : E6Vertex) : LinearMap.ker ((T.quotientProjection P).map v)=
      LinearMap.range ((T.componentInclusion P).map v) := by
  cases v with
  | center => exact (Submodule.ker_mkQ P).trans (Submodule.range_subtype P).symm
  | middle i => exact restrictedQuotient_exact (T.U i) P
  | outer i => exact restrictedQuotient_exact (T.A i) P

end UploadBroadcast.TaskDecomposition
