import UploadBroadcast.ScalarEndBaseChange

/-! Restrict actual indecomposable task components to their own ambient modules. -/
namespace UploadBroadcast.TaskDecomposition

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem map_restricted_inf (P : Submodule K V) (S : Submodule K V) (R : Submodule K P) :
    ((S.comap P.subtype) ⊓ R).map P.subtype = S ⊓ R.map P.subtype := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy.1, ⟨y, hy.2, rfl⟩⟩
  · rintro ⟨hx, y, hy, rfl⟩
    exact ⟨y, ⟨hx, hy⟩, rfl⟩

/-- Any split inside the component's own module is an actual simultaneous split
of that component inside the original ambient space. -/
theorem Split.map_subtype {S : ι → Submodule K V} {P : Submodule K V}
    {R T : Submodule K P} (h : Split (onSubspace S P) ⊤ R T) :
    Split S P (R.map P.subtype) (T.map P.subtype) := by
  constructor
  · apply disjoint_iff.mpr
    rw [← Submodule.map_inf P.subtype Subtype.val_injective, h.disjoint.eq_bot, Submodule.map_bot]
  · rw [← Submodule.map_sup, h.sup_eq, Submodule.map_subtype_top]
  · intro i
    have hh := congrArg (Submodule.map P.subtype) (h.compatible i)
    change ((S i).comap P.subtype ⊓ ⊤).map P.subtype =
      (((S i).comap P.subtype ⊓ R) ⊔ ((S i).comap P.subtype ⊓ T)).map P.subtype at hh
    rw [inf_top_eq, Submodule.map_comap_subtype, Submodule.map_sup,
      map_restricted_inf, map_restricted_inf] at hh
    exact (inf_comm _ _).trans hh

/-- The paper's indecomposable component remains indecomposable when regarded
as a task on its own ambient subspace. -/
theorem Indecomposable.onSubspace {S : ι → Submodule K V} {P : Submodule K V}
    (h : Indecomposable S P) : Indecomposable (onSubspace S P) ⊤ := by
  constructor
  · intro hp
    apply h.1
    apply bot_unique
    intro x hx
    have hh : (⟨x, hx⟩ : P) ∈ (⊤ : Submodule K P) := trivial
    rw [hp] at hh
    exact congrArg Subtype.val hh
  · intro R T hs
    rcases h.2 _ _ hs.map_subtype with hr | ht
    · left
      apply Submodule.map_injective_of_injective (f := P.subtype) Subtype.val_injective
      simpa using hr
    · right
      apply Submodule.map_injective_of_injective (f := P.subtype) Subtype.val_injective
      simpa using ht

/-- The induced three-arm task on a component. -/
def Task.onComponent (T : Task K V) (P : Submodule K V) : Task K P where
  A i := (T.A i).comap P.subtype
  U i := (T.U i).comap P.subtype
  nested i := Submodule.comap_mono (T.nested i)

@[simp] theorem Task.onComponent_spaces (T : Task K V) (P : Submodule K V) :
    (T.onComponent P).spaces = onSubspace T.spaces P := by
  funext i
  rcases i with ⟨i, b⟩
  cases b <;> rfl

theorem Task.onComponent_indec (T : Task K V) (P : Submodule K V)
    (h : Indecomposable T.spaces P) : Indecomposable (T.onComponent P).spaces ⊤ := by
  rw [T.onComponent_spaces]
  exact h.onSubspace

/-- Restriction does not merely preserve a numerical dimension: its actual
subspace is explicitly equivalent to the ambient intersection. -/
def comapIntersectionEquiv (A P : Submodule K V) : A.comap P.subtype ≃ₗ[K] ↥(A ⊓ P) where
  toFun x := ⟨x.val.val, x.property, x.val.property⟩
  invFun x := ⟨⟨x.val, x.property.2⟩, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_comap_subtype (A P : Submodule K V) :
    Module.finrank K (A.comap P.subtype) = Module.finrank K ↥(A ⊓ P) :=
  (comapIntersectionEquiv A P).finrank_eq

noncomputable def Task.componentDimension (T : Task K V) (P : Submodule K V) : ReflectionReduction.Dimension :=
  ⟨Module.finrank K P, Module.finrank K ↥(T.U 0 ⊓ P), Module.finrank K ↥(T.U 1 ⊓ P),
    Module.finrank K ↥(T.U 2 ⊓ P), Module.finrank K ↥(T.A 0 ⊓ P),
    Module.finrank K ↥(T.A 1 ⊓ P), Module.finrank K ↥(T.A 2 ⊓ P)⟩

@[simp] theorem Task.onComponent_dimensionVector {K V : Type} [Field K]
    [AddCommGroup V] [Module K V] (T : Task K V) (P : Submodule K V) :
    (T.onComponent P).dimensionVector = T.componentDimension P := by
  unfold Task.dimensionVector Task.componentDimension
  simp only [Task.onComponent, finrank_comap_subtype]

/-- Real-root conclusion directly for an indecomposable component in the original ambient space. -/
theorem Task.component_nonzero_defect_tits_one {K V : Type} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : Task K V) (P : Submodule K V) (h : Indecomposable T.spaces P)
    (hd : ReflectionReduction.defect (T.componentDimension P) ≠ 0) :
    ReflectionReduction.tits (T.componentDimension P) = 1 := by
  rw [← T.onComponent_dimensionVector P] at hd ⊢
  exact (T.onComponent P).nonzero_defect_tits_one (T.onComponent_indec P h) hd

/-- Arbitrary scalar extension preserves each actual nonzero-defect indecomposable component. -/
theorem Task.component_nonzero_defect_extend_indec {K V : Type} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : Task K V) (P : Submodule K V) (h : Indecomposable T.spaces P)
    (hd : ReflectionReduction.defect (T.componentDimension P) ≠ 0)
    (L : Type*) [Field L] [Algebra K L] :
    Indecomposable ((T.onComponent P).extend (L := L)).spaces ⊤ := by
  rw [← T.onComponent_dimensionVector P] at hd
  exact (T.onComponent P).nonzero_defect_extend_indec (T.onComponent_indec P h) hd L

end UploadBroadcast.TaskDecomposition
