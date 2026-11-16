import UploadBroadcast.StableEnd
import UploadBroadcast.QuiverTits
import Mathlib.LinearAlgebra.Projection

/-! The concrete six-subspace configuration and inward-E6 representation bridge. -/
namespace UploadBroadcast.TaskDecomposition
open QuiverRepresentation

universe u
variable {K V W : Type u} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- The paper's actual subspaces and inclusion maps form the inward E6 representation. -/
def Task.toRep (T : Task K V) : Rep K inwardE6 where
  space
    | .center => V
    | .middle i => T.U i
    | .outer i => T.A i
  add
    | .center => inferInstance
    | .middle _ => inferInstance
    | .outer _ => inferInstance
  module
    | .center => inferInstance
    | .middle _ => inferInstance
    | .outer _ => inferInstance
  arrow
    | .inner i => (T.U i).subtype
    | .outer i => Submodule.inclusion (T.nested i)

instance Task.toRep_finite (T : Task K V) [FiniteDimensional K V] (v : E6Vertex) :
    FiniteDimensional K (T.toRep.space v) := by
  cases v with
  | center => exact inferInstanceAs (FiniteDimensional K V)
  | middle i => exact inferInstanceAs (FiniteDimensional K (T.U i))
  | outer i => exact inferInstanceAs (FiniteDimensional K (T.A i))

/-- A preserving ambient map uniquely determines the morphism on all six subspaces. -/
def Task.homOfPreserves (T : Task K V) (S : Task K W) (f : V →ₗ[K] W)
    (hf : Preserves T.spaces S.spaces f) : Hom T.toRep S.toRep where
  map
    | .center => f
    | .middle i => (f.comp (T.U i).subtype).codRestrict (S.U i)
        (fun x => hf (i, true) x.val x.property)
    | .outer i => (f.comp (T.A i).subtype).codRestrict (S.A i)
        (fun x => hf (i, false) x.val x.property)
  comm e := by cases e <;> rfl

@[simp] theorem Task.hom_middle_coe (T : Task K V) (S : Task K W)
    (h : Hom T.toRep S.toRep) (i : Fin 3) (x : T.U i) :
    (show S.U i from h.map (.middle i) x).val = h.map .center x.val :=
  (LinearMap.congr_fun (h.comm (.inner i)) x).symm

@[simp] theorem Task.hom_outer_coe (T : Task K V) (S : Task K W)
    (h : Hom T.toRep S.toRep) (i : Fin 3) (x : T.A i) :
    (show S.A i from h.map (.outer i) x).val = h.map .center x.val := by
  have hh := congrArg (fun z : S.U i => z.val) (LinearMap.congr_fun (h.comm (.outer i)) x)
  change (show S.U i from h.map (.middle i) (Submodule.inclusion (T.nested i) x)).val =
    (show S.A i from h.map (.outer i) x).val at hh
  rw [T.hom_middle_coe S h] at hh
  exact hh.symm

/-- Every quiver morphism is an ambient map preserving exactly the labeled six spaces. -/
theorem Task.preservesOfHom (T : Task K V) (S : Task K W) (h : Hom T.toRep S.toRep) :
    Preserves T.spaces S.spaces (h.map .center) := by
  rintro ⟨i, b⟩ x hx
  cases b with
  | false =>
    change h.map .center x ∈ S.A i
    rw [← T.hom_outer_coe S h i ⟨x, hx⟩]
    exact (h.map (.outer i) ⟨x, hx⟩).property
  | true =>
    change h.map .center x ∈ S.U i
    rw [← T.hom_middle_coe S h i ⟨x, hx⟩]
    exact (h.map (.middle i) ⟨x, hx⟩).property

/-- Injectivity of all inward arrows makes the ambient component determine a morphism. -/
theorem Task.hom_center_ext (T : Task K V) (S : Task K W)
    (f g : Hom T.toRep S.toRep) (h : f.map .center = g.map .center) : f = g := by
  apply Hom.ext
  intro v
  cases v with
  | center => exact h
  | middle i =>
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [T.hom_middle_coe S f, T.hom_middle_coe S g, h]
  | outer i =>
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [T.hom_outer_coe S f, T.hom_outer_coe S g, h]

def Task.homEquiv (T : Task K V) (S : Task K W) :
    {f : V →ₗ[K] W // Preserves T.spaces S.spaces f} ≃ Hom T.toRep S.toRep where
  toFun f := T.homOfPreserves S f.val f.property
  invFun h := ⟨h.map .center, T.preservesOfHom S h⟩
  left_inv _ := rfl
  right_inv h := T.hom_center_ext S _ h rfl

theorem Task.configurationIso_of_repIso (T : Task K V) (S : Task K W)
    (f : Iso T.toRep S.toRep) : ConfigurationIso T.spaces S.spaces :=
  ⟨f.map .center, T.preservesOfHom S f.toHom, S.preservesOfHom T f.symm.toHom⟩

noncomputable def Task.repIsoOfLinearEquiv (T : Task K V) (S : Task K W)
    (e : V ≃ₗ[K] W) (he : Preserves T.spaces S.spaces e.toLinearMap)
    (hi : Preserves S.spaces T.spaces e.symm.toLinearMap) : Iso T.toRep S.toRep :=
  Iso.ofInverse (T.homOfPreserves S e.toLinearMap he) (S.homOfPreserves T e.symm.toLinearMap hi)
    (by apply T.hom_center_ext T; ext x; exact e.symm_apply_apply x)
    (by apply S.hom_center_ext S; ext x; exact e.apply_symm_apply x)

theorem Task.configurationIso_iff_repIso (T : Task K V) (S : Task K W) :
    ConfigurationIso T.spaces S.spaces ↔ Nonempty (Iso T.toRep S.toRep) := by
  constructor
  · rintro ⟨e, he, hi⟩; exact ⟨T.repIsoOfLinearEquiv S e he hi⟩
  · rintro ⟨e⟩; exact T.configurationIso_of_repIso S e

/-- No representation indecomposability assumption is hidden in this direction:
it is derived from the paper's simultaneous internal-splitting predicate. -/
theorem Task.rep_indec_of_indec (T : Task K V) (h : Indecomposable T.spaces ⊤) :
    QuiverRepresentation.Indecomposable T.toRep := by
  rw [QuiverRepresentation.indecomposable_iff]
  constructor
  · intro hz
    apply h.1
    apply bot_unique
    intro x _
    exact hz .center x
  · intro f hff
    have hf : Stable T.spaces (f.map .center) := T.preservesOfHom T f
    have hid (x : V) : f.map .center (f.map .center x) = f.map .center x :=
      LinearMap.congr_fun (congrArg (fun g => g.map .center) hff) x
    rcases h.projection_eq_zero_or_id (f.map .center) hf hid with hz | hi
    · left; exact T.hom_center_ext T f _ hz
    · right; exact T.hom_center_ext T f _ hi

/-- Every simultaneous internal split supplies a preserving ambient projection. -/
theorem Split.exists_stable_projection {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    {S : ι → Submodule K V}
    {P Q : Submodule K V} (h : Split S ⊤ P Q) :
    ∃ p : V →ₗ[K] V, Stable S p ∧ (∀ x, p (p x) = p x) ∧
      (∀ x ∈ P, p x = x) ∧ (∀ x ∈ Q, p x = 0) := by
  have hc : IsCompl P Q := ⟨h.disjoint, codisjoint_iff.mpr h.sup_eq⟩
  let r := P.linearProjOfIsCompl Q hc
  let p := P.subtype.comp r
  have hpP (x : V) (hx : x ∈ P) : p x = x :=
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨x, hx⟩)
  have hpQ (x : V) (hx : x ∈ Q) : p x = 0 :=
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨x, hx⟩)
  refine ⟨p, ?_, ?_, hpP, hpQ⟩
  · intro i x hx
    have hh : x ∈ (S i ⊓ P) ⊔ (S i ⊓ Q) := by rw [← h.compatible]; exact ⟨hx, trivial⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hh
    rw [map_add, hpP y hy.2, hpQ z hz.2, add_zero]
    exact hy.1
  · intro x
    exact hpP (p x) (r x).property

theorem Task.indec_of_rep_indec (T : Task K V)
    (hR : QuiverRepresentation.Indecomposable T.toRep) : Indecomposable T.spaces ⊤ := by
  constructor
  · intro hzero
    have hz (x : V) : x = 0 := by
      have hh : x ∈ (⊤ : Submodule K V) := trivial
      rw [hzero] at hh
      exact hh
    apply hR.1
    intro v x
    cases v with
    | center => exact hz x
    | middle i => exact Subtype.ext (hz x.val)
    | outer i => exact Subtype.ext (hz x.val)
  · intro P Q h
    obtain ⟨p, hp, hpp, hpP, hpQ⟩ := h.exists_stable_projection
    let a := T.homOfPreserves T p hp
    have haa : a.comp a = a := by
      apply T.hom_center_ext T
      apply LinearMap.ext
      intro x
      exact hpp x
    rcases hR.idempotentsTrivial a haa with hz | hi
    · left
      have hp0 : p = 0 := congrArg (fun f => f.map .center) hz
      apply bot_unique
      intro x hx
      have hh := hpP x hx
      rw [hp0, LinearMap.zero_apply] at hh
      exact hh.symm
    · right
      have hpid : p = LinearMap.id := congrArg (fun f => f.map .center) hi
      apply bot_unique
      intro x hx
      have hh := hpQ x hx
      rw [hpid, LinearMap.id_apply] at hh
      exact hh

/-- Exact equivalence with the manuscript's internal simultaneous-splitting predicate. -/
theorem Task.toRep_indec_iff (T : Task K V) :
    QuiverRepresentation.Indecomposable T.toRep ↔ Indecomposable T.spaces ⊤ :=
  ⟨T.indec_of_rep_indec, T.rep_indec_of_indec⟩

/-- The representation dimension vector uses the actual ambient and six subspace dimensions. -/
noncomputable def Task.dimensionVector (T : Task K V) : ReflectionReduction.Dimension :=
  ⟨Module.finrank K V, Module.finrank K (T.U 0), Module.finrank K (T.U 1),
    Module.finrank K (T.U 2), Module.finrank K (T.A 0), Module.finrank K (T.A 1),
    Module.finrank K (T.A 2)⟩

@[simp] theorem Task.dimensionVector_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (T : Task K V) :
    T.dimensionVector = E6Reflection.vector (QuiverRepresentation.dimension T.toRep) := rfl

/-- Concrete nonzero-defect configurations satisfy the real-root equation.
This invokes the actual representation bridge, not an assumed root hypothesis. -/
theorem Task.nonzero_defect_tits_one {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Task K V) (hT : Indecomposable T.spaces ⊤)
    (hd : ReflectionReduction.defect T.dimensionVector ≠ 0) :
    ReflectionReduction.tits T.dimensionVector = 1 :=
  E6Reflection.nonzero_defect_tits_one T.toRep (T.rep_indec_of_indec hT) hd

/-- Concrete original-field uniqueness preserves every one of the six labeled subspaces. -/
theorem Task.nonzero_defect_configurationIso {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (T : Task K V) (S : Task K W) (hT : Indecomposable T.spaces ⊤)
    (hS : Indecomposable S.spaces ⊤) (heq : T.dimensionVector = S.dimensionVector)
    (hd : ReflectionReduction.defect T.dimensionVector ≠ 0) : ConfigurationIso T.spaces S.spaces := by
  have heq' : QuiverRepresentation.dimension T.toRep = QuiverRepresentation.dimension S.toRep := by
    have hh := congrArg E6Reflection.encode heq
    simpa only [Task.dimensionVector_eq, E6Reflection.encode_vector] using hh
  obtain ⟨e⟩ := E6Reflection.nonzero_defect_unique T.toRep S.toRep
    (T.rep_indec_of_indec hT) (S.rep_indec_of_indec hS) heq' hd
  exact T.configurationIso_of_repIso S e

end UploadBroadcast.TaskDecomposition
