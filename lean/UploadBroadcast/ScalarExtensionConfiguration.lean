import UploadBroadcast.StableEnd
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Scalar extension of labeled subspace configurations

These results concern actual tensor products and the actual extended subspaces.
They do not assume or establish classification of indecomposable representations.
-/
noncomputable section
open scoped TensorProduct
namespace UploadBroadcast.TaskDecomposition
variable {K L V ι J : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V]

/-- Extend every labeled subspace along the field extension. -/
def extendConfiguration (S : ι → Submodule K V) : ι → Submodule L (L ⊗[K] V) :=
  fun i => (S i).baseChange L

lemma baseChange_mono {P Q : Submodule K V} (h : P ≤ Q) :
    P.baseChange L ≤ Q.baseChange L :=
  Submodule.span_mono (Submodule.map_mono h)

/-- Scalar extension respects the nesting of the three arms. -/
def Task.extend (T : Task K V) : Task L (L ⊗[K] V) where
  A i := (T.A i).baseChange L
  U i := (T.U i).baseChange L
  nested i := baseChange_mono (T.nested i)

/-- Extension of a subspace is the image of its tensor-product inclusion. -/
theorem baseChange_eq_range (P : Submodule K V) :
    P.baseChange L = LinearMap.range (P.subtype.baseChange L) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨1 ⊗ₜ[K] (⟨x, hx⟩ : P), by simp⟩
  · rintro _ ⟨x, rfl⟩
    induction x with
    | zero => simp
    | tmul a x =>
      simpa using (Submodule.tmul_mem_baseChange_of_mem a x.property)
    | add x y hx hy => simpa using (P.baseChange L).add_mem hx hy

/-- A field basis gives the restriction-of-scalars coordinates. -/
def restrictionCoordinates [Fintype J] [DecidableEq J] (b : Basis J K L) :
    (L ⊗[K] V) ≃ₗ[K] (J → V) :=
  (TensorProduct.equivFinsuppOfBasisLeft b).trans (Finsupp.linearEquivFunOnFinite K V J)

@[simp] theorem restrictionCoordinates_tmul [Fintype J] [DecidableEq J]
    (b : Basis J K L) (a : L) (v : V) (j : J) :
    restrictionCoordinates (V := V) b (a ⊗ₜ[K] v) j = b.repr a j • v := by
  exact TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply b a v j

/-- The coordinates of an extended subspace are exactly copies of that
subspace. This is a statement about all tensors, not only pure tensors. -/
theorem mem_baseChange_iff_coordinates [Fintype J] [DecidableEq J]
    (b : Basis J K L) (P : Submodule K V) (x : L ⊗[K] V) :
    x ∈ P.baseChange L ↔ ∀ j, restrictionCoordinates b x j ∈ P := by
  rw [baseChange_eq_range]
  constructor
  · rintro ⟨y, rfl⟩ j
    induction y with
    | zero => simp
    | tmul a y => simpa using P.smul_mem (b.repr a j) y.property
    | add y z hy hz => simpa using P.add_mem hy hz
  · intro hx
    let y : J → P := fun j => ⟨restrictionCoordinates b x j, hx j⟩
    refine ⟨(restrictionCoordinates (V := P) b).symm y, ?_⟩
    apply (restrictionCoordinates b).injective
    have natural (z : L ⊗[K] P) :
        restrictionCoordinates b (P.subtype.baseChange L z) =
          fun j => ((restrictionCoordinates b z j : P) : V) := by
      induction z with
      | zero => ext j; simp
      | tmul a z => ext j; simp
      | add z w hz hw => ext j; simp [hz, hw]
    rw [natural, LinearEquiv.apply_symm_apply]

/-- Restricting an extended configuration to the ground field gives one
copy per basis vector of the extension, preserving every label both ways. -/
theorem restriction_configuration_iso_copies [Fintype J] [DecidableEq J]
    (b : Basis J K L) (S : ι → Submodule K V) :
    ConfigurationIso (fun i => ((extendConfiguration (L := L) S i).restrictScalars K))
      (copies J S) := by
  refine ⟨restrictionCoordinates b, ?_, ?_⟩
  · intro i x hx j _
    exact (mem_baseChange_iff_coordinates b (S i) x).mp hx j
  · intro i x hx
    apply (mem_baseChange_iff_coordinates b (S i) _).mpr
    simpa using fun j => hx j (Set.mem_univ j)

/-- A configuration morphism extends to the tensor-product configurations. -/
theorem Preserves.baseChange {W : Type*} [AddCommGroup W] [Module K W]
    {S : ι → Submodule K V} {T : ι → Submodule K W}
    {f : V →ₗ[K] W} (hf : Preserves S T f) :
    Preserves (extendConfiguration (L := L) S) (extendConfiguration T)
      (f.baseChange L) := by
  intro i x hx
  apply Submodule.span_induction (p := fun x _ => f.baseChange L x ∈ (T i).baseChange L)
    (hx := hx)
  · rintro _ ⟨v, hv, rfl⟩
    simpa using Submodule.tmul_mem_baseChange_of_mem (1 : L) (hf i v hv)
  · simp
  · intro x y _ _ hx hy
    simpa using ((T i).baseChange L).add_mem hx hy
  · intro a x _ hx
    simpa using ((T i).baseChange L).smul_mem a hx

/-- The labeled configuration induced on an actual ambient subspace. -/
def onSubspace (S : ι → Submodule K V) (P : Submodule K V) :
    ι → Submodule K P := fun i => (S i).comap P.subtype

/-- A simultaneous internal direct sum supplies actual inclusion and
projection maps preserving the labels. -/
theorem Split.exists_retraction {S : ι → Submodule K V} {P Q : Submodule K V}
    (h : Split S ⊤ P Q) :
    ∃ g : V →ₗ[K] P, Preserves S (onSubspace S P) g ∧
      (∀ x : P, g (P.subtype x) = x) := by
  have hc : IsCompl P Q := ⟨h.disjoint, codisjoint_iff.mpr h.sup_eq⟩
  let g := P.linearProjOfIsCompl Q hc
  refine ⟨g, ?_, Submodule.linearProjOfIsCompl_apply_left hc⟩
  intro i x hx
  have hs : x ∈ (S i ⊓ P) ⊔ (S i ⊓ Q) := by
    rw [← h.compatible i]
    exact ⟨hx, Submodule.mem_top⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hs
  have hgy : g y = (⟨y, hy.2⟩ : P) :=
    Submodule.linearProjOfIsCompl_apply_left hc ⟨y, hy.2⟩
  have hgz : g z = 0 := Submodule.linearProjOfIsCompl_apply_right' hc z hz.2
  change ((g (y + z) : P) : V) ∈ S i
  rw [map_add, hgy, hgz, add_zero]
  exact hy.1

/-- Extension of scalars preserves sums of subspaces. -/
theorem baseChange_sup (P Q : Submodule K V) :
    (P ⊔ Q).baseChange L = P.baseChange L ⊔ Q.baseChange L := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.tmul_mem_baseChange_of_mem 1 hy))
      (Submodule.mem_sup_right (Submodule.tmul_mem_baseChange_of_mem 1 hz))
  · exact sup_le (baseChange_mono le_sup_left) (baseChange_mono le_sup_right)

/-- Extension of scalars preserves intersections, verified in actual tensor
coordinates. -/
theorem baseChange_inf [Fintype J] [DecidableEq J] (b : Basis J K L)
    (P Q : Submodule K V) :
    (P ⊓ Q).baseChange L = P.baseChange L ⊓ Q.baseChange L := by
  ext x
  simp only [mem_baseChange_iff_coordinates b, Submodule.mem_inf, forall_and]

/-- Every simultaneous split remains a simultaneous split after finite
extension. -/
theorem Split.baseChange [Fintype J] [DecidableEq J] (b : Basis J K L)
    {S : ι → Submodule K V} {W P Q : Submodule K V} (h : Split S W P Q) :
    Split (extendConfiguration S) (W.baseChange L) (P.baseChange L) (Q.baseChange L) := by
  constructor
  · apply disjoint_iff.mpr
    rw [← baseChange_inf b, h.disjoint.eq_bot, Submodule.baseChange_bot]
  · rw [← baseChange_sup, h.sup_eq]
  · intro i
    change (S i).baseChange L ⊓ W.baseChange L = _
    rw [← baseChange_inf b, h.compatible i, baseChange_sup,
      baseChange_inf b, baseChange_inf b]
    rfl

/-- Restriction coordinates commute with base-changed linear maps. -/
theorem restrictionCoordinates_natural [Fintype J] [DecidableEq J]
    (b : Basis J K L) {W : Type*} [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (x : L ⊗[K] V) :
    restrictionCoordinates b (f.baseChange L x) =
      fun j => f (restrictionCoordinates b x j) := by
  induction x with
  | zero => ext j; simp
  | tmul a x => ext j; simp
  | add x y hx hy => ext j; simp [hx, hy]

/-- Scalar extension preserves injectivity over a finite field extension. -/
theorem baseChange_injective [Fintype J] [DecidableEq J]
    (b : Basis J K L) {W : Type*} [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (hf : Function.Injective f) :
    Function.Injective (f.baseChange L) := by
  intro x y h
  apply (restrictionCoordinates b).injective
  ext j
  apply hf
  have h' := congrArg (fun z => restrictionCoordinates b z j) h
  simpa only [restrictionCoordinates_natural] using h'

/-- Every designated dimension is unchanged by finite scalar extension. -/
theorem finrank_baseChange [Fintype J] [DecidableEq J]
    (b : Basis J K L) (P : Submodule K V) :
    Module.finrank L (P.baseChange L) = Module.finrank K P := by
  rw [baseChange_eq_range, LinearMap.finrank_range_of_inj
    (baseChange_injective b P.subtype P.subtype_injective), Module.finrank_baseChange]

/-- A finite ground-field basis extends to a finite extension-field basis. -/
instance finiteDimensional_scalarExtension [FiniteDimensional K V] :
    FiniteDimensional L (L ⊗[K] V) :=
  Module.Finite.of_basis ((Module.finBasis K V).baseChange L)

/-- Scalar extension preserves the integer excess of each extended component. -/
theorem Task.componentExcess_extend [FiniteDimensional K V]
    [Fintype J] [DecidableEq J] (b : Basis J K L)
    (T : Task K V) (W : Submodule K V) :
    (T.extend (L := L)).componentExcess (W.baseChange L) = T.componentExcess W := by
  unfold Task.componentExcess
  rw [finrank_baseChange b W]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (Module.finrank L (↥((T.A i).baseChange L ⊓ W.baseChange L)) : ℤ) = _
  rw [← baseChange_inf b, finrank_baseChange b]

end UploadBroadcast.TaskDecomposition
