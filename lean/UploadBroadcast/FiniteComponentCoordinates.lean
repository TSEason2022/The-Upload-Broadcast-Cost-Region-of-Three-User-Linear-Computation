import UploadBroadcast.TaskComponentBridge
import UploadBroadcast.FiniteRelayAssembly
import UploadBroadcast.EdgeExtraction

/-! Actual finite product coordinates for the simultaneous indecomposable
components. Dimension additivity is used only to prove bijectivity of the
explicit sum map; all six labeled subspaces are transported exactly. -/
namespace UploadBroadcast.TaskDecomposition
open scoped BigOperators
variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]

/-- Add the actual embedded component vectors. -/
noncomputable def componentSumMap (P : I → Submodule K V) : (∀ i, P i) →ₗ[K] V :=
  ∑ i, (P i).subtype.comp (LinearMap.proj i)

@[simp] theorem componentSumMap_apply (P : I → Submodule K V) (x : ∀ i, P i) :
    componentSumMap P x = ∑ i, (x i).val := by
  simp [componentSumMap,LinearMap.sum_apply]

theorem componentSumMap_surjective (P : I → Submodule K V) (hP : iSup P=⊤) :
    Function.Surjective (componentSumMap P) := by
  intro x
  have hx : x ∈ ⨆ i ∈ (Finset.univ : Finset I), P i := by simp [hP]
  obtain ⟨mu,hmu⟩ := (Submodule.mem_iSup_finset_iff_exists_sum P x).mp hx
  exact ⟨mu,by simpa using hmu⟩

/-- A spanning family with exact dimension sum provides genuine product
coordinates, including the empty family for the zero ambient space. -/
noncomputable def componentSumEquiv [FiniteDimensional K V]
    (P : I → Submodule K V) (hP : iSup P=⊤)
    (hd : (∑ i, Module.finrank K (P i))=Module.finrank K V) :
    (∀ i, P i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (componentSumMap P)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
       (by simpa only [Module.finrank_pi_fintype] using hd)).mpr
       (componentSumMap_surjective P hP),componentSumMap_surjective P hP⟩

/-- Every labeled subspace is exactly the image of its coordinatewise
intersections with the actual components. -/
theorem componentSumMap_image (P : I → Submodule K V) (A : Submodule K V)
    (hA : (⨆ i, A ⊓ P i)=A) :
    (Submodule.pi Set.univ (fun i => A.comap (P i).subtype)).map (componentSumMap P)=A := by
  classical
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    rw [componentSumMap_apply]
    exact Submodule.sum_mem A (fun i _ => hx i trivial)
  · intro x hx
    have hx' : x ∈ ⨆ i ∈ (Finset.univ : Finset I), A ⊓ P i := by simpa [hA] using hx
    obtain ⟨mu,hmu⟩ := (Submodule.mem_iSup_finset_iff_exists_sum (fun i => A ⊓ P i) x).mp hx'
    refine ⟨fun i => ⟨(mu i).val,(mu i).property.2⟩,?_,?_⟩
    · intro i _
      exact (mu i).property.1
    · simpa using hmu

omit [Fintype I] in
theorem componentSup_le_iff (L : List (Submodule K V)) (W : Submodule K V) :
    componentSup L ≤ W ↔ ∀ P ∈ L, P ≤ W := by
  induction L with
  | nil => simp [componentSup]
  | cons P L ih =>
    change (P ⊔ componentSup L ≤ W) ↔ _
    simp only [sup_le_iff, ih, List.mem_cons, forall_eq_or_imp]

omit [Fintype I] in
theorem componentSup_map_eq_iSup (L : List (Submodule K V))
    (f : Submodule K V → Submodule K V) :
    componentSup (L.map f) = ⨆ i : Fin L.length, f (L.get i) := by
  apply le_antisymm
  · rw [componentSup_le_iff]
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hP
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hQ
    exact le_iSup (fun i => f (L.get i)) i
  · apply iSup_le
    intro i
    exact (componentSup_le_iff (L.map f) _).mp le_rfl _
      (List.mem_map.mpr ⟨L.get i,List.get_mem L i,rfl⟩)

omit [Fintype I] in
/-- Every actual finite-dimensional task admits a finite product of its own
indecomposable subspaces, with an explicit linear coordinate equivalence and
exact transport of all six labeled spaces. -/
theorem Task.exists_finite_component_coordinates [FiniteDimensional K V]
    (T : Task K V) :
    ∃ n : ℕ, ∃ P : Fin n → Submodule K V,
      (∀ i, Indecomposable T.spaces (P i)) ∧ iSup P=⊤ ∧
      (∑ i, Module.finrank K (P i))=Module.finrank K V ∧
      ∃ e : (∀ i, P i) ≃ₗ[K] V,
        ∀ j, (Submodule.pi Set.univ (fun i => (T.spaces j).comap (P i).subtype)).map
          e.toLinearMap=T.spaces j := by
  classical
  obtain ⟨L,hL,hspan,hspaces,hd⟩ := T.exists_finite_components
  have hsup : (⨆ i : Fin L.length, L.get i)=⊤ := by
    have hh : componentSup L = ⨆ i : Fin L.length, L.get i := by
      simpa using componentSup_map_eq_iSup L id
    exact hh.symm.trans hspan
  have hdim : (∑ i : Fin L.length, Module.finrank K (L.get i))=Module.finrank K V := by
    rw [← List.sum_ofFn]
    have he := List.map_ofFn L.get (fun P : Submodule K V => Module.finrank K P)
    rw [List.ofFn_get] at he
    simpa only [Function.comp_def] using (congrArg List.sum he).symm.trans hd
  refine ⟨L.length,L.get,fun i => hL _ (List.get_mem L i),hsup,hdim,
    componentSumEquiv L.get hsup hdim,?_⟩
  intro j
  apply componentSumMap_image
  exact (componentSup_map_eq_iSup L (fun P => T.spaces j ⊓ P)).symm.trans (hspaces j)

end UploadBroadcast.TaskDecomposition

namespace UploadBroadcast.FiniteComponentCoordinates
open TaskDecomposition
open scoped BigOperators
variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]

omit [Fintype I] in
/-- A coordinate projection maps the product subspace onto its factor. -/
theorem pi_map_proj {F : I → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module K (F i)]
    (A : ∀ i, Submodule K (F i)) (i : I) :
    (Submodule.pi Set.univ A).map (LinearMap.proj i)=A i := by
  classical
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact hx i trivial
  · intro x hx
    refine ⟨LinearMap.single K F i x,?_,?_⟩
    · exact Submodule.le_comap_single_pi A hx
    · simp

/-- Project an original operational task in an actual product chart. -/
def componentTask (T : UploadBroadcast.Task K V) (P : I → Submodule K V)
    (e : (∀ i, P i) ≃ₗ[K] V) (i : I) : UploadBroadcast.Task K (P i) :=
  (Profile.mapTask e.symm T).imageTask (LinearMap.proj i)

omit [Fintype I] in
theorem projected_space_eq (P : I → Submodule K V) (e : (∀ i, P i) ≃ₗ[K] V)
    (A : Submodule K V)
    (hA : (Submodule.pi Set.univ (fun i => A.comap (P i).subtype)).map e.toLinearMap=A)
    (i : I) :
    (A.map e.symm.toLinearMap).map (LinearMap.proj i)=A.comap (P i).subtype := by
  have he : e.symm.toLinearMap.comp e.toLinearMap=LinearMap.id := by ext x; simp
  calc
    _ = (((Submodule.pi Set.univ (fun i => A.comap (P i).subtype)).map e.toLinearMap).map e.symm.toLinearMap).map (LinearMap.proj i) := by rw [hA]
    _ = _ := by rw [← Submodule.map_comp e.toLinearMap e.symm.toLinearMap,he,Submodule.map_id,pi_map_proj]

omit [Fintype I] in
/-- The component constructed by projection is literally the original
induced task, including feasibility rather than just dimension data. -/
theorem componentTask_spaces (T : UploadBroadcast.Task K V) (P : I → Submodule K V)
    (e : (∀ i, P i) ≃ₗ[K] V)
    (h : ∀ j, (Submodule.pi Set.univ
      (fun i => ((EdgeExtraction.configuration T).spaces j).comap (P i).subtype)).map
        e.toLinearMap=(EdgeExtraction.configuration T).spaces j) (i : I) :
    (∀ j, (componentTask T P e i).A j=(T.A j).comap (P i).subtype) ∧
    (∀ j, (componentTask T P e i).U j=(T.U j).comap (P i).subtype) := by
  constructor
  · intro j
    exact projected_space_eq P e (T.A j) (h (j,false)) i
  · intro j
    exact projected_space_eq P e (T.U j) (h (j,true)) i

omit [Fintype I] in
/-- Exact original-task reconstruction from all actual indecomposable factors. -/
theorem map_product_componentTask (T : UploadBroadcast.Task K V) (P : I → Submodule K V)
    (e : (∀ i, P i) ≃ₗ[K] V)
    (h : ∀ j, (Submodule.pi Set.univ
      (fun i => ((EdgeExtraction.configuration T).spaces j).comap (P i).subtype)).map
        e.toLinearMap=(EdgeExtraction.configuration T).spaces j) :
    Profile.mapTask e (FiniteRelayAssembly.task (componentTask T P e))=T := by
  have hA : (Profile.mapTask e (FiniteRelayAssembly.task (componentTask T P e))).A=T.A := by
    funext j
    change (Submodule.pi Set.univ (fun i => (componentTask T P e i).A j)).map e.toLinearMap=T.A j
    simp_rw [(componentTask_spaces T P e h _).1]
    exact h (j,false)
  have hU : (Profile.mapTask e (FiniteRelayAssembly.task (componentTask T P e))).U=T.U := by
    funext j
    change (Submodule.pi Set.univ (fun i => (componentTask T P e i).U j)).map e.toLinearMap=T.U j
    simp_rw [(componentTask_spaces T P e h _).2]
    exact h (j,true)
  cases T
  cases hprod : Profile.mapTask e (FiniteRelayAssembly.task (componentTask _ P e))
  simp_all only [UploadBroadcast.Task.mk.injEq]

omit [Fintype I] in
/-- Unconditional operational finite-product realization of the actual
indecomposable decomposition, with exact original labeled coefficient spaces. -/
theorem exists_operational_component_coordinates [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) :
    ∃ n : ℕ, ∃ P : Fin n → Submodule K V, ∃ e : (∀ i, P i) ≃ₗ[K] V,
      Profile.mapTask e (FiniteRelayAssembly.task (componentTask T P e))=T ∧
      (∀ i, Indecomposable (EdgeExtraction.configuration (componentTask T P e i)).spaces ⊤) ∧
      (∀ i j, (componentTask T P e i).A j=(T.A j).comap (P i).subtype) ∧
      (∀ i j, (componentTask T P e i).U j=(T.U j).comap (P i).subtype) ∧
      (∑ i, Module.finrank K (P i))=Module.finrank K V := by
  obtain ⟨n,P,hind,_,hd,e,hspaces⟩ :=
    (EdgeExtraction.configuration T).exists_finite_component_coordinates
  refine ⟨n,P,e,map_product_componentTask T P e hspaces,?_,
    fun i => (componentTask_spaces T P e hspaces i).1,
    fun i => (componentTask_spaces T P e hspaces i).2,hd⟩
  intro i
  have heq : (EdgeExtraction.configuration (componentTask T P e i)).spaces =
      ((EdgeExtraction.configuration T).onComponent (P i)).spaces := by
    funext j
    rcases j with ⟨j,b⟩
    cases b
    · exact (componentTask_spaces T P e hspaces i).1 j
    · exact (componentTask_spaces T P e hspaces i).2 j
  rw [heq]
  exact (EdgeExtraction.configuration T).onComponent_indec (P i) (hind i)

end UploadBroadcast.FiniteComponentCoordinates
