import UploadBroadcast.FiniteProductCoordinates
import UploadBroadcast.EdgeExtraction

/-! An actual simultaneous internal split gives actual operational factor
tasks and a full coefficient-space direct-sum chart. -/
namespace UploadBroadcast.SplitTaskCoordinates
open TaskDecomposition FiniteProductCoordinates
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def splitEquiv (T : UploadBroadcast.Task K V) (P Q : Submodule K V)
    (h : Split (EdgeExtraction.configuration T).spaces ⊤ P Q) : (P × Q) ≃ₗ[K] V :=
  Submodule.prodEquivOfIsCompl P Q ⟨h.disjoint,codisjoint_iff.mpr h.sup_eq⟩

theorem subspace_image (T : UploadBroadcast.Task K V) (P Q : Submodule K V)
    (h : Split (EdgeExtraction.configuration T).spaces ⊤ P Q)
    (A : Submodule K V) (hA : A=(A ⊓ P) ⊔ (A ⊓ Q)) :
    ((A.comap P.subtype).prod (A.comap Q.subtype)).map (splitEquiv T P Q h).toLinearMap=A := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    change (x.1.val+x.2.val) ∈ A
    exact A.add_mem hx.1 hx.2
  · intro x hx
    rw [hA] at hx
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨a,ha.2⟩,⟨b,hb.2⟩),⟨ha.1,hb.1⟩,hab⟩

noncomputable def leftTask (T : UploadBroadcast.Task K V) (P Q : Submodule K V)
    (h : Split (EdgeExtraction.configuration T).spaces ⊤ P Q) : UploadBroadcast.Task K P :=
  T.imageTask ((LinearMap.fst K P Q).comp (splitEquiv T P Q h).symm.toLinearMap)

noncomputable def rightTask (T : UploadBroadcast.Task K V) (P Q : Submodule K V)
    (h : Split (EdgeExtraction.configuration T).spaces ⊤ P Q) : UploadBroadcast.Task K Q :=
  T.imageTask ((LinearMap.snd K P Q).comp (splitEquiv T P Q h).symm.toLinearMap)

theorem projected_subspaces (T : UploadBroadcast.Task K V) (P Q : Submodule K V)
    (h : Split (EdgeExtraction.configuration T).spaces ⊤ P Q)
    (A : Submodule K V) (hA : A=(A ⊓ P) ⊔ (A ⊓ Q)) :
    A.map ((LinearMap.fst K P Q).comp (splitEquiv T P Q h).symm.toLinearMap)=A.comap P.subtype ∧
    A.map ((LinearMap.snd K P Q).comp (splitEquiv T P Q h).symm.toLinearMap)=A.comap Q.subtype := by
  let e := splitEquiv T P Q h
  have hcancel : e.symm.toLinearMap.comp e.toLinearMap=LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply x
  have hh := subspace_image T P Q h A hA
  have hp : A.map e.symm.toLinearMap=(A.comap P.subtype).prod (A.comap Q.subtype) := by
    calc
      _ = (((A.comap P.subtype).prod (A.comap Q.subtype)).map e.toLinearMap).map e.symm.toLinearMap := by rw [hh]
      _ = _ := by rw [←Submodule.map_comp,hcancel,Submodule.map_id]
  constructor
  · rw [Submodule.map_comp,hp,Submodule.prod_map_fst]
  · rw [Submodule.map_comp,hp,Submodule.prod_map_snd]

/-- Exact induced side and signal spaces of both operational factors. -/
theorem factor_spaces (T : UploadBroadcast.Task K V) (P Q : Submodule K V)
    (h : Split (EdgeExtraction.configuration T).spaces ⊤ P Q) :
    (∀ i, (leftTask T P Q h).A i=(T.A i).comap P.subtype) ∧
    (∀ i, (leftTask T P Q h).U i=(T.U i).comap P.subtype) ∧
    (∀ i, (rightTask T P Q h).A i=(T.A i).comap Q.subtype) ∧
    (∀ i, (rightTask T P Q h).U i=(T.U i).comap Q.subtype) := by
  have hA (i : Three) : T.A i=(T.A i ⊓ P) ⊔ (T.A i ⊓ Q) := by
    simpa only [Task.spaces,EdgeExtraction.configuration,if_false,inf_top_eq] using h.compatible (i,false)
  have hU (i : Three) : T.U i=(T.U i ⊓ P) ⊔ (T.U i ⊓ Q) := by
    simpa only [Task.spaces,EdgeExtraction.configuration,if_true,inf_top_eq] using h.compatible (i,true)
  exact ⟨fun i => (projected_subspaces T P Q h (T.A i) (hA i)).1,
    fun i => (projected_subspaces T P Q h (T.U i) (hU i)).1,
    fun i => (projected_subspaces T P Q h (T.A i) (hA i)).2,
    fun i => (projected_subspaces T P Q h (T.U i) (hU i)).2⟩

/-- A split certificate yields the original task exactly, with no feasibility
or coordinate-chart premise on the newly constructed factors. -/
theorem map_split (T : UploadBroadcast.Task K V) (P Q : Submodule K V)
    (h : Split (EdgeExtraction.configuration T).spaces ⊤ P Q) :
    Profile.mapTask (splitEquiv T P Q h)
      (Profile.directSum (leftTask T P Q h) (rightTask T P Q h))=T := by
  obtain ⟨hLA,hLU,hRA,hRU⟩ := factor_spaces T P Q h
  apply task_eq_of_spaces
  · funext i
    change ((leftTask T P Q h).A i |>.prod ((rightTask T P Q h).A i)).map _=T.A i
    rw [hLA,hRA]
    apply subspace_image
    simpa only [Task.spaces,EdgeExtraction.configuration,if_false,inf_top_eq] using h.compatible (i,false)
  · funext i
    change ((leftTask T P Q h).U i |>.prod ((rightTask T P Q h).U i)).map _=T.U i
    rw [hLU,hRU]
    apply subspace_image
    simpa only [Task.spaces,EdgeExtraction.configuration,if_true,inf_top_eq] using h.compatible (i,true)

end UploadBroadcast.SplitTaskCoordinates
