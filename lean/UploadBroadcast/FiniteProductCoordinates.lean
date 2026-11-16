import UploadBroadcast.FiniteRelayAssembly

/-! Exact coefficient charts for finite-product regrouping. Every identity
below is at the level of the actual six subspaces, not just rank profiles. -/
namespace UploadBroadcast.FiniteProductCoordinates
open FiniteRelayAssembly
variable {K I J : Type*} [Field K] {F G : I → Type*}
  [∀ i, AddCommGroup (F i)] [∀ i, Module K (F i)]
  [∀ i, AddCommGroup (G i)] [∀ i, Module K (G i)]

theorem task_eq_of_spaces {V : Type*} [AddCommGroup V] [Module K V]
    (T S : Task K V) (hA : T.A=S.A) (hU : T.U=S.U) : T=S := by
  cases T
  cases S
  simp_all only [Task.mk.injEq]

theorem pi_map_congr (A : ∀ i, Submodule K (F i)) (e : ∀ i, F i ≃ₗ[K] G i) :
    (space A).map (LinearEquiv.piCongrRight e).toLinearMap=
      space (fun i => (A i).map (e i).toLinearMap) := by
  classical
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    intro i _
    exact ⟨x i,hx i trivial,rfl⟩
  · intro y hy
    have hh : ∀ i, ∃ x ∈ A i, e i x=y i := fun i => hy i trivial
    choose x hx he using hh
    exact ⟨x,fun i _ => hx i,funext he⟩

/-- Simultaneous genuine coordinate charts for every factor give a chart
of the actual product task. -/
theorem map_product_congr (T : ∀ i, Task K (F i)) (e : ∀ i, F i ≃ₗ[K] G i) :
    Profile.mapTask (LinearEquiv.piCongrRight e) (task T)=
      task (fun i => Profile.mapTask (e i) (T i)) := by
  apply task_eq_of_spaces
  · funext j
    exact pi_map_congr (fun i => (T i).A j) e
  · funext j
    exact pi_map_congr (fun i => (T i).U j) e

/-- Partition a dependent product by a predicate without choosing bases. -/
noncomputable def partitionEquiv (p : I → Prop) :
    (∀ i, F i) ≃ₗ[K] ((∀ i : {i // p i}, F i.val) × (∀ i : {i // ¬p i}, F i.val)) := by
  classical
  exact
    { Equiv.piEquivPiSubtypeProd p F with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem pi_map_partition (p : I → Prop) (A : ∀ i, Submodule K (F i)) :
    (space A).map (partitionEquiv (K:=K) (F:=F) p).toLinearMap=
      (space (fun i : {i // p i} => A i.val)).prod
        (space (fun i : {i // ¬p i} => A i.val)) := by
  classical
  let e := partitionEquiv (K:=K) (F:=F) p
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨fun i _ => hx i.val trivial,fun i _ => hx i.val trivial⟩
  · intro y hy
    refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
    intro i _
    by_cases hi : p i
    · have he := congrArg (fun z => z.1 ⟨i,hi⟩) (e.apply_symm_apply y)
      change (e.symm y) i=y.1 ⟨i,hi⟩ at he
      rw [he]
      exact hy.1 ⟨i,hi⟩ trivial
    · have he := congrArg (fun z => z.2 ⟨i,hi⟩) (e.apply_symm_apply y)
      change (e.symm y) i=y.2 ⟨i,hi⟩ at he
      rw [he]
      exact hy.2 ⟨i,hi⟩ trivial

/-- Predicate partitioning is an exact task direct sum, preserving all labels. -/
theorem map_product_partition (p : I → Prop) (T : ∀ i, Task K (F i)) :
    Profile.mapTask (partitionEquiv (K:=K) (F:=F) p) (task T)=
      Profile.directSum (task (fun i : {i // p i} => T i.val))
        (task (fun i : {i // ¬p i} => T i.val)) := by
  apply task_eq_of_spaces
  · funext j
    exact pi_map_partition p (fun i => (T i).A j)
  · funext j
    exact pi_map_partition p (fun i => (T i).U j)

theorem pi_map_reindex (A : ∀ i, Submodule K (F i)) (e : I ≃ J) :
    (space A).map (LinearEquiv.piCongrLeft' K F e).toLinearMap=
      space (fun j => A (e.symm j)) := by
  let E := LinearEquiv.piCongrLeft' K F e
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    intro j _
    exact hx (e.symm j) trivial
  · intro y hy
    refine ⟨E.symm y,?_,E.apply_symm_apply y⟩
    intro i _
    obtain ⟨j,rfl⟩ := e.symm.surjective i
    have he := congrArg (fun f => f j) (E.apply_symm_apply y)
    change (E.symm y) (e.symm j)=y j at he
    rw [he]
    exact hy j trivial

/-- Relabeling component indices preserves the literal product task. -/
theorem map_product_reindex (T : ∀ i, Task K (F i)) (e : I ≃ J) :
    Profile.mapTask (LinearEquiv.piCongrLeft' K F e) (task T)=
      task (fun j => T (e.symm j)) := by
  apply task_eq_of_spaces
  · funext j
    exact pi_map_reindex (fun i => (T i).A j) e
  · funext j
    exact pi_map_reindex (fun i => (T i).U j) e

/-- Regroup two indexed products into the indexed product of paired factors. -/
def piProdEquiv : ((∀ i, F i) × (∀ i, G i)) ≃ₗ[K] (∀ i, F i × G i) where
  toFun x i := (x.1 i,x.2 i)
  invFun x := (fun i => (x i).1,fun i => (x i).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem map_space_prod (A : ∀ i, Submodule K (F i)) (B : ∀ i, Submodule K (G i)) :
    ((space A).prod (space B)).map (piProdEquiv (K:=K) (F:=F) (G:=G)).toLinearMap=
      space (fun i => (A i).prod (B i)) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact fun i _ => ⟨hx.1 i trivial,hx.2 i trivial⟩
  · intro y hy
    exact ⟨(fun i => (y i).1,fun i => (y i).2),
      ⟨fun i _ => (hy i trivial).1,fun i _ => (hy i trivial).2⟩,rfl⟩

/-- Pairing factors is an exact labeled-task coordinate identity. -/
theorem map_product_exchange (T : ∀ i, Task K (F i)) (S : ∀ i, Task K (G i)) :
    Profile.mapTask (piProdEquiv (K:=K) (F:=F) (G:=G))
      (Profile.directSum (task T) (task S))=task (fun i => Profile.directSum (T i) (S i)) := by
  apply task_eq_of_spaces
  · funext j
    exact map_space_prod (fun i => (T i).A j) (fun i => (S i).A j)
  · funext j
    exact map_space_prod (fun i => (T i).U j) (fun i => (S i).U j)

section FiniteSums
open scoped BigOperators
variable [Fintype I] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def sumMaps (f : ∀ i, F i →ₗ[K] V) : (∀ i, F i) →ₗ[K] V :=
  ∑ i, (f i).comp (LinearMap.proj i)

@[simp] theorem sumMaps_apply (f : ∀ i, F i →ₗ[K] V) (x : ∀ i, F i) :
    sumMaps f x=∑ i, f i (x i) := by simp [sumMaps,LinearMap.sum_apply]

/-- The image of a finite product under the actual sum of coefficient maps
is exactly the join of the individual subspace images. -/
theorem image_pi_sumMaps (f : ∀ i, F i →ₗ[K] V) (A : ∀ i, Submodule K (F i)) :
    (space A).map (sumMaps f)=⨆ i, (A i).map (f i) := by
  classical
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    rw [sumMaps_apply]
    apply Submodule.sum_mem
    intro i _
    exact (le_iSup (fun j => (A j).map (f j)) i) ⟨x i,hx i trivial,rfl⟩
  · intro y hy
    have hy' : y ∈ ⨆ i ∈ (Finset.univ : Finset I), (A i).map (f i) := by simpa using hy
    obtain ⟨mu,hmu⟩ := (Submodule.mem_iSup_finset_iff_exists_sum (fun i => (A i).map (f i)) y).mp hy'
    have hh : ∀ i, ∃ x ∈ A i, f i x=(mu i).val := fun i => (mu i).property
    choose x hx he using hh
    refine ⟨x,fun i _ => hx i,?_⟩
    rw [sumMaps_apply]
    simpa only [he,Finset.mem_univ,Finset.sum_const_zero,Finset.sum_ite_irrel] using hmu
end FiniteSums

section OrdinaryProducts
variable {V W X Y : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]

theorem mapTask_trans (T : Task K V) (e : V ≃ₗ[K] W) (f : W ≃ₗ[K] X) :
    Profile.mapTask f (Profile.mapTask e T)=Profile.mapTask (e.trans f) T := by
  apply task_eq_of_spaces
  · funext i
    exact (Submodule.map_comp e.toLinearMap f.toLinearMap (T.A i)).symm
  · funext i
    exact (Submodule.map_comp e.toLinearMap f.toLinearMap (T.U i)).symm

theorem map_product_subspaces (A : Submodule K V) (B : Submodule K W)
    (e : V ≃ₗ[K] X) (f : W ≃ₗ[K] Y) :
    (A.prod B).map (e.prodCongr f).toLinearMap=(A.map e.toLinearMap).prod (B.map f.toLinearMap) := by
  ext z
  constructor
  · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
    exact ⟨⟨a,ha,rfl⟩,⟨b,hb,rfl⟩⟩
  · rintro ⟨⟨a,ha,he⟩,⟨b,hb,hf⟩⟩
    exact ⟨(a,b),⟨ha,hb⟩,Prod.ext he hf⟩

theorem map_directSum_congr (T : Task K V) (S : Task K W)
    (e : V ≃ₗ[K] X) (f : W ≃ₗ[K] Y) :
    Profile.mapTask (e.prodCongr f) (Profile.directSum T S)=
      Profile.directSum (Profile.mapTask e T) (Profile.mapTask f S) := by
  apply task_eq_of_spaces
  · funext i
    exact map_product_subspaces (T.A i) (S.A i) e f
  · funext i
    exact map_product_subspaces (T.U i) (S.U i) e f
end OrdinaryProducts

section FiveFactors
variable {A B C D E : Type*}
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]
  [AddCommGroup E] [Module K E]

/-- Move selected resonant factors beside their selected cycle factors. -/
def repairRegroupEquiv : ((A×B)×(C×(D×E))) ≃ₗ[K] ((B×C)×((A×E)×D)) where
  toFun x := ((x.1.2,x.2.1),((x.1.1,x.2.2.2),x.2.2.1))
  invFun y := ((y.2.1.1,y.1.1),(y.1.2,(y.2.2,y.2.1.2)))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem map_repair_regroup_spaces (PA : Submodule K A) (PB : Submodule K B)
    (PC : Submodule K C) (PD : Submodule K D) (PE : Submodule K E) :
    ((PA.prod PB).prod (PC.prod (PD.prod PE))).map (repairRegroupEquiv (K:=K)).toLinearMap=
      (PB.prod PC).prod ((PA.prod PE).prod PD) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨⟨hx.1.2,hx.2.1⟩,⟨⟨hx.1.1,hx.2.2.2⟩,hx.2.2.1⟩⟩
  · intro y hy
    refine ⟨(repairRegroupEquiv (K:=K)).symm y,?_,(repairRegroupEquiv (K:=K)).apply_symm_apply y⟩
    exact ⟨⟨hy.2.1.1,hy.1.1⟩,⟨hy.1.2,⟨hy.2.2,hy.2.1.2⟩⟩⟩

/-- Exact five-factor task regrouping before pairing repaired components. -/
theorem map_repair_regroup (TA : Task K A) (TB : Task K B) (TC : Task K C)
    (TD : Task K D) (TE : Task K E) :
    Profile.mapTask (repairRegroupEquiv (K:=K))
      (Profile.directSum (Profile.directSum TA TB)
        (Profile.directSum TC (Profile.directSum TD TE)))=
      Profile.directSum (Profile.directSum TB TC)
        (Profile.directSum (Profile.directSum TA TE) TD) := by
  apply task_eq_of_spaces
  · funext i
    exact map_repair_regroup_spaces (TA.A i) (TB.A i) (TC.A i) (TD.A i) (TE.A i)
  · funext i
    exact map_repair_regroup_spaces (TA.U i) (TB.U i) (TC.U i) (TD.U i) (TE.U i)
end FiveFactors

end UploadBroadcast.FiniteProductCoordinates
