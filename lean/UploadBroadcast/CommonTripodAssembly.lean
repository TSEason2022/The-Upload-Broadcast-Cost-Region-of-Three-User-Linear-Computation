import UploadBroadcast.ResidualTaskAssembly
import UploadBroadcast.ResidualPrivateSplit
import UploadBroadcast.ProfileTransport

/-! Actual removal of the fully demanded common tripod rows into an
omniscience direct summand, preserving the exact coefficient task. -/
namespace UploadBroadcast.CommonTripodAssembly
open ResidualUpload ResidualTaskAssembly
variable {K P₁ P₂ P₃ D : Type*} [Field K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]

variable (task : Task K (Ambient P₁ P₂ P₃ D))
def commonRows : Submodule K D := pureRows₁ task ⊓ pureRows₂ task ⊓ pureRows₃ task

variable {task}

def commonEmbed (C : Submodule K D) : (C × C) →ₗ[K] Ambient P₁ P₂ P₃ D where
  toFun x := (0,(x.1.val,x.2.val))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def residualEmbed (N : Submodule K D) : Ambient P₁ P₂ P₃ N →ₗ[K] Ambient P₁ P₂ P₃ D where
  toFun x := (x.1,(x.2.1.val,x.2.2.val))
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

/-- One actual ambient equivalence separates both tripod coordinates by the
same row-space complement, and fixes all private coordinates. -/
noncomputable def splitEquiv (C N : Submodule K D) (hCN : IsCompl C N) :
    ((C × C) × Ambient P₁ P₂ P₃ N) ≃ₗ[K] Ambient P₁ P₂ P₃ D := by
  let e := Submodule.prodEquivOfIsCompl C N hCN
  exact
    { toFun := fun x => (x.2.1,(e (x.1.1,x.2.2.1),e (x.1.2,x.2.2.2)))
      invFun := fun x => (((e.symm x.2.1).1,(e.symm x.2.2).1),
        (x.1,((e.symm x.2.1).2,(e.symm x.2.2).2)))
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      map_add' := by intro x y; ext <;> simp [e] <;> abel
      map_smul' := by intro a x; ext <;> simp [e,smul_add] }

@[simp] theorem splitEquiv_apply (C N : Submodule K D) (hCN : IsCompl C N)
    (c : C × C) (x : Ambient P₁ P₂ P₃ N) :
    splitEquiv C N hCN (c,x) = commonEmbed C c + residualEmbed N x := by
  ext <;> simp [splitEquiv,commonEmbed,residualEmbed]

variable (task)
variable (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
  (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
  (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)

include h₀ h₁ h₂ in
/-- The full common two-coordinate block belongs to every actual signal. -/
theorem commonEmbed_mem (i : Three) (c : commonRows task × commonRows task) :
    commonEmbed (commonRows task) c ∈ task.U i := by
  let g := selectedDemandData task h₀ h₁ h₂
  fin_cases i
  · apply (g.mem₁ _).mpr
    exact ⟨(privateDomain₁ task).zero_mem,by simpa [commonEmbed] using c.2.property.1.1⟩
  · apply (g.mem₂ _).mpr
    exact ⟨(privateDomain₂ task).zero_mem,by simpa [commonEmbed] using c.1.property.1.2⟩
  · apply (g.mem₃ _).mpr
    refine ⟨(privateDomain₃ task).zero_mem,?_⟩
    simpa [commonEmbed] using (pureRows₃ task).add_mem c.1.property.2 c.2.property.2

/-- The exact task on the row complement, before any further active reduction. -/
def residualTask
    (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D) (N : Submodule K D) : Task K (Ambient P₁ P₂ P₃ N) where
  A := ![A₁ K P₁ P₂ P₃ N,A₂ K P₁ P₂ P₃ N,A₃ K P₁ P₂ P₃ N]
  U i := (task.U i).comap (residualEmbed N)
  side_le_signal i := by
    intro x hx
    apply task.side_le_signal i
    fin_cases i
    · change residualEmbed N x ∈ task.A 0
      rw [h₀]
      obtain ⟨⟨p,t⟩,rfl⟩ := hx
      exact ⟨(p,t.val),rfl⟩
    · change residualEmbed N x ∈ task.A 1
      rw [h₁]
      obtain ⟨⟨p,t⟩,rfl⟩ := hx
      exact ⟨(p,t.val),rfl⟩
    · change residualEmbed N x ∈ task.A 2
      rw [h₂]
      obtain ⟨⟨p,t⟩,rfl⟩ := hx
      exact ⟨(p,t.val),rfl⟩
  feasible i := by
    have hs : (⨆ j : Three, ![A₁ K P₁ P₂ P₃ N,A₂ K P₁ P₂ P₃ N,A₃ K P₁ P₂ P₃ N] j) = ⊤ := by
      rw [Profile.three_iSup]
      exact sides_span
    rw [hs]
    exact le_top

def commonTask : Task K (commonRows task × commonRows task) where
  A := ![LinearMap.range (vMap (K := K)),LinearMap.range rMap,LinearMap.range diffMap]
  U _ := ⊤
  side_le_signal _ := le_top
  feasible _ := by
    rw [Profile.three_iSup]
    change (⊤ : Submodule K (commonRows task × commonRows task)) ≤
      LinearMap.range (vMap (K := K)) ⊔ LinearMap.range rMap ⊔ LinearMap.range diffMap
    rw [v_sup_r,top_sup_eq]

/-- Membership of each original signal is determined entirely by its
complement component after the full common block is separated. -/
theorem signal_membership (N : Submodule K D) (hCN : IsCompl (commonRows task) N)
    (i : Three) (c : commonRows task × commonRows task) (x : Ambient P₁ P₂ P₃ N) :
    splitEquiv (commonRows task) N hCN (c,x) ∈ task.U i ↔
      x ∈ (residualTask task h₀ h₁ h₂ N).U i := by
  rw [splitEquiv_apply]
  exact Submodule.add_mem_iff_right _ (commonEmbed_mem task h₀ h₁ h₂ i c)

private theorem mem_side₁ (x : Ambient P₁ P₂ P₃ D) :
    x ∈ A₁ K P₁ P₂ P₃ D ↔ x.1.1.2 = 0 ∧ x.1.2 = 0 ∧ x.2.2 = 0 := by
  constructor
  · rintro ⟨⟨p,t⟩,rfl⟩; simp [side₁]
  · rintro ⟨hp₂,hp₃,hr⟩
    refine ⟨(x.1.1.1,x.2.1),?_⟩
    ext <;> simp [side₁,hp₂,hp₃,hr]
private theorem mem_side₂ (x : Ambient P₁ P₂ P₃ D) :
    x ∈ A₂ K P₁ P₂ P₃ D ↔ x.1.1.1 = 0 ∧ x.1.2 = 0 ∧ x.2.1 = 0 := by
  constructor
  · rintro ⟨⟨p,t⟩,rfl⟩; simp [side₂]
  · rintro ⟨hp₁,hp₃,hv⟩
    refine ⟨(x.1.1.2,x.2.2),?_⟩
    ext <;> simp [side₂,hp₁,hp₃,hv]
private theorem mem_side₃ (x : Ambient P₁ P₂ P₃ D) :
    x ∈ A₃ K P₁ P₂ P₃ D ↔ x.1.1.1 = 0 ∧ x.1.1.2 = 0 ∧ x.2.1+x.2.2 = 0 := by
  constructor
  · rintro ⟨⟨p,t⟩,rfl⟩; simp [side₃]
  · rintro ⟨hp₁,hp₂,hvr⟩
    refine ⟨(x.1.2,x.2.2),?_⟩
    have hv : x.2.1 = -x.2.2 := eq_neg_of_add_eq_zero_left hvr
    ext <;> simp [side₃,hp₁,hp₂,hv]

private theorem mem_v {E : Type*} [AddCommGroup E] [Module K E] (x : E × E) :
    x ∈ LinearMap.range (vMap (K := K)) ↔ x.2 = 0 := by
  constructor
  · rintro ⟨t,rfl⟩; rfl
  · intro hx; exact ⟨x.1,by ext <;> simp [vMap,hx]⟩
private theorem mem_r {E : Type*} [AddCommGroup E] [Module K E] (x : E × E) :
    x ∈ LinearMap.range (rMap (K := K)) ↔ x.1 = 0 := by
  constructor
  · rintro ⟨t,rfl⟩; rfl
  · intro hx; exact ⟨x.2,by ext <;> simp [rMap,hx]⟩
private theorem mem_diff {E : Type*} [AddCommGroup E] [Module K E] (x : E × E) :
    x ∈ LinearMap.range (diffMap (K := K)) ↔ x.1+x.2 = 0 := by
  constructor
  · rintro ⟨t,rfl⟩; simp [diffMap,vMap,rMap]
  · intro hx
    have he := eq_neg_of_add_eq_zero_left hx
    exact ⟨x.2,by ext <;> simp [diffMap,vMap,rMap,he]⟩

/-- Both original side coordinates split exactly under the common-row chart. -/
theorem side_product_map (N : Submodule K D) (hCN : IsCompl (commonRows task) N) (i : Three) :
    (task.A i).map (splitEquiv (commonRows task) N hCN).symm.toLinearMap =
      ((commonTask task).A i).prod ((residualTask task h₀ h₁ h₂ N).A i) := by
  let e := Submodule.prodEquivOfIsCompl (commonRows task) N hCN
  have split_zero (c : commonRows task) (n : N) : (c:D)+(n:D)=0 ↔ c=0 ∧ n=0 := by
    change e (c,n) = 0 ↔ _
    rw [← e.map_zero,e.injective.eq_iff]
    simp
  ext x
  rw [Submodule.mem_map_equiv]
  fin_cases i
  · change splitEquiv (commonRows task) N hCN x ∈ task.A 0 ↔
      x.1 ∈ LinearMap.range (vMap (K := K)) ∧ x.2 ∈ A₁ K P₁ P₂ P₃ N
    rw [h₀,mem_side₁,mem_v,mem_side₁]
    change (x.2.1.1.2=0 ∧ x.2.1.2=0 ∧ (x.1.2:D)+(x.2.2.2:D)=0) ↔ _
    rw [split_zero]
    tauto
  · change splitEquiv (commonRows task) N hCN x ∈ task.A 1 ↔
      x.1 ∈ LinearMap.range (rMap (K := K)) ∧ x.2 ∈ A₂ K P₁ P₂ P₃ N
    rw [h₁,mem_side₂,mem_r,mem_side₂]
    change (x.2.1.1.1=0 ∧ x.2.1.2=0 ∧ (x.1.1:D)+(x.2.2.1:D)=0) ↔ _
    rw [split_zero]
    tauto
  · change splitEquiv (commonRows task) N hCN x ∈ task.A 2 ↔
      x.1 ∈ LinearMap.range (diffMap (K := K)) ∧ x.2 ∈ A₃ K P₁ P₂ P₃ N
    rw [h₂,mem_side₃,mem_diff,mem_side₃]
    change (x.2.1.1.1=0 ∧ x.2.1.1.2=0 ∧
      ((x.1.1:D)+(x.2.2.1:D))+((x.1.2:D)+(x.2.2.2:D))=0) ↔ _
    have he : ((x.1.1:D)+(x.2.2.1:D))+((x.1.2:D)+(x.2.2.2:D)) =
        ((x.1.1+x.1.2 : commonRows task):D)+((x.2.2.1+x.2.2.2 : N):D) := by simp; abel
    rw [he,split_zero]
    tauto

private theorem task_eq_of_spaces {V : Type*} [AddCommGroup V] [Module K V]
    {T S : Task K V} (hA : T.A = S.A) (hU : T.U = S.U) : T = S := by
  cases T; cases S; cases hA; cases hU; rfl

/-- Exact coefficient-task equality after a single common-row coordinate
change, not merely equality of dimensions or upload values. -/
theorem common_product_mapTask (N : Submodule K D) (hCN : IsCompl (commonRows task) N) :
    Profile.mapTask (splitEquiv (commonRows task) N hCN).symm task =
      Profile.directSum (commonTask task) (residualTask task h₀ h₁ h₂ N) := by
  apply task_eq_of_spaces
  · funext i
    exact side_product_map task h₀ h₁ h₂ N hCN i
  · funext i
    change (task.U i).map (splitEquiv (commonRows task) N hCN).symm.toLinearMap =
      (⊤ : Submodule K (commonRows task × commonRows task)).prod ((residualTask task h₀ h₁ h₂ N).U i)
    ext x
    rw [Submodule.mem_map_equiv]
    change splitEquiv (commonRows task) N hCN x ∈ task.U i ↔
      x.1 ∈ (⊤ : Submodule K (commonRows task × commonRows task)) ∧
      x.2 ∈ (residualTask task h₀ h₁ h₂ N).U i
    rw [signal_membership task h₀ h₁ h₂ N hCN i x.1 x.2]
    simp

include h₀ h₁ h₂ in
/-- Pure rows are recovered from actual pure signal coefficients, not from
projections of mixed demands. -/
theorem pureRows₁_mem_iff (d : D) : d ∈ pureRows₁ task ↔ embedR (K := K) d ∈ task.U 0 := by
  have hh := (selectedDemandData task h₀ h₁ h₂).mem₁ (embedR (K := K) d)
  simpa [embedR,side₂] using hh.symm
include h₀ h₁ h₂ in
theorem pureRows₂_mem_iff (d : D) : d ∈ pureRows₂ task ↔ embedV (K := K) d ∈ task.U 1 := by
  have hh := (selectedDemandData task h₀ h₁ h₂).mem₂ (embedV (K := K) d)
  simpa [embedV,side₁] using hh.symm
include h₀ h₁ h₂ in
theorem pureRows₃_mem_iff (d : D) : d ∈ pureRows₃ task ↔ embedV (K := K) d ∈ task.U 2 := by
  have hh := (selectedDemandData task h₀ h₁ h₂).mem₃ (embedV (K := K) d)
  simpa [embedV,side₁] using hh.symm

/-- Each complementary pure-demand space is the actual intersection with N. -/
theorem residual_pureRows (N : Submodule K D) :
    pureRows₁ (residualTask task h₀ h₁ h₂ N) = (pureRows₁ task).comap N.subtype ∧
    pureRows₂ (residualTask task h₀ h₁ h₂ N) = (pureRows₂ task).comap N.subtype ∧
    pureRows₃ (residualTask task h₀ h₁ h₂ N) = (pureRows₃ task).comap N.subtype := by
  constructor
  · ext d
    change d ∈ pureRows₁ (residualTask task h₀ h₁ h₂ N) ↔ (d:D) ∈ pureRows₁ task
    rw [pureRows₁_mem_iff _ rfl rfl rfl,pureRows₁_mem_iff task h₀ h₁ h₂]
    rfl
  constructor
  · ext d
    change d ∈ pureRows₂ (residualTask task h₀ h₁ h₂ N) ↔ (d:D) ∈ pureRows₂ task
    rw [pureRows₂_mem_iff _ rfl rfl rfl,pureRows₂_mem_iff task h₀ h₁ h₂]
    rfl
  · ext d
    change d ∈ pureRows₃ (residualTask task h₀ h₁ h₂ N) ↔ (d:D) ∈ pureRows₃ task
    rw [pureRows₃_mem_iff _ rfl rfl rfl,pureRows₃_mem_iff task h₀ h₁ h₂]
    rfl

/-- The separated residual has zero triple pure-demand intersection. -/
theorem residual_commonRows_eq_bot (N : Submodule K D) (hCN : IsCompl (commonRows task) N) :
    commonRows (residualTask task h₀ h₁ h₂ N) = ⊥ := by
  obtain ⟨hp₁,hp₂,hp₃⟩ := residual_pureRows task h₀ h₁ h₂ N
  unfold commonRows
  rw [hp₁,hp₂,hp₃,← Submodule.comap_inf,← Submodule.comap_inf]
  apply le_antisymm _ bot_le
  intro d hd
  exact Subtype.ext (Submodule.disjoint_def.mp hCN.disjoint d hd d.property)

/-- Projecting any actual signal onto private coordinates is unaffected by
the common-row split, since the removed factor has zero private coordinates. -/
theorem private_image_eq {P : Type*} [AddCommGroup P] [Module K P]
    (N : Submodule K D) (hCN : IsCompl (commonRows task) N)
    (π : Ambient P₁ P₂ P₃ D →ₗ[K] P) (π' : Ambient P₁ P₂ P₃ N →ₗ[K] P)
    (hπ : ∀ c x, π (splitEquiv (commonRows task) N hCN (c,x)) = π' x) (i : Three) :
    (task.U i).map π = ((residualTask task h₀ h₁ h₂ N).U i).map π' := by
  let e : ((commonRows task × commonRows task) × Ambient P₁ P₂ P₃ N) ≃ₗ[K]
      Ambient P₁ P₂ P₃ D := splitEquiv (commonRows task) N hCN
  ext p
  constructor
  · rintro ⟨u,hu,rfl⟩
    have hm : e ((e.symm u).1,(e.symm u).2) ∈ task.U i := by simpa using hu
    have hx := (signal_membership task h₀ h₁ h₂ N hCN i (e.symm u).1 (e.symm u).2).mp hm
    refine ⟨(e.symm u).2,hx,?_⟩
    have he := hπ (e.symm u).1 (e.symm u).2
    simpa only [e,Prod.eta,LinearEquiv.apply_symm_apply] using he.symm
  · rintro ⟨x,hx,rfl⟩
    exact ⟨e (0,x),(signal_membership task h₀ h₁ h₂ N hCN i 0 x).mpr hx,hπ 0 x⟩

/-- Full use of every retained private dimension is preserved exactly. -/
theorem residual_used (N : Submodule K D) (hCN : IsCompl (commonRows task) N) :
    used₁ (residualTask task h₀ h₁ h₂ N) = used₁ task ∧
    used₂ (residualTask task h₀ h₁ h₂ N) = used₂ task ∧
    used₃ (residualTask task h₀ h₁ h₂ N) = used₃ task := by
  have hp₁ (i : Three) := private_image_eq task h₀ h₁ h₂ N hCN
    (private₁ (K := K)) (private₁ (K := K)) (by intro c x; rfl) i
  have hp₂ (i : Three) := private_image_eq task h₀ h₁ h₂ N hCN
    (private₂ (K := K)) (private₂ (K := K)) (by intro c x; rfl) i
  have hp₃ (i : Three) := private_image_eq task h₀ h₁ h₂ N hCN
    (private₃ (K := K)) (private₃ (K := K)) (by intro c x; rfl) i
  simp [used₁,used₂,used₃,← hp₁,← hp₂,← hp₃]

/-- All positive-blocklength nonlinear cost regions are preserved by the
actual common-tripod direct-sum decomposition. -/
theorem common_product_achievableAt_eq [Finite K] [FiniteDimensional K P₁]
    [FiniteDimensional K P₂] [FiniteDimensional K P₃] [FiniteDimensional K D]
    (N : Submodule K D) (hCN : IsCompl (commonRows task) N) (n : ℕ) :
    task.achievableAt n =
      (Profile.directSum (commonTask task) (residualTask task h₀ h₁ h₂ N)).achievableAt n := by
  rw [Task.coordinate_achievableAt_eq task (splitEquiv (commonRows task) N hCN).symm n]
  rw [common_product_mapTask task h₀ h₁ h₂ N hCN]

/-- The exact common-row split also preserves the regularized closed region. -/
theorem common_product_costRegion_eq [Finite K] [FiniteDimensional K P₁]
    [FiniteDimensional K P₂] [FiniteDimensional K P₃] [FiniteDimensional K D]
    (N : Submodule K D) (hCN : IsCompl (commonRows task) N) :
    task.costRegion = (Profile.directSum (commonTask task) (residualTask task h₀ h₁ h₂ N)).costRegion := by
  unfold Task.costRegion
  exact congrArg closure (Set.iUnion_congr fun n => common_product_achievableAt_eq task h₀ h₁ h₂ N hCN n)

/-- The common-tripod and residual row dimensions add to the original row dimension. -/
theorem common_dimension_split [FiniteDimensional K D]
    (N : Submodule K D) (hCN : IsCompl (commonRows task) N) :
    Module.finrank K (commonRows task) + Module.finrank K N = Module.finrank K D :=
  Submodule.finrank_add_eq_of_isCompl hCN

/-- Unconditional construction of the common-tripod factor and common-free
canonical residual from any task with the actual canonical side spaces. -/
theorem exists_common_product :
    ∃ (N : Submodule K D) (hCN : IsCompl (commonRows task) N),
      Profile.mapTask (splitEquiv (commonRows task) N hCN).symm task =
        Profile.directSum (commonTask task) (residualTask task h₀ h₁ h₂ N) ∧
      commonRows (residualTask task h₀ h₁ h₂ N) = ⊥ ∧
      used₁ (residualTask task h₀ h₁ h₂ N) = used₁ task ∧
      used₂ (residualTask task h₀ h₁ h₂ N) = used₂ task ∧
      used₃ (residualTask task h₀ h₁ h₂ N) = used₃ task := by
  obtain ⟨N,hCN⟩ := (commonRows task).exists_isCompl
  obtain ⟨hu₁,hu₂,hu₃⟩ := residual_used task h₀ h₁ h₂ N hCN
  exact ⟨N,hCN,common_product_mapTask task h₀ h₁ h₂ N hCN,
    residual_commonRows_eq_bot task h₀ h₁ h₂ N hCN,hu₁,hu₂,hu₃⟩

end UploadBroadcast.CommonTripodAssembly
