import UploadBroadcast.ResidualRelayAssembly

/-! Exact pure/retained-row relay shape, with a tripod-fixing simultaneous shear. -/
namespace UploadBroadcast.ResidualRowShape
open Module ResidualUpload ResidualRowCompletion ResidualTaskAssembly ResidualRelayAssembly
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000
variable {K P₁ P₂ P₃ H₁ H₂ H₃ Z : Type*} [Field K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup H₁] [Module K H₁]
  [AddCommGroup H₂] [Module K H₂] [AddCommGroup H₃] [Module K H₃]
  [AddCommGroup Z] [Module K Z]
local notation "R" => Rows H₁ H₂ H₃ Z
local notation "S₁" => A₁ K P₁ P₂ P₃ R
local notation "S₂" => A₂ K P₁ P₂ P₃ R
local notation "S₃" => A₃ K P₁ P₂ P₃ R
local notation "P" => LinearMap.range (fullRelay (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃)
  (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (D := Z))

theorem exists_simultaneous_row_completion_fixed
    (L₁ : Submodule K (P₂ × P₃)) (L₂ : Submodule K (P₁ × P₃))
    (L₃ : Submodule K (P₁ × P₂))
    (φ₁ : L₁ →ₗ[K] Rows H₁ H₂ H₃ Z)
    (φ₂ : L₂ →ₗ[K] Rows H₁ H₂ H₃ Z)
    (φ₃ : L₃ →ₗ[K] Rows H₁ H₂ H₃ Z)
    (U₁ U₂ U₃ : Submodule K (Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ Z)))
    (shape₁ : ∀ u ∈ U₁, ∃ x : L₁,
      u.1.1.2 = x.val.1 ∧ u.1.2 = x.val.2 ∧
      u.2.2.1 = (φ₁ x).1 ∧ u.2.2.2.2.2.2 = (φ₁ x).2.2.2.2)
    (shape₂ : ∀ u ∈ U₂, ∃ x : L₂,
      u.1.1.1 = x.val.1 ∧ u.1.2 = x.val.2 ∧
      u.2.1.2.1 = (φ₂ x).2.1 ∧ u.2.1.2.2.2.1 = (φ₂ x).2.2.2.1)
    (shape₃ : ∀ u ∈ U₃, ∃ x : L₃,
      u.1.1.1 = x.val.1 ∧ u.1.1.2 = x.val.2 ∧
      u.2.1.2.2.1 + u.2.2.2.2.1 = (φ₃ x).2.2.1) :
    ∃ e : Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ Z) ≃ₗ[K]
        Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ Z),
      (S₁).map e.toLinearMap = S₁ ∧ (S₂).map e.toLinearMap = S₂ ∧
      (S₃).map e.toLinearMap = S₃ ∧
      U₁.map e.toLinearMap ≤ S₁ ⊔ P ∧ U₂.map e.toLinearMap ≤ S₂ ⊔ P ∧
      U₃.map e.toLinearMap ≤ S₃ ⊔ P ∧
      (∀ t, e (0,t) = (0,t)) := by
  obtain ⟨g₁,g₂,g₃,h₁,h₂,h₃⟩ := simultaneous_corrections L₁ L₂ L₃ φ₁ φ₂ φ₃
  let e := squareZeroShear (privateCorrection g₁ g₂ g₃) (privateCorrection_square_zero g₁ g₂ g₃)
  obtain ⟨hs₁,hs₂,hs₃⟩ := privateShear_preserves g₁ g₂ g₃
  refine ⟨e,hs₁,hs₂,hs₃,?_,?_,?_,?_⟩
  · rintro _ ⟨u,hu,rfl⟩
    obtain ⟨x,hp₂,hp₃,hH,hb⟩ := shape₁ u hu
    apply lift_row_recovery S₁ vMap (fun t => ⟨(0,t),rfl⟩) (e u)
    apply user₁_recovers
    · have hh := (h₁ x).1
      change u.2.2.1 - ((g₂ u.1.1.2).1 + (g₃ u.1.2).1) = 0
      rw [hp₂,hp₃,hH]
      simpa only [Prod.fst_sub, sub_sub] using hh
    · have hh := (h₁ x).2
      change u.2.2.2.2.2.2 - ((g₂ u.1.1.2).2.2.2.2 + (g₃ u.1.2).2.2.2.2) = 0
      rw [hp₂,hp₃,hb]
      simpa only [Prod.snd_sub, sub_sub] using hh
  · rintro _ ⟨u,hu,rfl⟩
    obtain ⟨x,hp₁,hp₃,hH,ha⟩ := shape₂ u hu
    apply lift_row_recovery S₂ rMap (fun t => ⟨(0,t),rfl⟩) (e u)
    apply user₂_recovers
    · have hh := (h₂ x).1
      change u.2.1.2.1 - ((g₁ u.1.1.1).2.1 - (g₃ u.1.2).2.1) = 0
      rw [hp₁,hp₃,hH]
      simp only [Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub] at hh
      convert hh using 1; abel
    · have hh := (h₂ x).2
      change u.2.1.2.2.2.1 - ((g₁ u.1.1.1).2.2.2.1 - (g₃ u.1.2).2.2.2.1) = 0
      rw [hp₁,hp₃,ha]
      simp only [Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub] at hh
      convert hh using 1; abel
  · rintro _ ⟨u,hu,rfl⟩
    obtain ⟨x,hp₁,hp₂,hH⟩ := shape₃ u hu
    apply lift_row_recovery S₃ diffMap (fun t => ⟨(0,t),by simp [side₃,diffMap,vMap,rMap]⟩) (e u)
    apply user₃_recovers
    have hh := h₃ x
    change (u.2.1.2.2.1 - ((g₁ u.1.1.1).2.2.1 - (g₃ u.1.2).2.2.1)) +
      (u.2.2.2.2.1 - ((g₂ u.1.1.2).2.2.1 + (g₃ u.1.2).2.2.1)) = 0
    have he : (u.2.1.2.2.1 - ((g₁ u.1.1.1).2.2.1 - (g₃ u.1.2).2.2.1)) +
        (u.2.2.2.2.1 - ((g₂ u.1.1.2).2.2.1 + (g₃ u.1.2).2.2.1)) =
        (u.2.1.2.2.1 + u.2.2.2.2.1) - (g₁ u.1.1.1).2.2.1 - (g₂ u.1.1.2).2.2.1 := by abel
    rw [he,hp₁,hp₂,hH]
    exact hh

  · intro t
    change (0,t) - privateCorrection g₁ g₂ g₃ (0,t) = (0,t)
    simp [privateCorrection]

/-- The coordinate change is constructed from the actual demand graph and fixes
all tripod vectors pointwise. -/
theorem exists_shear_in_rows
    (task : Task K (Ambient P₁ P₂ P₃ R))
    (h₀ : task.A 0 = S₁) (h₁ : task.A 1 = S₂) (h₂ : task.A 2 = S₃)
    (b₀ : ∀ d ∈ pureRows₁ task, d.1=0 ∧ d.2.2.2.2=0)
    (b₁ : ∀ d ∈ pureRows₂ task, d.2.1=0 ∧ d.2.2.2.1=0)
    (b₂ : ∀ d ∈ pureRows₃ task, d.2.2.1=0) :
    ∃ e : Ambient P₁ P₂ P₃ R ≃ₗ[K] Ambient P₁ P₂ P₃ R,
      (∀ i, (task.A i).map e.toLinearMap = task.A i) ∧
      (∀ i, (task.U i).map e.toLinearMap ≤ task.A i ⊔ P) ∧
      (∀ t, e (0,t) = (0,t)) := by
  let g := selectedDemandData task h₀ h₁ h₂
  obtain ⟨hu₀,hu₁,hu₂⟩ := signal_graphs task h₀ h₁ h₂ g
  have result := exists_simultaneous_row_completion_fixed
    (privateDomain₁ task) (privateDomain₂ task) (privateDomain₃ task)
    (g.φ₁.domRestrict _) (g.φ₂.domRestrict _) (g.φ₃.domRestrict _)
    (task.U 0) (task.U 1) (task.U 2) (by
    intro u hu
    rw [hu₀] at hu
    obtain ⟨a,ha,m,⟨x,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a,⟨⟨p,t⟩,rfl⟩,d,⟨d,rfl⟩,rfl⟩ := Submodule.mem_sup.mp ha
    have hd := b₀ d d.property
    refine ⟨x,?_,?_,?_,?_⟩ <;> simp [side₁,pureR,mixed₁,hd]
  ) (by
    intro u hu
    rw [hu₁] at hu
    obtain ⟨a,ha,m,⟨x,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a,⟨⟨p,t⟩,rfl⟩,d,⟨d,rfl⟩,rfl⟩ := Submodule.mem_sup.mp ha
    have hd := b₁ d d.property
    refine ⟨x,?_,?_,?_,?_⟩ <;> simp [side₂,pureV,mixed₂,hd]
  ) (by
    intro u hu
    rw [hu₂] at hu
    obtain ⟨a,ha,m,⟨x,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a,⟨⟨p,t⟩,rfl⟩,d,⟨d,rfl⟩,rfl⟩ := Submodule.mem_sup.mp ha
    have hd := b₂ d d.property
    refine ⟨x,?_,?_,?_⟩ <;> simp [side₃,pureV,mixed₃,hd]
  )


  obtain ⟨e,ha,hb,hc,ua,ub,uc,hfix⟩ := result
  refine ⟨e,?_,?_,hfix⟩
  · intro i
    fin_cases i
    · change (task.A 0).map e.toLinearMap = task.A 0
      rw [h₀]; exact ha
    · change (task.A 1).map e.toLinearMap = task.A 1
      rw [h₁]; exact hb
    · change (task.A 2).map e.toLinearMap = task.A 2
      rw [h₂]; exact hc
  · intro i
    fin_cases i
    · change (task.U 0).map e.toLinearMap ≤ task.A 0 ⊔ P
      rw [h₀]; exact ua
    · change (task.U 1).map e.toLinearMap ≤ task.A 1 ⊔ P
      rw [h₁]; exact ub
    · change (task.U 2).map e.toLinearMap ≤ task.A 2 ⊔ P
      rw [h₂]; exact uc

section RetainedRows
variable {D W : Type*} [AddCommGroup D] [Module K D] [AddCommGroup W] [Module K W]

/-- Insert the retained empty rows inside the first user-upload block. -/
def splitRows : Rows (H₁ × W) H₂ H₃ Z ≃ₗ[K] (R × W) where
  toFun t := ((t.1.1,t.2),t.1.2)
  invFun t := ((t.1.1,t.2),t.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Row coordinates adapted to any prescribed complement of the pure rows. -/
noncomputable def supportedEquiv (S W : Submodule K D) (hSW : IsCompl S W)
    (e : R ≃ₗ[K] S) : Rows (H₁ × W) H₂ H₃ Z ≃ₗ[K] D :=
  (splitRows (K := K)).trans ((e.prodCongr (LinearEquiv.refl K W)).trans
    (Submodule.prodEquivOfIsCompl S W hSW))

theorem supportedEquiv_apply (S W : Submodule K D) (hSW : IsCompl S W)
    (e : R ≃ₗ[K] S) (t : Rows (H₁ × W) H₂ H₃ Z) :
    supportedEquiv S W hSW e t = (e (t.1.1,t.2) : D) + (t.1.2 : D) := rfl

theorem supportedEquiv_mem (S W : Submodule K D) (hSW : IsCompl S W)
    (e : R ≃ₗ[K] S) (t : Rows (H₁ × W) H₂ H₃ Z) :
    supportedEquiv S W hSW e t ∈ S ↔ t.1.2 = 0 := by
  rw [supportedEquiv_apply]
  constructor
  · intro h
    have hw : (t.1.2 : D) ∈ S := by simpa using S.sub_mem h (e (t.1.1,t.2)).property
    exact Subtype.ext (Submodule.disjoint_def.mp hSW.disjoint _ hw t.1.2.property)
  · intro h
    simpa only [h,Submodule.coe_zero,add_zero] using (e (t.1.1,t.2)).property

/-- The row upload in the original retained coefficient space. -/
def transportedRowUpload (e : R ≃ₗ[K] D) : D →ₗ[K] (D × D) :=
  (e.prodCongr e).toLinearMap.comp ((rowUpload (K := K)).comp e.symm.toLinearMap)

theorem transportedRowUpload_injective (e : R ≃ₗ[K] D) :
    Function.Injective (transportedRowUpload e) :=
  (e.prodCongr e).injective.comp (rowUpload_injective.comp e.symm.injective)

/-- Every retained row is uploaded along v, exactly as in the paper. -/
theorem supportedRowUpload_retained (S W : Submodule K D) (hSW : IsCompl S W)
    (e : R ≃ₗ[K] S) (w : W) :
    transportedRowUpload (supportedEquiv S W hSW e) w = ((w : D),0) := by
  let t : Rows (H₁ × W) H₂ H₃ Z := ((0,w),0,0,0,0)
  have ht : supportedEquiv S W hSW e t = w := by
    simp [supportedEquiv_apply,t]
  rw [← ht]
  change (supportedEquiv S W hSW e).prodCongr (supportedEquiv S W hSW e)
    (rowUpload (K := K) ((supportedEquiv S W hSW e).symm (supportedEquiv S W hSW e t))) = _
  rw [LinearEquiv.symm_apply_apply]
  simp [rowUpload,t,supportedEquiv_apply]

/-- Pure rows never acquire retained-row coordinates under the upload map. -/
theorem supportedRowUpload_pure (S W : Submodule K D) (hSW : IsCompl S W)
    (e : R ≃ₗ[K] S) (s : S) :
    (transportedRowUpload (supportedEquiv S W hSW e) s).1 ∈ S ∧
    (transportedRowUpload (supportedEquiv S W hSW e) s).2 ∈ S := by
  let t := (supportedEquiv S W hSW e).symm (s : D)
  have ht : t.1.2 = 0 := (supportedEquiv_mem S W hSW e t).mp (by
    simpa only [t,LinearEquiv.apply_symm_apply] using s.property)
  change supportedEquiv S W hSW e (rowUpload (K := K) t).1 ∈ S ∧
    supportedEquiv S W hSW e (rowUpload (K := K) t).2 ∈ S
  constructor
  · exact (supportedEquiv_mem S W hSW e _).mpr ht
  · apply (supportedEquiv_mem S W hSW e _).mpr
    rfl

/-- The original-coordinate full relay. -/
def transportedFullRelay (e : R ≃ₗ[K] D) : (((P₁ × P₂) × P₃) × D) →ₗ[K]
    Ambient P₁ P₂ P₃ D where
  toFun x := (x.1, transportedRowUpload e x.2)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- Transport identifies the constructed full relay with private plus row uploads. -/
theorem transportedFullRelay_range (e : R ≃ₗ[K] D) :
    LinearMap.range (transportedFullRelay (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) e) =
      (LinearMap.range (fullRelay (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃)
        (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (D := Z))).map (rowEquiv e).toLinearMap := by
  ext x
  constructor
  · rintro ⟨⟨p,t⟩,rfl⟩
    exact ⟨fullRelay (p,e.symm t),⟨_,rfl⟩,rfl⟩
  · rintro ⟨_,⟨⟨p,t⟩,rfl⟩,rfl⟩
    refine ⟨(p,e t),?_⟩
    simp [transportedFullRelay,transportedRowUpload,rowEquiv,fullRelay]

/-- Row-coordinate construction transported back, retaining the actual shear
and its pointwise tripod-fixing property. -/
theorem exists_shear_of_row_coordinates
    (task : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)
    (e : R ≃ₗ[K] D)
    (b₀ : ∀ t, e t ∈ pureRows₁ task → t.1=0 ∧ t.2.2.2.2=0)
    (b₁ : ∀ t, e t ∈ pureRows₂ task → t.2.1=0 ∧ t.2.2.2.1=0)
    (b₂ : ∀ t, e t ∈ pureRows₃ task → t.2.2.1=0) :
    ∃ f : Ambient P₁ P₂ P₃ D ≃ₗ[K] Ambient P₁ P₂ P₃ D,
      (∀ i, (task.A i).map f.toLinearMap = task.A i) ∧
      (∀ i, (task.U i).map f.toLinearMap ≤ task.A i ⊔
        LinearMap.range (transportedFullRelay e)) ∧
      (∀ t, f (0,t) = (0,t)) ∧
      task.LocallyGenerated (LinearMap.range (transportedFullRelay e)) := by
  let a := rowEquiv (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) e
  let q := Profile.mapTask (rowEquiv e.symm) task
  have heq : rowEquiv (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) e.symm = a.symm := rfl
  obtain ⟨ha,hb,hc⟩ := row_task_sides task h₀ h₁ h₂ e.symm
  obtain ⟨pa,pb,pc⟩ := row_task_pure task h₀ h₁ h₂ e.symm
  obtain ⟨s,hs,hu,hfix⟩ := exists_shear_in_rows (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃)
    (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (Z := Z) q ha hb hc
    (fun t ht => b₀ t (by simpa only [q,pa,Submodule.mem_comap,
      LinearEquiv.symm_symm,LinearEquiv.coe_coe] using ht))
    (fun t ht => b₁ t (by simpa only [q,pb,Submodule.mem_comap,
      LinearEquiv.symm_symm,LinearEquiv.coe_coe] using ht))
    (fun t ht => b₂ t (by simpa only [q,pc,Submodule.mem_comap,
      LinearEquiv.symm_symm,LinearEquiv.coe_coe] using ht))
  let f := a.symm.trans (s.trans a)
  have hm (X : Submodule K (Ambient P₁ P₂ P₃ D)) :
      X.map f.toLinearMap = ((X.map a.symm.toLinearMap).map s.toLinearMap).map a.toLinearMap := by
    rw [← Submodule.map_comp,← Submodule.map_comp]
    rfl
  have hi (X : Submodule K (Ambient P₁ P₂ P₃ D)) :
      (X.map a.symm.toLinearMap).map a.toLinearMap = X := by
    ext x
    simp [Submodule.mem_map_equiv]
  have hP : LinearMap.range (transportedFullRelay (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) e) =
      (P).map a.toLinearMap := transportedFullRelay_range e
  refine ⟨f,?_,?_,?_,?_⟩
  · intro i
    rw [hm]
    change ((q.A i).map s.toLinearMap).map a.toLinearMap = _
    rw [hs]
    exact hi _
  · intro i
    rw [hm,hP]
    have hh := Submodule.map_mono (f := a.toLinearMap) (hu i)
    rw [Submodule.map_sup] at hh
    simpa only [q,Profile.mapTask,heq,hi] using hh
  · intro t
    change a (s (0,(e.symm t.1,e.symm t.2))) = (0,t)
    rw [hfix]
    simp [a,rowEquiv]
  · rw [hP]
    have hp : q.LocallyGenerated P := by
      have hA : ∀ i, q.A i = ![S₁,S₂,S₃] i := by
        intro i; fin_cases i
        · exact ha
        · exact hb
        · exact hc
      simpa only [Task.LocallyGenerated,hA] using
        (fullRelay_locally_generated (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃)
          (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (D := Z))
    change (P).map a.toLinearMap = ⨆ i, (P).map a.toLinearMap ⊓ task.A i
    conv_lhs => rw [show P = ⨆ i, P ⊓ q.A i from hp,Submodule.map_iSup]
    congr 1
    funext i
    rw [Submodule.map_inf a.toLinearMap a.injective]
    simpa only [q,Profile.mapTask,heq] using
      congrArg (fun X => (P).map a.toLinearMap ⊓ X) (hi (task.A i))

/-- Private coefficient summands, embedded without tripod coefficients. -/
def privateSpace : Submodule K (Ambient P₁ P₂ P₃ D) :=
  LinearMap.range (LinearMap.inl K ((P₁ × P₂) × P₃) (D × D))

/-- The pure portion of a transported row upload. -/
def pureRelay (S : Submodule K D) (e : R ≃ₗ[K] D) : Submodule K (Ambient P₁ P₂ P₃ D) :=
  S.map ((LinearMap.inr K ((P₁ × P₂) × P₃) (D × D)).comp (transportedRowUpload e))

/-- Exact pure/retained decomposition of the full upload. -/
theorem supportedFullRelay_shape (S W : Submodule K D) (hSW : IsCompl S W)
    (e : R ≃ₗ[K] S) :
    LinearMap.range (transportedFullRelay (P₁ := P₁) (P₂ := P₂) (P₃ := P₃)
      (supportedEquiv S W hSW e)) =
      privateSpace ⊔ pureRelay S (supportedEquiv S W hSW e) ⊔
        W.map (embedV (K := K)) := by
  let se := supportedEquiv S W hSW e
  apply le_antisymm
  · rintro _ ⟨⟨p,t⟩,rfl⟩
    have ht : t ∈ S ⊔ W := by rw [hSW.sup_eq_top]; trivial
    obtain ⟨s,hs,w,hw,hst⟩ := Submodule.mem_sup.mp ht
    have hp : (p,(0,0)) ∈ privateSpace (K := K) (D := D) := ⟨p,rfl⟩
    have hpr : (0,transportedRowUpload se s) ∈ pureRelay (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) S se := ⟨s,hs,rfl⟩
    have hwr : (0,((w : D),0)) ∈ W.map (embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃)) :=
      ⟨w,hw,rfl⟩
    have he : transportedRowUpload se w = (w,0) := supportedRowUpload_retained S W hSW e ⟨w,hw⟩
    convert Submodule.add_mem_sup (Submodule.add_mem_sup hp hpr) hwr using 1
    simp [transportedFullRelay,← hst,map_add,← he,se]
  · apply sup_le
    · apply sup_le
      · rintro _ ⟨p,rfl⟩
        exact ⟨(p,0),by simp [transportedFullRelay]⟩
      · rintro _ ⟨s,hs,rfl⟩
        exact ⟨(0,s),rfl⟩
    · rintro _ ⟨w,hw,rfl⟩
      refine ⟨(0,w),?_⟩
      change (0,transportedRowUpload se w) = (0,(w,0))
      rw [supportedRowUpload_retained S W hSW e ⟨w,hw⟩]

/-- P_row is contained entirely in the pure-row tripod space B₀⊗E. -/
theorem pureRelay_supported (S W : Submodule K D) (hSW : IsCompl S W)
    (e : R ≃ₗ[K] S) :
    pureRelay (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) S (supportedEquiv S W hSW e) ≤
      (⊥ : Submodule K ((P₁ × P₂) × P₃)).prod (S.prod S) := by
  rintro _ ⟨s,hs,rfl⟩
  exact ⟨rfl,supportedRowUpload_pure S W hSW e ⟨s,hs⟩⟩

/-- No pure row upload is redundant. -/
theorem pureRelay_rank [FiniteDimensional K D] (S : Submodule K D) (e : R ≃ₗ[K] D) :
    finrank K (pureRelay (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) S e) = finrank K S := by
  let j := (LinearMap.inr K ((P₁ × P₂) × P₃) (D × D)).comp (transportedRowUpload e)
  have hj : Function.Injective j := (LinearMap.inr_injective).comp
    (transportedRowUpload_injective e)
  have hh := LinearMap.finrank_range_of_inj (f := j.comp S.subtype) (hj.comp S.subtype_injective)
  rw [LinearMap.range_comp,Submodule.range_subtype] at hh
  exact hh

/-- The pure upload and the retained v-upload are independent. -/
theorem pureRelay_disjoint_retained (S W : Submodule K D) (hSW : IsCompl S W)
    (e : R ≃ₗ[K] S) :
    Disjoint (pureRelay (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) S (supportedEquiv S W hSW e))
      (W.map (embedV (K := K))) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  obtain ⟨w,hw,rfl⟩ := hy
  have hs := pureRelay_supported S W hSW e hx
  have hz : w = 0 := Submodule.disjoint_def.mp hSW.disjoint w hs.2.1 hw
  simp [hz,embedV]

/-- Private coordinates are independent of the entire pure-plus-retained relay. -/
theorem privateSpace_disjoint_rows (S W : Submodule K D) (e : R ≃ₗ[K] D) :
    Disjoint (privateSpace (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D))
      (pureRelay S e ⊔ W.map (embedV (K := K))) := by
  apply Submodule.disjoint_def.mpr
  rintro x ⟨p,rfl⟩ hx
  obtain ⟨a,⟨s,hs,rfl⟩,b,⟨w,hw,rfl⟩,he⟩ := Submodule.mem_sup.mp hx
  have hp := congrArg Prod.fst he
  change 0 + 0 = p at hp
  simp only [zero_add] at hp
  simp [← hp]

/-- Exact total rank of the source-shaped relay. -/
theorem supportedFullRelay_rank [FiniteDimensional K P₁] [FiniteDimensional K P₂]
    [FiniteDimensional K P₃] [FiniteDimensional K D]
    (S W : Submodule K D) (hSW : IsCompl S W) (e : R ≃ₗ[K] S) :
    finrank K (LinearMap.range (transportedFullRelay (P₁ := P₁) (P₂ := P₂) (P₃ := P₃)
      (supportedEquiv S W hSW e))) =
      finrank K P₁ + finrank K P₂ + finrank K P₃ + finrank K S + finrank K W := by
  have hi : Function.Injective (transportedFullRelay (P₁ := P₁) (P₂ := P₂) (P₃ := P₃)
      (supportedEquiv S W hSW e)) := by
    intro x y h
    have hp : x.1 = y.1 := congrArg (fun z : Ambient P₁ P₂ P₃ D => z.1) h
    have ht : transportedRowUpload (supportedEquiv S W hSW e) x.2 =
        transportedRowUpload (supportedEquiv S W hSW e) y.2 := congrArg Prod.snd h
    exact Prod.ext hp (transportedRowUpload_injective _ ht)
  rw [LinearMap.finrank_range_of_inj hi]
  have hd := (Submodule.prodEquivOfIsCompl S W hSW).finrank_eq
  simp only [Module.finrank_prod] at hd ⊢
  omega

/-- The pure relay itself is generated by rows individually available at users. -/
theorem pureRelay_locally_generated (S W : Submodule K D) (hSW : IsCompl S W)
    (e : R ≃ₗ[K] S) :
    let Q := pureRelay (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) S (supportedEquiv S W hSW e)
    Q = ⨆ i : Three, Q ⊓ ![A₁ K P₁ P₂ P₃ D,A₂ K P₁ P₂ P₃ D,A₃ K P₁ P₂ P₃ D] i := by
  let se := supportedEquiv S W hSW e
  let Q := pureRelay (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) S se
  change Q = _
  apply le_antisymm
  · rintro _ ⟨s,hs,rfl⟩
    let t := se.symm s
    have ht : t.1.2 = 0 := (supportedEquiv_mem S W hSW e t).mp (by
      simpa only [t,se,LinearEquiv.apply_symm_apply] using hs)
    let t₁ : Rows (H₁ × W) H₂ H₃ Z := (t.1,0,0,0,t.2.2.2.2)
    let t₂ : Rows (H₁ × W) H₂ H₃ Z := (0,t.2.1,0,t.2.2.2.1,0)
    let t₃ : Rows (H₁ × W) H₂ H₃ Z := (0,0,t.2.2.1,0,0)
    let j := (LinearMap.inr K ((P₁ × P₂) × P₃) (D × D)).comp (transportedRowUpload se)
    have hp (u : Rows (H₁ × W) H₂ H₃ Z) (hu : u.1.2 = 0) : j (se u) ∈ Q :=
      ⟨se u,(supportedEquiv_mem S W hSW e u).mpr hu,rfl⟩
    have h₁ : j (se t₁) ∈ Q ⊓ A₁ K P₁ P₂ P₃ D := by
      refine ⟨hp t₁ ht,⟨(0,se t₁),?_⟩⟩
      simp [j,transportedRowUpload,rowUpload,t₁,side₁]
    have h₂ : j (se t₂) ∈ Q ⊓ A₂ K P₁ P₂ P₃ D := by
      refine ⟨hp t₂ rfl,⟨(0,se t₂),?_⟩⟩
      simp [j,transportedRowUpload,rowUpload,t₂,side₂]
    have h₃ : j (se t₃) ∈ Q ⊓ A₃ K P₁ P₂ P₃ D := by
      refine ⟨hp t₃ rfl,⟨(0,se t₃),?_⟩⟩
      simp [j,transportedRowUpload,rowUpload,t₃,side₃,← map_neg]
    have h₁' := (le_iSup (fun i : Three => Q ⊓
      ![A₁ K P₁ P₂ P₃ D,A₂ K P₁ P₂ P₃ D,A₃ K P₁ P₂ P₃ D] i) 0) h₁
    have h₂' := (le_iSup (fun i : Three => Q ⊓
      ![A₁ K P₁ P₂ P₃ D,A₂ K P₁ P₂ P₃ D,A₃ K P₁ P₂ P₃ D] i) 1) h₂
    have h₃' := (le_iSup (fun i : Three => Q ⊓
      ![A₁ K P₁ P₂ P₃ D,A₂ K P₁ P₂ P₃ D,A₃ K P₁ P₂ P₃ D] i) 2) h₃
    have hsum : t₁+t₂+t₃=t := by ext <;> simp [t₁,t₂,t₃]
    have hj : j (se t₁) + j (se t₂) + j (se t₃) = j s := by
      rw [← map_add,← map_add,← map_add,← map_add,hsum]
      simp [t]
    exact hj ▸ Submodule.add_mem _ (Submodule.add_mem _ h₁' h₂') h₃'
  · exact iSup_le fun _ => inf_le_left

end RetainedRows
end UploadBroadcast.ResidualRowShape
