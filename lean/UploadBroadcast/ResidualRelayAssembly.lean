import UploadBroadcast.ResidualRowCompletion
import UploadBroadcast.CommonTripodAssembly
import UploadBroadcast.ZeroCommonRowNormalForm
import UploadBroadcast.RelayLinearComposition

/-! Select a minimum-dimensional actual relay from constructed demand graphs
and row coordinates, then transport it back to the original residual task. -/
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

namespace UploadBroadcast.ResidualRelayAssembly
open ResidualUpload ResidualTaskAssembly ResidualRowCompletion
variable {K P₁ P₂ P₃ H₁ H₂ H₃ Z : Type*} [Field K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup H₁] [Module K H₁]
  [AddCommGroup H₂] [Module K H₂] [AddCommGroup H₃] [Module K H₃]
  [AddCommGroup Z] [Module K Z]
local notation "R" => Rows H₁ H₂ H₃ Z
local notation "F" => Ambient P₁ P₂ P₃ R

/-- The actual signal spaces equal side plus pure rows plus the actual
private-domain graph. This is proved from the exact quotient characterization. -/
theorem signal_graphs (task : Task K F)
    (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ R) (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ R)
    (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ R) (g : DemandData task) :
    task.U 0 = A₁ K P₁ P₂ P₃ R ⊔ LinearMap.range (pureR (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (pureRows₁ task)) ⊔
      LinearMap.range (mixed₁ (P₁ := P₁) (privateDomain₁ task) (g.φ₁.domRestrict _)) ∧
    task.U 1 = A₂ K P₁ P₂ P₃ R ⊔ LinearMap.range (pureV (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (pureRows₂ task)) ⊔
      LinearMap.range (mixed₂ (P₂ := P₂) (privateDomain₂ task) (g.φ₂.domRestrict _)) ∧
    task.U 2 = A₃ K P₁ P₂ P₃ R ⊔ LinearMap.range (pureV (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (pureRows₃ task)) ⊔
      LinearMap.range (mixed₃ (P₃ := P₃) (privateDomain₃ task) (g.φ₃.domRestrict _)) := by
  constructor
  · apply le_antisymm
    · intro u hu
      obtain ⟨hd,hp⟩ := (g.mem₁ u).mp hu
      let x : privateDomain₁ task := ⟨(u.1.1.2,u.1.2),hd⟩
      let d : pureRows₁ task := ⟨u.2.2-g.φ₁ (u.1.1.2,u.1.2),hp⟩
      have hs : side₁ (u.1.1.1,u.2.1) ∈ A₁ K P₁ P₂ P₃ R := ⟨_,rfl⟩
      have hp' : pureR (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (pureRows₁ task) d ∈
          LinearMap.range (pureR (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (pureRows₁ task)) := ⟨_,rfl⟩
      have hm : mixed₁ (P₁ := P₁) _ (g.φ₁.domRestrict _) x ∈
          LinearMap.range (mixed₁ (P₁ := P₁) _ (g.φ₁.domRestrict _)) := ⟨_,rfl⟩
      convert Submodule.add_mem_sup (Submodule.add_mem_sup hs hp') hm using 1
      ext <;> simp [side₁,pureR,mixed₁,x,d]
    · apply sup_le
      · apply sup_le
        · simpa only [h₀] using task.side_le_signal 0
        · rintro _ ⟨d,rfl⟩
          apply (g.mem₁ _).mpr
          simp [pureR, (privateDomain₁ task).zero_mem, d.property]
      · rintro _ ⟨x,rfl⟩
        apply (g.mem₁ _).mpr
        simp [mixed₁, x.property, (pureRows₁ task).zero_mem]
  constructor
  · apply le_antisymm
    · intro u hu
      obtain ⟨hd,hp⟩ := (g.mem₂ u).mp hu
      let x : privateDomain₂ task := ⟨(u.1.1.1,u.1.2),hd⟩
      let d : pureRows₂ task := ⟨u.2.1-g.φ₂ (u.1.1.1,u.1.2),hp⟩
      have hs : side₂ (u.1.1.2,u.2.2) ∈ A₂ K P₁ P₂ P₃ R := ⟨_,rfl⟩
      have hp' : pureV (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (pureRows₂ task) d ∈
          LinearMap.range (pureV (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (pureRows₂ task)) := ⟨_,rfl⟩
      have hm : mixed₂ (P₂ := P₂) _ (g.φ₂.domRestrict _) x ∈
          LinearMap.range (mixed₂ (P₂ := P₂) _ (g.φ₂.domRestrict _)) := ⟨_,rfl⟩
      convert Submodule.add_mem_sup (Submodule.add_mem_sup hs hp') hm using 1
      ext <;> simp [side₂,pureV,mixed₂,x,d]
    · apply sup_le
      · apply sup_le
        · simpa only [h₁] using task.side_le_signal 1
        · rintro _ ⟨d,rfl⟩
          apply (g.mem₂ _).mpr
          simp [pureV, (privateDomain₂ task).zero_mem, d.property]
      · rintro _ ⟨x,rfl⟩
        apply (g.mem₂ _).mpr
        simp [mixed₂, x.property, (pureRows₂ task).zero_mem]
  · apply le_antisymm
    · intro u hu
      obtain ⟨hd,hp⟩ := (g.mem₃ u).mp hu
      let x : privateDomain₃ task := ⟨(u.1.1.1,u.1.1.2),hd⟩
      let d : pureRows₃ task := ⟨u.2.1+u.2.2-g.φ₃ (u.1.1.1,u.1.1.2),hp⟩
      have hs : side₃ (u.1.2,u.2.2) ∈ A₃ K P₁ P₂ P₃ R := ⟨_,rfl⟩
      have hp' : pureV (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (pureRows₃ task) d ∈
          LinearMap.range (pureV (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (pureRows₃ task)) := ⟨_,rfl⟩
      have hm : mixed₃ (P₃ := P₃) _ (g.φ₃.domRestrict _) x ∈
          LinearMap.range (mixed₃ (P₃ := P₃) _ (g.φ₃.domRestrict _)) := ⟨_,rfl⟩
      convert Submodule.add_mem_sup (Submodule.add_mem_sup hs hp') hm using 1
      ext <;> simp [side₃,pureV,mixed₃,x,d] <;> abel
    · apply sup_le
      · apply sup_le
        · simpa only [h₂] using task.side_le_signal 2
        · rintro _ ⟨d,rfl⟩
          apply (g.mem₃ _).mpr
          simp [pureV, (privateDomain₃ task).zero_mem, d.property]
      · rintro _ ⟨x,rfl⟩
        apply (g.mem₃ _).mpr
        simp [mixed₃, x.property, (pureRows₃ task).zero_mem]

/-- Actual minimum-size row relay for a task whose pure spaces satisfy the
row-coordinate vanishing conditions; all mixed demand maps are constructed. -/
theorem exists_relay_in_rows [FiniteDimensional K P₁] [FiniteDimensional K P₂]
    [FiniteDimensional K P₃] [FiniteDimensional K H₁] [FiniteDimensional K H₂]
    [FiniteDimensional K H₃] [FiniteDimensional K Z]
    (task : Task K F)
    (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ R) (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ R)
    (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ R)
    (b₀ : ∀ d ∈ pureRows₁ task, d.1=0 ∧ d.2.2.2.2=0)
    (b₁ : ∀ d ∈ pureRows₂ task, d.2.1=0 ∧ d.2.2.2.1=0)
    (b₂ : ∀ d ∈ pureRows₃ task, d.2.2.1=0) :
    ∃ Q : Submodule K F, task.LocallyGenerated Q ∧ task.RelayFeasible Q ∧
      Module.finrank K Q = Module.finrank K P₁+Module.finrank K P₂+Module.finrank K P₃+Module.finrank K R := by
  let g := selectedDemandData task h₀ h₁ h₂
  obtain ⟨hu₀,hu₁,hu₂⟩ := signal_graphs task h₀ h₁ h₂ g
  obtain ⟨Q,hq,hf,hr⟩ := generated_signals_row_completion (pureRows₁ task) (pureRows₂ task) (pureRows₃ task)
    b₀ b₁ b₂ (privateDomain₁ task) (privateDomain₂ task) (privateDomain₃ task)
    (g.φ₁.domRestrict _) (g.φ₂.domRestrict _) (g.φ₃.domRestrict _)
  have ha : ∀ i : Three, task.A i = ![A₁ K P₁ P₂ P₃ R,A₂ K P₁ P₂ P₃ R,A₃ K P₁ P₂ P₃ R] i := by
    intro i
    fin_cases i <;> assumption
  refine ⟨Q,?_,?_,hr⟩
  · simpa only [Task.LocallyGenerated,ha] using hq
  · intro i
    fin_cases i
    · change task.U 0 ≤ task.A 0 ⊔ Q
      rw [hu₀,h₀]
      exact hf 0
    · change task.U 1 ≤ task.A 1 ⊔ Q
      rw [hu₁,h₁]
      exact hf 1
    · change task.U 2 ≤ task.A 2 ⊔ Q
      rw [hu₂,h₂]
      exact hf 2

section RowTransport
variable {D E : Type*} [AddCommGroup D] [Module K D] [AddCommGroup E] [Module K E]

def rowEquiv (e : D ≃ₗ[K] E) : Ambient P₁ P₂ P₃ D ≃ₗ[K] Ambient P₁ P₂ P₃ E :=
  (LinearEquiv.refl K ((P₁ × P₂) × P₃)).prodCongr (e.prodCongr e)

theorem row_sides (e : D ≃ₗ[K] E) :
    (A₁ K P₁ P₂ P₃ D).map (rowEquiv e).toLinearMap = A₁ K P₁ P₂ P₃ E ∧
    (A₂ K P₁ P₂ P₃ D).map (rowEquiv e).toLinearMap = A₂ K P₁ P₂ P₃ E ∧
    (A₃ K P₁ P₂ P₃ D).map (rowEquiv e).toLinearMap = A₃ K P₁ P₂ P₃ E := by
  refine ⟨?_,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨u,⟨⟨p,t⟩,rfl⟩,rfl⟩
      exact ⟨(p,e t),by ext <;> simp [rowEquiv,side₁]⟩
    · rintro ⟨⟨p,t⟩,rfl⟩
      exact ⟨side₁ (p,e.symm t),⟨_,rfl⟩,by ext <;> simp [rowEquiv,side₁]⟩
  · ext x
    constructor
    · rintro ⟨u,⟨⟨p,t⟩,rfl⟩,rfl⟩
      exact ⟨(p,e t),by ext <;> simp [rowEquiv,side₂]⟩
    · rintro ⟨⟨p,t⟩,rfl⟩
      exact ⟨side₂ (p,e.symm t),⟨_,rfl⟩,by ext <;> simp [rowEquiv,side₂]⟩
  · ext x
    constructor
    · rintro ⟨u,⟨⟨p,t⟩,rfl⟩,rfl⟩
      exact ⟨(p,e t),by ext <;> simp [rowEquiv,side₃]⟩
    · rintro ⟨⟨p,t⟩,rfl⟩
      exact ⟨side₃ (p,e.symm t),⟨_,rfl⟩,by ext <;> simp [rowEquiv,side₃]⟩

theorem row_task_sides (task : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D) (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D) (e : D ≃ₗ[K] E) :
    (Profile.mapTask (rowEquiv e) task).A 0 = A₁ K P₁ P₂ P₃ E ∧
    (Profile.mapTask (rowEquiv e) task).A 1 = A₂ K P₁ P₂ P₃ E ∧
    (Profile.mapTask (rowEquiv e) task).A 2 = A₃ K P₁ P₂ P₃ E := by
  simpa only [Profile.mapTask,h₀,h₁,h₂] using row_sides (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) e

/-- Actual pure intersections transport by the row equivalence. -/
theorem row_task_pure (task : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D) (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D) (e : D ≃ₗ[K] E) :
    pureRows₁ (Profile.mapTask (rowEquiv e) task) = (pureRows₁ task).comap e.symm.toLinearMap ∧
    pureRows₂ (Profile.mapTask (rowEquiv e) task) = (pureRows₂ task).comap e.symm.toLinearMap ∧
    pureRows₃ (Profile.mapTask (rowEquiv e) task) = (pureRows₃ task).comap e.symm.toLinearMap := by
  obtain ⟨ha,hb,hc⟩ := row_task_sides task h₀ h₁ h₂ e
  let q := Profile.mapTask (rowEquiv e) task
  refine ⟨?_,?_,?_⟩
  · ext t
    change t ∈ pureRows₁ q ↔ e.symm t ∈ pureRows₁ task
    rw [CommonTripodAssembly.pureRows₁_mem_iff q ha hb hc,
      CommonTripodAssembly.pureRows₁_mem_iff task h₀ h₁ h₂]
    change embedR (K := K) t ∈ (task.U 0).map (rowEquiv e).toLinearMap ↔ _
    rw [Submodule.mem_map_equiv]
    change (((0,0),0),(e.symm 0,e.symm t)) ∈ task.U 0 ↔ (((0,0),0),(0,e.symm t)) ∈ task.U 0
    simp only [map_zero]
  · ext t
    change t ∈ pureRows₂ q ↔ e.symm t ∈ pureRows₂ task
    rw [CommonTripodAssembly.pureRows₂_mem_iff q ha hb hc,
      CommonTripodAssembly.pureRows₂_mem_iff task h₀ h₁ h₂]
    change embedV (K := K) t ∈ (task.U 1).map (rowEquiv e).toLinearMap ↔ _
    rw [Submodule.mem_map_equiv]
    change (((0,0),0),(e.symm t,e.symm 0)) ∈ task.U 1 ↔ (((0,0),0),(e.symm t,0)) ∈ task.U 1
    simp only [map_zero]
  · ext t
    change t ∈ pureRows₃ q ↔ e.symm t ∈ pureRows₃ task
    rw [CommonTripodAssembly.pureRows₃_mem_iff q ha hb hc,
      CommonTripodAssembly.pureRows₃_mem_iff task h₀ h₁ h₂]
    change embedV (K := K) t ∈ (task.U 2).map (rowEquiv e).toLinearMap ↔ _
    rw [Submodule.mem_map_equiv]
    change (((0,0),0),(e.symm t,e.symm 0)) ∈ task.U 2 ↔ (((0,0),0),(e.symm t,0)) ∈ task.U 2
    simp only [map_zero]
end RowTransport

section RelayTransport
variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Local generation and feasibility transport together under ambient coordinates. -/
theorem map_relay (task : Task K V) (e : V ≃ₗ[K] W) (Q : Submodule K V)
    (hl : task.LocallyGenerated Q) (hf : task.RelayFeasible Q) :
    (Profile.mapTask e task).LocallyGenerated (Q.map e.toLinearMap) ∧
      (Profile.mapTask e task).RelayFeasible (Q.map e.toLinearMap) := by
  constructor
  · change Q.map e.toLinearMap = ⨆ i, Q.map e.toLinearMap ⊓ (task.A i).map e.toLinearMap
    conv_lhs => rw [show Q = ⨆ i, Q ⊓ task.A i from hl,Submodule.map_iSup]
    congr 1
    funext i
    exact Submodule.map_inf _ e.injective
  · intro i
    exact (Submodule.map_mono (f := e.toLinearMap) (hf i)).trans_eq (Submodule.map_sup _ _ _)

private theorem task_eq_of_spaces {T S : Task K V} (hA : T.A = S.A) (hU : T.U = S.U) : T = S := by
  cases T; cases S; cases hA; cases hU; rfl

theorem mapTask_inverse (task : Task K V) (e : W ≃ₗ[K] V) :
    Profile.mapTask e (Profile.mapTask e.symm task) = task := by
  have hh (A : Submodule K V) : (A.map e.symm.toLinearMap).map e.toLinearMap = A := by
    ext x
    simp [Submodule.mem_map_equiv]
  have ha : (Profile.mapTask e (Profile.mapTask e.symm task)).A = task.A := by funext i; exact hh _
  have hu : (Profile.mapTask e (Profile.mapTask e.symm task)).U = task.U := by funext i; exact hh _
  exact task_eq_of_spaces ha hu
end RelayTransport

section FinalRelay
variable {D : Type*} [AddCommGroup D] [Module K D]
  [FiniteDimensional K P₁] [FiniteDimensional K P₂] [FiniteDimensional K P₃]
  [FiniteDimensional K D]

omit [FiniteDimensional K D] in
/-- Row coordinates supply an actual relay in the original residual space. -/
theorem exists_relay_of_row_coordinates
    [FiniteDimensional K H₁] [FiniteDimensional K H₂]
    [FiniteDimensional K H₃] [FiniteDimensional K Z]
    (task : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D) (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D) (e : R ≃ₗ[K] D)
    (b₀ : ∀ t, e t ∈ pureRows₁ task → t.1=0 ∧ t.2.2.2.2=0)
    (b₁ : ∀ t, e t ∈ pureRows₂ task → t.2.1=0 ∧ t.2.2.2.1=0)
    (b₂ : ∀ t, e t ∈ pureRows₃ task → t.2.2.1=0) :
    ∃ Q : Submodule K (Ambient P₁ P₂ P₃ D),
      task.LocallyGenerated Q ∧ task.RelayFeasible Q ∧
      Module.finrank K Q = Module.finrank K P₁+Module.finrank K P₂+
        Module.finrank K P₃+Module.finrank K D := by
  let q := Profile.mapTask (rowEquiv e.symm) task
  obtain ⟨ha,hb,hc⟩ := row_task_sides task h₀ h₁ h₂ e.symm
  obtain ⟨pa,pb,pc⟩ := row_task_pure task h₀ h₁ h₂ e.symm
  obtain ⟨Q,hl,hf,hr⟩ := exists_relay_in_rows q ha hb hc
    (fun t ht => b₀ t (by simpa only [q,pa,Submodule.mem_comap,
      LinearEquiv.symm_symm,LinearEquiv.coe_coe] using ht))
    (fun t ht => b₁ t (by simpa only [q,pb,Submodule.mem_comap,
      LinearEquiv.symm_symm,LinearEquiv.coe_coe] using ht))
    (fun t ht => b₂ t (by simpa only [q,pc,Submodule.mem_comap,
      LinearEquiv.symm_symm,LinearEquiv.coe_coe] using ht))
  have he : rowEquiv e.symm = (rowEquiv (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) e).symm := rfl
  have hq : Profile.mapTask (rowEquiv e) q = task := by
    dsimp [q]
    rw [he]
    exact mapTask_inverse task _
  obtain ⟨hlocal,hfeasible⟩ := map_relay q (rowEquiv e) Q hl hf
  refine ⟨Q.map (rowEquiv e).toLinearMap,?_,?_,?_⟩
  · simpa only [hq] using hlocal
  · simpa only [hq] using hfeasible
  · rw [(rowEquiv e).finrank_map_eq,hr,e.finrank_eq]

/-- No row certificate is assumed: zero common pure rows suffice to construct
an actual original-field, locally generated feasible relay of residual size. -/
theorem exists_relay_of_zero_common
    (task : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D) (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)
    (hz : pureRows₁ task ⊓ pureRows₂ task ⊓ pureRows₃ task = ⊥) :
    ∃ Q : Submodule K (Ambient P₁ P₂ P₃ D),
      task.LocallyGenerated Q ∧ task.RelayFeasible Q ∧
      Module.finrank K Q = Module.finrank K P₁+Module.finrank K P₂+
        Module.finrank K P₃+Module.finrank K D := by
  obtain ⟨c⟩ := ZeroCommonRowNormalForm.exists_chart
    (pureRows₁ task) (pureRows₂ task) (pureRows₃ task) hz
  exact exists_relay_of_row_coordinates task h₀ h₁ h₂ c.equiv c.first c.second c.third
/-- The selected relay yields an actual scalar linear upload code over the
original field, with no field-size condition. -/
theorem exists_scalar_linear_upload [Finite K]
    (task : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D) (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)
    (hz : pureRows₁ task ⊓ pureRows₂ task ⊓ pureRows₃ task = ⊥) :
    ∃ r : Three → ℕ, ∃ c : task.LinearCode 1 r
      (Module.finrank K P₁+Module.finrank K P₂+Module.finrank K P₃+Module.finrank K D),
      (∑ i,r i) = Module.finrank K P₁+Module.finrank K P₂+Module.finrank K P₃+Module.finrank K D ∧
      c.toCode.uploadCost ≤ Module.finrank K P₁+Module.finrank K P₂+Module.finrank K P₃+Module.finrank K D ∧
      c.toCode.broadcastCost ≤ Module.finrank K P₁+Module.finrank K P₂+Module.finrank K P₃+Module.finrank K D := by
  obtain ⟨Q,hl,hf,hr⟩ := exists_relay_of_zero_common task h₀ h₁ h₂ hz
  have hh := RelayLinearComposition.full_relay_linear_code task Q hl hf
  rw [hr] at hh
  simpa only [Nat.cast_add] using hh

end FinalRelay

end UploadBroadcast.ResidualRelayAssembly
