import UploadBroadcast.CommonTripodAssembly
import UploadBroadcast.ResidualTaskRanks

namespace UploadBroadcast.CommonTripodRanks
open ResidualUpload ResidualTaskAssembly ResidualTaskAssembly.DemandData CommonTripodAssembly
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {K P₁ P₂ P₃ D : Type*} [Field K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]

/-- Intrinsic zero-private row witnesses use actual signal membership,
independently of any selected demand-graph lift. -/
def ActiveWitness (task : Task K (Ambient P₁ P₂ P₃ D)) (d : D) : Prop :=
  ∃ (x₁ : P₂ × P₃) (x₂ : P₁ × P₃) (x₃ : P₁ × P₂) (r₁ r₂ r₃ : D),
    demandLift₁ (K := K) (x₁,r₁) ∈ task.U 0 ∧
    demandLift₂ (K := K) (x₂,r₂) ∈ task.U 1 ∧
    demandLift₃ (K := K) (x₃,r₃) ∈ task.U 2 ∧
    x₂.1+x₃.1=0 ∧ x₁.1+x₃.2=0 ∧ x₁.2-x₂.2=0 ∧ d=r₁+r₂+r₃

/-- The active row space has a description independent of graph choices. -/
theorem activeRows_mem_iff {task : Task K (Ambient P₁ P₂ P₃ D)}
    (g : DemandData task) (d : D) : d ∈ g.activeRows ↔ ActiveWitness task d := by
  constructor
  · intro hd
    obtain ⟨s,hs,m,hm,rfl⟩ := Submodule.mem_sup.mp hd
    obtain ⟨s₁₂,hs₁₂,s₃,hs₃,rfl⟩ := Submodule.mem_sup.mp hs
    obtain ⟨s₁,hs₁,s₂,hs₂,rfl⟩ := Submodule.mem_sup.mp hs₁₂
    obtain ⟨x,hx,rfl⟩ := hm
    have hx' : ((x.1.2.val.1+x.2.val.1,x.1.1.val.1+x.2.val.2),
        x.1.1.val.2-x.1.2.val.2) = ((0,0),0) := hx
    have ha := congrArg (fun t => t.1.1) hx'
    have hb := congrArg (fun t => t.1.2) hx'
    have hc := congrArg Prod.snd hx'
    refine ⟨x.1.1.val,x.1.2.val,x.2.val,s₁+g.φ₁ x.1.1.val,
      s₂+g.φ₂ x.1.2.val,s₃+g.φ₃ x.2.val,?_,?_,?_,ha,hb,hc,?_⟩
    · apply (g.mem₁ _).mpr
      exact ⟨x.1.1.property,by simpa [demandLift₁] using hs₁⟩
    · apply (g.mem₂ _).mpr
      exact ⟨x.1.2.property,by simpa [demandLift₂] using hs₂⟩
    · apply (g.mem₃ _).mpr
      exact ⟨x.2.property,by simpa [demandLift₃] using hs₃⟩
    · simp only [relationRows,LinearMap.coe_mk,AddHom.coe_mk]
      abel
  · rintro ⟨x₁,x₂,x₃,r₁,r₂,r₃,hm₁,hm₂,hm₃,ha,hb,hc,rfl⟩
    have h₁ := (g.mem₁ _).mp hm₁
    have h₂ := (g.mem₂ _).mp hm₂
    have h₃ := (g.mem₃ _).mp hm₃
    simp only [demandLift₁,demandLift₂,demandLift₃,LinearMap.coe_mk,AddHom.coe_mk,
      add_zero] at h₁ h₂ h₃
    let x : Relations (task := task) := ((⟨x₁,h₁.1⟩,⟨x₂,h₂.1⟩),⟨x₃,h₃.1⟩)
    have hx : x ∈ LinearMap.ker (incidence (task := task)) := by
      change ((x₂.1+x₃.1,x₁.1+x₃.2),x₁.2-x₂.2) = ((0,0),0)
      simp only [ha,hb,hc]
    have hs : (r₁-g.φ₁ x₁)+(r₂-g.φ₂ x₂)+(r₃-g.φ₃ x₃) ∈
        pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task :=
      Submodule.add_mem_sup (Submodule.add_mem_sup h₁.2 h₂.2) h₃.2
    have hm : g.relationRows x ∈ (LinearMap.ker (incidence (task := task))).map g.relationRows :=
      ⟨x,hx,rfl⟩
    convert Submodule.add_mem_sup hs hm using 1
    simp only [relationRows,LinearMap.coe_mk,AddHom.coe_mk,x]
    abel

/-- In particular the selected graph lift does not affect the retained space. -/
theorem activeRows_choice_independent {task : Task K (Ambient P₁ P₂ P₃ D)}
    (g h : DemandData task) : g.activeRows = h.activeRows := by
  ext d
  rw [activeRows_mem_iff,activeRows_mem_iff]

noncomputable def complementProjection (C N : Submodule K D) (hc : IsCompl C N) : D →ₗ[K] N :=
  (LinearMap.snd K C N).comp (Submodule.prodEquivOfIsCompl C N hc).symm.toLinearMap

@[simp] theorem complementProjection_self (C N : Submodule K D) (hc : IsCompl C N) (n : N) :
    complementProjection C N hc n = n := by
  let e := Submodule.prodEquivOfIsCompl C N hc
  have he : e (0,n) = (n:D) := by simp [e]
  change (e.symm (n:D)).2 = n
  rw [← he,e.symm_apply_apply]

theorem complementProjection_remainder (C N : Submodule K D) (hc : IsCompl C N) (d : D) :
    d - (complementProjection C N hc d : D) ∈ C := by
  let e := Submodule.prodEquivOfIsCompl C N hc
  have he : ((e.symm d).1 : D) + ((e.symm d).2 : D) = d := e.apply_symm_apply d
  change d - ((e.symm d).2 : D) ∈ C
  rw [(eq_sub_iff_add_eq.mpr he).symm]
  exact (e.symm d).1.property

variable (task : Task K (Ambient P₁ P₂ P₃ D))
  (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D) (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
  (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)
  (N : Submodule K D) (hCN : IsCompl (commonRows task) N)

include hCN

/-- Active retained rows commute exactly with removal of the fully demanded
common tripod, for arbitrary choices of both lifted demand graphs. -/
theorem residual_activeRows (g : DemandData task)
    (h : DemandData (residualTask task h₀ h₁ h₂ N)) :
    h.activeRows = g.activeRows.comap N.subtype := by
  ext d
  change d ∈ h.activeRows ↔ (d:D) ∈ g.activeRows
  rw [activeRows_mem_iff,activeRows_mem_iff]
  constructor
  · rintro ⟨x₁,x₂,x₃,r₁,r₂,r₃,hm₁,hm₂,hm₃,ha,hb,hc,hd⟩
    refine ⟨x₁,x₂,x₃,r₁.val,r₂.val,r₃.val,hm₁,hm₂,hm₃,ha,hb,hc,?_⟩
    exact congrArg Subtype.val hd
  · rintro ⟨x₁,x₂,x₃,r₁,r₂,r₃,hm₁,hm₂,hm₃,ha,hb,hc,hd⟩
    let p := complementProjection (commonRows task) N hCN
    have hc₁ := complementProjection_remainder (commonRows task) N hCN r₁
    have hc₂ := complementProjection_remainder (commonRows task) N hCN r₂
    have hc₃ := complementProjection_remainder (commonRows task) N hCN r₃
    refine ⟨x₁,x₂,x₃,p r₁,p r₂,p r₃,?_,?_,?_,ha,hb,hc,?_⟩
    · have hs := (task.U 0).sub_mem hm₁
        (commonEmbed_mem task h₀ h₁ h₂ 0 (0,⟨r₁-(p r₁:D),hc₁⟩))
      change residualEmbed N (demandLift₁ (K := K) (x₁,p r₁)) ∈ task.U 0
      convert hs using 1
      ext <;> simp [residualEmbed,demandLift₁,commonEmbed]
    · have hs := (task.U 1).sub_mem hm₂
        (commonEmbed_mem task h₀ h₁ h₂ 1 (⟨r₂-(p r₂:D),hc₂⟩,0))
      change residualEmbed N (demandLift₂ (K := K) (x₂,p r₂)) ∈ task.U 1
      convert hs using 1
      ext <;> simp [residualEmbed,demandLift₂,commonEmbed]
    · have hs := (task.U 2).sub_mem hm₃
        (commonEmbed_mem task h₀ h₁ h₂ 2 (⟨r₃-(p r₃:D),hc₃⟩,0))
      change residualEmbed N (demandLift₃ (K := K) (x₃,p r₃)) ∈ task.U 2
      convert hs using 1
      ext <;> simp [residualEmbed,demandLift₃,commonEmbed]
    · calc
        d = p (d:D) := (complementProjection_self _ _ hCN d).symm
        _ = p r₁+p r₂+p r₃ := by rw [hd,map_add,map_add]

/-- Common-row deletion subtracts exactly the common dimension from the
intrinsic active row rank, regardless of graph-lift choices. -/
theorem residual_activeRows_finrank [FiniteDimensional K D]
    (g : DemandData task) (h : DemandData (residualTask task h₀ h₁ h₂ N)) :
    Module.finrank K h.activeRows = Module.finrank K g.activeRows - Module.finrank K (commonRows task) := by
  have hC : commonRows task ≤ g.activeRows := by
    intro d hd
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left hd.1.1))
  have hs : commonRows task ⊔ (N ⊓ g.activeRows) = g.activeRows := by
    apply le_antisymm (sup_le hC inf_le_right)
    intro d hd
    let p := complementProjection (commonRows task) N hCN
    have hc := complementProjection_remainder (commonRows task) N hCN d
    have hn : (p d:D) ∈ g.activeRows := by
      have hh := g.activeRows.sub_mem hd (hC hc)
      simpa only [sub_sub_cancel] using hh
    have hh := Submodule.add_mem_sup hc (show (p d:D) ∈ N ⊓ g.activeRows from ⟨(p d).property,hn⟩)
    simpa only [p,sub_add_cancel] using hh
  have hi : commonRows task ⊓ (N ⊓ g.activeRows) = ⊥ :=
    (hCN.disjoint.mono_right inf_le_left).eq_bot
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (commonRows task) (N ⊓ g.activeRows)
  rw [hs,hi,finrank_bot,add_zero] at hdim
  have hm : h.activeRows.map N.subtype = N ⊓ g.activeRows := by
    rw [residual_activeRows task h₀ h₁ h₂ N hCN g h,Submodule.map_comap_subtype]
  have hr := Submodule.finrank_map_subtype_eq N h.activeRows
  rw [hm] at hr
  omega

end UploadBroadcast.CommonTripodRanks
