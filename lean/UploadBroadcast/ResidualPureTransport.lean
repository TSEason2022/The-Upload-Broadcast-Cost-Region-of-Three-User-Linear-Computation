import UploadBroadcast.ResidualTaskAssembly

namespace UploadBroadcast
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F V : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup V] [Module K V]

theorem PassiveRetraction.mem_signal_iff_embed {T : Task K F} {R : Task K V}
    (r : PassiveRetraction T R) (i : Three) (x : V) :
    x ∈ R.U i ↔ r.embed x ∈ T.U i := by
  constructor
  · intro hx
    have h := (r.signalInclude i ⟨x,hx⟩).property
    rwa [r.signalInclude_coe] at h
  · intro hx
    have h := (r.signalProject i ⟨r.embed x,hx⟩).property
    rw [r.signalProject_coe] at h
    have he := LinearMap.congr_fun r.project_include x
    change r.project (r.embed x) = x at he
    rwa [he] at h

namespace ResidualTaskAssembly
open ResidualUpload
variable {P₁ P₂ P₃ D : Type*}
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]
  {task : Task K (Ambient P₁ P₂ P₃ D)}

/-- Pure-row membership is actual pure coefficient membership in the signal. -/
theorem DemandData.pureRows_iff (g : DemandData task) :
    (∀ d, d ∈ pureRows₁ task ↔ embedR (K := K) d ∈ task.U 0) ∧
    (∀ d, d ∈ pureRows₂ task ↔ embedV (K := K) d ∈ task.U 1) ∧
    (∀ d, d ∈ pureRows₃ task ↔ embedV (K := K) d ∈ task.U 2) := by
  refine ⟨?_,?_,?_⟩
  · intro d
    simpa [embedR,side₂] using (g.mem₁ (embedR (K := K) d)).symm
  · intro d
    simpa [embedV,side₁] using (g.mem₂ (embedV (K := K) d)).symm
  · intro d
    simpa [embedV,side₁] using (g.mem₃ (embedV (K := K) d)).symm

variable (task)
  (h₁ : task.A 0 = A₁ K P₁ P₂ P₃ D)
  (h₂ : task.A 1 = A₂ K P₁ P₂ P₃ D)
  (h₃ : task.A 2 = A₃ K P₁ P₂ P₃ D)

include h₁ h₂ h₃

/-- Unused-private deletion preserves each pure demand space exactly. -/
theorem privateTrim_pureRows :
    pureRows₁ (privateTrim task) = pureRows₁ task ∧
    pureRows₂ (privateTrim task) = pureRows₂ task ∧
    pureRows₃ (privateTrim task) = pureRows₃ task := by
  let g := selectedDemandData task h₁ h₂ h₃
  let t := selectedTrimData task h₁ h₂ h₃
  refine ⟨?_,?_,?_⟩
  · ext d
    rw [t.pureRows_iff.1,g.pureRows_iff.1]
    exact (trimRetraction task h₁ h₂ h₃).mem_signal_iff_embed 0 (embedR d)
  · ext d
    rw [t.pureRows_iff.2.1,g.pureRows_iff.2.1]
    exact (trimRetraction task h₁ h₂ h₃).mem_signal_iff_embed 1 (embedV d)
  · ext d
    rw [t.pureRows_iff.2.2,g.pureRows_iff.2.2]
    exact (trimRetraction task h₁ h₂ h₃).mem_signal_iff_embed 2 (embedV d)

omit h₁ h₂ h₃

private theorem mem_map_equiv_fixed (U : Submodule K F) (e : F ≃ₗ[K] F)
    (x : F) (hfix : e x = x) : x ∈ U.map e.toLinearMap ↔ x ∈ U := by
  constructor
  · rintro ⟨y,hy,he⟩
    have hyx : y = x := e.injective (he.trans hfix.symm)
    simpa only [hyx] using hy
  · intro hx
    exact ⟨x,hx,hfix⟩

include h₁ h₂ h₃

namespace DemandData
variable {task} (g : DemandData task)

/-- Private gauges fix all pure tripod coefficients, preserving purity. -/
theorem correctedTask_pureRows :
    pureRows₁ g.correctedTask = pureRows₁ task ∧
    pureRows₂ g.correctedTask = pureRows₂ task ∧
    pureRows₃ g.correctedTask = pureRows₃ task := by
  let t := selectedDemandData g.correctedTask
    (g.correctedTask_sides h₁ h₂ h₃).1
    (g.correctedTask_sides h₁ h₂ h₃).2.1
    (g.correctedTask_sides h₁ h₂ h₃).2.2
  refine ⟨?_,?_,?_⟩
  · ext d
    rw [t.pureRows_iff.1,g.pureRows_iff.1]
    apply mem_map_equiv_fixed
    ext <;> simp [embedR,side₂,privateGaugeShear,privateGauge]
  · ext d
    rw [t.pureRows_iff.2.1,g.pureRows_iff.2.1]
    apply mem_map_equiv_fixed
    ext <;> simp [embedV,side₁,privateGaugeShear,privateGauge]
  · ext d
    rw [t.pureRows_iff.2.2,g.pureRows_iff.2.2]
    apply mem_map_equiv_fixed
    ext <;> simp [embedV,side₁,privateGaugeShear,privateGauge]
end DemandData

/-- Genuine passive-row deletion restricts the pure spaces to retained rows. -/
theorem rowTrim_pureRows (R : Submodule K D)
    (hr₁ : ∀ x ∈ task.U 0, x.2.2 ∈ R)
    (hr₂ : ∀ x ∈ task.U 1, x.2.1 ∈ R)
    (hr₃ : ∀ x ∈ task.U 2, x.2.1 + x.2.2 ∈ R) :
    pureRows₁ (rowTrim task R) = (pureRows₁ task).comap R.subtype ∧
    pureRows₂ (rowTrim task R) = (pureRows₂ task).comap R.subtype ∧
    pureRows₃ (rowTrim task R) = (pureRows₃ task).comap R.subtype := by
  let g := selectedDemandData task h₁ h₂ h₃
  let t := selectedDemandData (rowTrim task R)
    (rowTrim_sides task h₁ h₂ h₃ R).1
    (rowTrim_sides task h₁ h₂ h₃ R).2.1
    (rowTrim_sides task h₁ h₂ h₃ R).2.2
  refine ⟨?_,?_,?_⟩
  · ext d
    rw [t.pureRows_iff.1]
    change _ ↔ (d : D) ∈ pureRows₁ task
    rw [g.pureRows_iff.1]
    exact (rowRetraction task h₁ h₂ h₃ R hr₁ hr₂ hr₃).mem_signal_iff_embed 0 (embedR d)
  · ext d
    rw [t.pureRows_iff.2.1]
    change _ ↔ (d : D) ∈ pureRows₂ task
    rw [g.pureRows_iff.2.1]
    exact (rowRetraction task h₁ h₂ h₃ R hr₁ hr₂ hr₃).mem_signal_iff_embed 1 (embedV d)
  · ext d
    rw [t.pureRows_iff.2.2]
    change _ ↔ (d : D) ∈ pureRows₃ task
    rw [g.pureRows_iff.2.2]
    exact (rowRetraction task h₁ h₂ h₃ R hr₁ hr₂ hr₃).mem_signal_iff_embed 2 (embedV d)

namespace DemandData
variable {task} (g : DemandData task)

theorem activeRowReduction_pureRows :
    pureRows₁ g.activeRowReduction = (pureRows₁ task).comap g.activeRows.subtype ∧
    pureRows₂ g.activeRowReduction = (pureRows₂ task).comap g.activeRows.subtype ∧
    pureRows₃ g.activeRowReduction = (pureRows₃ task).comap g.activeRows.subtype := by
  have h := rowTrim_pureRows g.correctedTask
    (g.correctedTask_sides h₁ h₂ h₃).1
    (g.correctedTask_sides h₁ h₂ h₃).2.1
    (g.correctedTask_sides h₁ h₂ h₃).2.2 g.activeRows
    g.correctedTask_rows.1 g.correctedTask_rows.2.1 g.correctedTask_rows.2.2
  rw [(g.correctedTask_pureRows h₁ h₂ h₃).1,(g.correctedTask_pureRows h₁ h₂ h₃).2.1,
    (g.correctedTask_pureRows h₁ h₂ h₃).2.2] at h
  exact h

theorem activeRowReduction_common_pure_eq_bot
    (hzero : pureRows₁ task ⊓ pureRows₂ task ⊓ pureRows₃ task = ⊥) :
    pureRows₁ g.activeRowReduction ⊓ pureRows₂ g.activeRowReduction ⊓ pureRows₃ g.activeRowReduction = ⊥ := by
  obtain ⟨h₁',h₂',h₃'⟩ := g.activeRowReduction_pureRows h₁ h₂ h₃
  rw [h₁',h₂',h₃',← Submodule.comap_inf,← Submodule.comap_inf,hzero]
  ext x
  change (x.val = 0) ↔ x = 0
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg Subtype.val h
end DemandData

/-- The fully constructed reduction preserves absence of common pure rows. -/
theorem canonicalReduction_common_pure_eq_bot
    (hzero : pureRows₁ task ⊓ pureRows₂ task ⊓ pureRows₃ task = ⊥) :
    pureRows₁ (canonicalReduction task h₁ h₂ h₃) ⊓
      pureRows₂ (canonicalReduction task h₁ h₂ h₃) ⊓
      pureRows₃ (canonicalReduction task h₁ h₂ h₃) = ⊥ := by
  apply (selectedTrimData task h₁ h₂ h₃).activeRowReduction_common_pure_eq_bot
    (privateTrim_sides task h₁ h₂ h₃).1
    (privateTrim_sides task h₁ h₂ h₃).2.1
    (privateTrim_sides task h₁ h₂ h₃).2.2
  rw [(privateTrim_pureRows task h₁ h₂ h₃).1,
    (privateTrim_pureRows task h₁ h₂ h₃).2.1,(privateTrim_pureRows task h₁ h₂ h₃).2.2]
  exact hzero
end ResidualTaskAssembly
end UploadBroadcast
