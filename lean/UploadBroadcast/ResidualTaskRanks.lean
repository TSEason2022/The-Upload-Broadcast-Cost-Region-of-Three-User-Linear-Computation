import UploadBroadcast.ResidualTaskAssembly

namespace UploadBroadcast.ResidualTaskAssembly.DemandData
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000
variable {K P₁ P₂ P₃ D : Type*} [Field K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]
  [FiniteDimensional K D]
  {task : Task K (ResidualUpload.Ambient P₁ P₂ P₃ D)} (g : DemandData task)

/-- The retained row dimension is the pure-row rank plus the rank of G on
ker B modulo pure rows, derived from the actual constructed coefficient space. -/
theorem activeRows_finrank :
    let S := pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task
    Module.finrank K g.activeRows = Module.finrank K S +
      Module.finrank K ((LinearMap.ker (incidence (task := task))).map
        (S.mkQ.comp g.relationRows)) := by
  dsimp only
  let S := pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task
  let M := (LinearMap.ker (incidence (task := task))).map g.relationRows
  have h := condRank_eq_finrank_quotient_image M S
  unfold condRank at h
  rw [← Submodule.map_comp] at h
  have hle : Module.finrank K S ≤ Module.finrank K ↥(S ⊔ M) :=
    Submodule.finrank_mono le_sup_left
  change Module.finrank K ↥(S ⊔ M) = _
  dsimp only [S,M] at h hle ⊢
  omega

/-- Removing the common pure rows leaves exactly the manuscript's pure
noncommon dimension plus the genuine zero-private mixed rank. -/
theorem noncommon_activeRows_finrank :
    let S := pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task
    let C := pureRows₁ task ⊓ pureRows₂ task ⊓ pureRows₃ task
    Module.finrank K g.activeRows - Module.finrank K C =
      (Module.finrank K S - Module.finrank K C) +
      Module.finrank K ((LinearMap.ker (incidence (task := task))).map
        (S.mkQ.comp g.relationRows)) := by
  dsimp only
  have h := g.activeRows_finrank
  dsimp only at h
  have hle : Module.finrank K ↥(pureRows₁ task ⊓ pureRows₂ task ⊓ pureRows₃ task) ≤
      Module.finrank K ↥(pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task) :=
    Submodule.finrank_mono ((inf_le_left.trans inf_le_left).trans
      (le_sup_left.trans le_sup_left))
  omega

omit [FiniteDimensional K D]

/-- The same retained mixed rank is the stacked-rank difference [B;G]-B
for the actual quotient row map. -/
theorem mixedRows_stacked_rank [FiniteDimensional K P₁] [FiniteDimensional K P₂]
    [FiniteDimensional K P₃] :
    let S := pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task
    Module.finrank K ((LinearMap.ker (incidence (task := task))).map
      (S.mkQ.comp g.relationRows)) =
      Module.finrank K (LinearMap.range ((incidence (task := task)).prod
        (S.mkQ.comp g.relationRows))) -
      Module.finrank K (LinearMap.range (incidence (task := task))) := by
  dsimp only
  have h := rank_restrict_ker (incidence (task := task))
    ((pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task).mkQ.comp g.relationRows)
  rwa [LinearMap.range_comp,Submodule.range_subtype] at h
end UploadBroadcast.ResidualTaskAssembly.DemandData
