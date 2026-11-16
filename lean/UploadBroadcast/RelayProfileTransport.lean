import UploadBroadcast.RelayTask
import UploadBroadcast.ActiveTaskAssembly
import UploadBroadcast.NonzeroDefectRelays

namespace UploadBroadcast.Profile
open Module
variable {K F G : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup G] [Module K G] [FiniteDimensional K F] [FiniteDimensional K G]

omit [FiniteDimensional K F] [FiniteDimensional K G] in
theorem finrank_map_injective (f : F →ₗ[K] G) (hf : Function.Injective f) (A : Submodule K F) :
    finrank K (A.map f) = finrank K A :=
  (Submodule.equivMapOfInjective f hf A).finrank_eq.symm

theorem condRank_map_injective (f : F →ₗ[K] G) (hf : Function.Injective f) (A B : Submodule K F) :
    condRank (A.map f) (B.map f) = condRank A B := by
  unfold condRank
  rw [← Submodule.map_sup,finrank_map_injective f hf,finrank_map_injective f hf]

omit [FiniteDimensional K F] [FiniteDimensional K G] in
theorem totalDemand_imageTask (T : Task K F) (f : F →ₗ[K] G) (hf : Function.Injective f) :
    totalDemand (T.imageTask f) = totalDemand T := by
  simp only [totalDemand,Task.imageTask,finrank_map_injective f hf]

theorem firstEntry_imageTask (T : Task K F) (f : F →ₗ[K] G) (hf : Function.Injective f)
    (i j k : Three) : firstEntry (T.imageTask f) i j k = firstEntry T i j k := by
  unfold firstEntry
  rw [totalDemand_imageTask T f hf]
  simp only [Task.imageTask,← Submodule.map_inf f hf,← Submodule.map_sup,condRank_map_injective f hf]

theorem secondEntry_imageTask (T : Task K F) (f : F →ₗ[K] G) (hf : Function.Injective f)
    (i j k ell : Three) : secondEntry (T.imageTask f) i j k ell = secondEntry T i j k ell := by
  unfold secondEntry
  rw [totalDemand_imageTask T f hf]
  simp only [Task.imageTask,← Submodule.map_inf f hf,← Submodule.map_sup,condRank_map_injective f hf]

theorem entry_imageTask (T : Task K F) (f : F →ₗ[K] G) (hf : Function.Injective f) (r : Index) :
    entry (T.imageTask f) r = entry T r := by
  cases r with
  | inl r => exact firstEntry_imageTask T f hf _ _ _
  | inr r => exact secondEntry_imageTask T f hf _ _ _ _

theorem rankBound_imageTask (T : Task K F) (f : F →ₗ[K] G) (hf : Function.Injective f) :
    rankBound (T.imageTask f) = rankBound T := by
  simp only [rankBound,entry_imageTask T f hf]

end UploadBroadcast.Profile

namespace UploadBroadcast.Task
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- The intrinsic relay task and the ambient-intersection presentation are
literally related by the coefficient inclusion map. -/
theorem inducedRelay_image (T : Task K F) (P : Submodule K F) (hg : T.LocallyGenerated P) :
    (T.inducedRelay P hg).imageTask P.subtype = NonzeroDefectRelays.inducedTask T P hg := by
  have hA : ((T.inducedRelay P hg).imageTask P.subtype).A =
      (NonzeroDefectRelays.inducedTask T P hg).A := by
    funext i
    simp only [imageTask,inducedRelay,NonzeroDefectRelays.inducedTask,
      Submodule.map_comap_eq,Submodule.range_subtype,inf_comm]
  have hU : ((T.inducedRelay P hg).imageTask P.subtype).U =
      (NonzeroDefectRelays.inducedTask T P hg).U := by
    funext i
    simp only [imageTask,inducedRelay,NonzeroDefectRelays.inducedTask,
      Submodule.map_comap_eq,Submodule.range_subtype,inf_comm]
  cases h : (T.inducedRelay P hg).imageTask P.subtype
  cases h' : NonzeroDefectRelays.inducedTask T P hg
  simp_all only [mk.injEq]

variable [FiniteDimensional K F]

theorem inducedRelay_entry (T : Task K F) (P : Submodule K F) (hg : T.LocallyGenerated P)
    (r : Profile.Index) :
    Profile.entry (T.inducedRelay P hg) r = Profile.entry (NonzeroDefectRelays.inducedTask T P hg) r := by
  rw [← T.inducedRelay_image P hg,Profile.entry_imageTask _ _ P.subtype_injective]

theorem inducedRelay_rankBound (T : Task K F) (P : Submodule K F) (hg : T.LocallyGenerated P) :
    Profile.rankBound (T.inducedRelay P hg) = Profile.rankBound (NonzeroDefectRelays.inducedTask T P hg) := by
  simp only [Profile.rankBound,T.inducedRelay_entry P hg]

end UploadBroadcast.Task
