import UploadBroadcast.PassiveProduct

namespace UploadBroadcast.PassiveRetraction
variable {K F V W : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {T : Task K F} {R : Task K V} {S : Task K W}

/-- Composition retains the actual coefficient maps and locally recoverable
remainders, so it is valid for jointly encoded nonlinear tasks. -/
def trans (r : PassiveRetraction T R) (s : PassiveRetraction R S) : PassiveRetraction T S where
  project := s.project.comp r.project
  embed := r.embed.comp s.embed
  project_include := by
    apply LinearMap.ext
    intro x
    change s.project (r.project (r.embed (s.embed x))) = x
    rw [show r.project (r.embed (s.embed x)) = s.embed x from
      LinearMap.congr_fun r.project_include (s.embed x)]
    exact LinearMap.congr_fun s.project_include x
  sideProject i := (s.sideProject i).comp (r.sideProject i)
  sideInclude i := (r.sideInclude i).comp (s.sideInclude i)
  signalProject i := (s.signalProject i).comp (r.signalProject i)
  signalInclude i := (r.signalInclude i).comp (s.signalInclude i)
  localPart i := ((r.sideInclude i).comp ((s.localPart i).comp (r.signalProject i))) + r.localPart i
  sideProject_coe i x := by simp only [LinearMap.comp_apply,s.sideProject_coe,r.sideProject_coe]
  sideInclude_coe i x := by simp only [LinearMap.comp_apply,r.sideInclude_coe,s.sideInclude_coe]
  signalProject_coe i x := by simp only [LinearMap.comp_apply,s.signalProject_coe,r.signalProject_coe]
  signalInclude_coe i x := by simp only [LinearMap.comp_apply,r.signalInclude_coe,s.signalInclude_coe]
  reconstruct i x := by
    change r.embed (s.embed (s.project (r.project x))) +
      ((r.sideInclude i (s.localPart i (r.signalProject i x)) : F) + (r.localPart i x : F)) = x
    rw [r.sideInclude_coe,← add_assoc,← map_add]
    have hs := s.reconstruct i (r.signalProject i x)
    rw [r.signalProject_coe] at hs
    rw [hs]
    exact r.reconstruct i x
end UploadBroadcast.PassiveRetraction

namespace UploadBroadcast.PassiveRetraction
variable {K F V : Type*} [Field K] [Finite K]
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
  [FiniteDimensional K F] [FiniteDimensional K V]
  {T : Task K F} {R : Task K V}

/-- Concrete two-way coefficient retractions preserve the operational infimum
including all blocklengths and the regularized closure. -/
theorem uploadOptimum_eq (r : PassiveRetraction T R) : T.uploadOptimum = R.uploadOptimum := by
  unfold Task.uploadOptimum
  rw [r.costRegion_eq]
end UploadBroadcast.PassiveRetraction
