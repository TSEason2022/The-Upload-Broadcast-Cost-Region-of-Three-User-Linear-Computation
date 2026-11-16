import UploadBroadcast.PassiveLinearCode

namespace UploadBroadcast
variable {K F V G W : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
  [AddCommGroup G] [Module K G] [AddCommGroup W] [Module K W]

private def submoduleProductMap {A : Submodule K F} {B : Submodule K V}
    {C : Submodule K G} {D : Submodule K W}
    (f : A →ₗ[K] B) (g : C →ₗ[K] D) : A.prod C →ₗ[K] B.prod D :=
  (Profile.submoduleProdEquiv B D).symm.toLinearMap.comp
    ((f.prodMap g).comp (Profile.submoduleProdEquiv A C).toLinearMap)

namespace PassiveRetraction

/-- Identity coefficient reduction, leaving all observations unchanged. -/
def refl (T : Task K F) : PassiveRetraction T T where
  project := LinearMap.id
  embed := LinearMap.id
  project_include := rfl
  sideProject _ := LinearMap.id
  sideInclude _ := LinearMap.id
  signalProject _ := LinearMap.id
  signalInclude _ := LinearMap.id
  localPart _ := 0
  sideProject_coe _ _ := rfl
  sideInclude_coe _ _ := rfl
  signalProject_coe _ _ := rfl
  signalInclude_coe _ _ := rfl
  reconstruct _ _ := add_zero _

/-- Product reductions act on the actual jointly encoded full task. Thus they
preserve every nonlinear code, even when uploads mix across the two factors. -/
def prod {T : Task K F} {R : Task K V} {S : Task K G} {Q : Task K W}
    (r : PassiveRetraction T R) (s : PassiveRetraction S Q) :
    PassiveRetraction (Profile.directSum T S) (Profile.directSum R Q) where
  project := r.project.prodMap s.project
  embed := r.embed.prodMap s.embed
  project_include := by
    apply LinearMap.ext
    intro x
    exact Prod.ext (LinearMap.congr_fun r.project_include x.1)
      (LinearMap.congr_fun s.project_include x.2)
  sideProject i := submoduleProductMap (r.sideProject i) (s.sideProject i)
  sideInclude i := submoduleProductMap (r.sideInclude i) (s.sideInclude i)
  signalProject i := submoduleProductMap (r.signalProject i) (s.signalProject i)
  signalInclude i := submoduleProductMap (r.signalInclude i) (s.signalInclude i)
  localPart i := submoduleProductMap (r.localPart i) (s.localPart i)
  sideProject_coe i x := Prod.ext (r.sideProject_coe i ⟨x.val.1,x.property.1⟩)
    (s.sideProject_coe i ⟨x.val.2,x.property.2⟩)
  sideInclude_coe i x := Prod.ext (r.sideInclude_coe i ⟨x.val.1,x.property.1⟩)
    (s.sideInclude_coe i ⟨x.val.2,x.property.2⟩)
  signalProject_coe i x := Prod.ext (r.signalProject_coe i ⟨x.val.1,x.property.1⟩)
    (s.signalProject_coe i ⟨x.val.2,x.property.2⟩)
  signalInclude_coe i x := Prod.ext (r.signalInclude_coe i ⟨x.val.1,x.property.1⟩)
    (s.signalInclude_coe i ⟨x.val.2,x.property.2⟩)
  reconstruct i x := Prod.ext (r.reconstruct i ⟨x.val.1,x.property.1⟩)
    (s.reconstruct i ⟨x.val.2,x.property.2⟩)

end PassiveRetraction
end UploadBroadcast
