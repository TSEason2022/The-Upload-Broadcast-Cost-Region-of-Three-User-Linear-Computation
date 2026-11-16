import UploadBroadcast.ExtensionGenerated

/-! Hom orthogonality propagates through the concrete extension closure. -/
namespace UploadBroadcast.QuiverRepresentation
universe u
variable {K V E : Type u} [Field K] {Q : Orientation V E}

/-- No actual arrow-preserving linear map exists other than zero. -/
def HomZero (R S : Rep K Q) : Prop := ∀ f : Hom R S, f=Hom.zero R S

theorem homZero_zero_source (R S : Rep K Q) (hR : IsZero R) : HomZero R S := by
  intro f
  apply Hom.ext
  intro v
  apply LinearMap.ext
  intro x
  rw [hR v x,map_zero]
  rfl

theorem homZero_zero_target (R S : Rep K Q) (hS : IsZero S) : HomZero R S := by
  intro f
  apply Hom.ext
  intro v
  apply LinearMap.ext
  intro x
  exact hS v (f.map v x)

theorem homZero_iso_source {R R' S : Rep K Q} (e : Iso R R')
    (h : HomZero R S) : HomZero R' S := by
  intro f
  have hz := h (f.comp e.toHom)
  apply Hom.ext
  intro v
  apply LinearMap.ext
  intro x
  have he := LinearMap.congr_fun (congrArg (fun g => g.map v) hz) ((e.map v).symm x)
  simpa only [Hom.comp,Hom.zero,Iso.toHom,LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,LinearMap.zero_apply] using he

theorem homZero_iso_target {R S S' : Rep K Q} (e : Iso S S')
    (h : HomZero R S) : HomZero R S' := by
  intro f
  have hz := h (e.symm.toHom.comp f)
  apply Hom.ext
  intro v
  apply LinearMap.ext
  intro x
  have he := LinearMap.congr_fun (congrArg (fun g => g.map v) hz) x
  have he' := congrArg (e.map v) he
  simpa only [Hom.comp,Hom.zero,Iso.toHom,Iso.symm,LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,LinearMap.zero_apply,map_zero] using he'

/-- A map out of an extension vanishes when it vanishes on both factors. -/
theorem homZero_extension_source (A B R : Rep K Q) (z : ArrowMaps B A)
    (hA : HomZero A R) (hB : HomZero B R) : HomZero (extension A B z) R := by
  intro f
  let fA : Hom A R :=
    { map := fun v => (f.map v).comp (LinearMap.inl K _ _)
      comm := by
        intro a
        apply LinearMap.ext
        intro x
        have hc := f.comm_apply a (x,0)
        change f.map (Q.target a) (A.arrow a x+z a 0,B.arrow a 0)=R.arrow a (f.map (Q.source a) (x,0)) at hc
        simpa only [map_zero,add_zero] using hc }
  have hfA := hA fA
  have hfst (v : V) (x : A.space v) : f.map v (x,0)=0 :=
    LinearMap.congr_fun (congrArg (fun g => g.map v) hfA) x
  let fB : Hom B R :=
    { map := fun v => (f.map v).comp (LinearMap.inr K _ _)
      comm := by
        intro a
        apply LinearMap.ext
        intro x
        have hc := f.comm_apply a (0,x)
        change f.map (Q.target a) (A.arrow a 0+z a x,B.arrow a x)=R.arrow a (f.map (Q.source a) (0,x)) at hc
        rw [map_zero,zero_add] at hc
        have hh : f.map (Q.target a) (z a x,B.arrow a x)=f.map (Q.target a) (0,B.arrow a x) := by
          have he : (z a x,B.arrow a x)=(z a x,0)+(0,B.arrow a x) := by simp
          rw [he,map_add,hfst,zero_add]
        rw [hh] at hc
        exact hc }
  have hfB := hB fB
  have hsnd (v : V) (x : B.space v) : f.map v (0,x)=0 :=
    LinearMap.congr_fun (congrArg (fun g => g.map v) hfB) x
  apply Hom.ext
  intro v
  apply LinearMap.ext
  intro x
  change f.map v x=0
  have he : x=(x.1,0)+(0,x.2) := by change x=(x.1+0,0+x.2); simp
  rw [he,map_add,hfst,hsnd,add_zero]

/-- A map into an extension vanishes when it vanishes into both factors. -/
theorem homZero_extension_target (R A B : Rep K Q) (z : ArrowMaps B A)
    (hA : HomZero R A) (hB : HomZero R B) : HomZero R (extension A B z) := by
  intro f
  let fB : Hom R B :=
    { map := fun v => (LinearMap.snd K _ _).comp (f.map v)
      comm := by
        intro a
        apply LinearMap.ext
        intro x
        exact congrArg Prod.snd (f.comm_apply a x) }
  have hfB := hB fB
  have hsnd (v : V) (x : R.space v) : (f.map v x).2=0 :=
    LinearMap.congr_fun (congrArg (fun g => g.map v) hfB) x
  let fA : Hom R A :=
    { map := fun v => (LinearMap.fst K _ _).comp (f.map v)
      comm := by
        intro a
        apply LinearMap.ext
        intro x
        have hc := congrArg Prod.fst (f.comm_apply a x)
        change (f.map (Q.target a) (R.arrow a x)).1=
          A.arrow a (f.map (Q.source a) x).1+z a (f.map (Q.source a) x).2 at hc
        rw [hsnd,map_zero,add_zero] at hc
        exact hc }
  have hfA := hA fA
  have hfst (v : V) (x : R.space v) : (f.map v x).1=0 :=
    LinearMap.congr_fun (congrArg (fun g => g.map v) hfA) x
  apply Hom.ext
  intro v
  apply LinearMap.ext
  intro x
  exact Prod.ext (hfst v x) (hsnd v x)

/-- Pairwise Hom orthogonality of two atom classes persists throughout their
finite actual extension closures. -/
theorem ExtensionGenerated.homZero {C D : Rep K Q → Prop}
    (hpair : ∀ R S, C R → D S → HomZero R S)
    {R S : Rep K Q} (hR : ExtensionGenerated C R) (hS : ExtensionGenerated D S) :
    HomZero R S := by
  induction hR with
  | zero R hz => exact homZero_zero_source R S hz
  | atom R hc =>
    induction hS with
    | zero S hz => exact homZero_zero_target R S hz
    | atom S hd => exact hpair R S hc hd
    | extension A B z _ _ ihA ihB => exact homZero_extension_target R A B z ihA ihB
    | iso e _ ih => exact homZero_iso_target e ih
  | extension A B z _ _ ihA ihB => exact homZero_extension_source A B S z ihA ihB
  | iso e _ ih => exact homZero_iso_source e ih

end UploadBroadcast.QuiverRepresentation
