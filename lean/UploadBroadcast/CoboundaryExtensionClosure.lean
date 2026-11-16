import UploadBroadcast.QuiverExtensions

/-! Extension-closure of the explicit quiver coboundary obstruction. -/
namespace UploadBroadcast.QuiverRepresentation
universe u
variable {K V E : Type u} [Field K] {Q : Orientation V E}

/-- Vanishing of the explicit extension obstruction is preserved when the
source is an extension of two sources with vanishing obstruction. -/
theorem coboundary_surjective_extension_source
    (R S A : Rep K Q) (z : ArrowMaps S R)
    (hR : Function.Surjective (coboundary R A))
    (hS : Function.Surjective (coboundary S A)) :
    Function.Surjective (coboundary (extension R S z) A) := by
  intro w
  let wR : ArrowMaps R A := fun a => (w a).comp (LinearMap.inl K _ _)
  obtain ⟨gR,hgR⟩ := hR wR
  let wS : ArrowMaps S A := fun a => (w a).comp (LinearMap.inr K _ _) -
    (gR (Q.target a)).comp (z a)
  obtain ⟨gS,hgS⟩ := hS wS
  refine ⟨fun v => (gR v).comp (LinearMap.fst K _ _)+(gS v).comp (LinearMap.snd K _ _),?_⟩
  funext a
  apply LinearMap.ext
  intro x
  have hR' := LinearMap.congr_fun (congrFun hgR a) x.1
  have hS' := LinearMap.congr_fun (congrFun hgS a) x.2
  change gR (Q.target a) (R.arrow a x.1)-A.arrow a (gR (Q.source a) x.1)=w a (x.1,0) at hR'
  change gS (Q.target a) (S.arrow a x.2)-A.arrow a (gS (Q.source a) x.2)=
    w a (0,x.2)-gR (Q.target a) (z a x.2) at hS'
  change gR (Q.target a) (R.arrow a x.1+z a x.2)+gS (Q.target a) (S.arrow a x.2)-
    A.arrow a (gR (Q.source a) x.1+gS (Q.source a) x.2)=w a x
  have hw : w a x=w a (x.1,0)+w a (0,x.2) := by
    rw [←map_add]
    congr 1
    change x=(x.1+0,0+x.2)
    simp
  rw [map_add,map_add,hw]
  rw [sub_eq_iff_eq_add.mp hR',sub_eq_iff_eq_add.mp hS']
  abel

/-- Vanishing of the explicit extension obstruction is also preserved when
the target is an extension of two targets with vanishing obstruction. -/
theorem coboundary_surjective_extension_target
    (A R S : Rep K Q) (z : ArrowMaps S R)
    (hR : Function.Surjective (coboundary A R))
    (hS : Function.Surjective (coboundary A S)) :
    Function.Surjective (coboundary A (extension R S z)) := by
  intro w
  let wS : ArrowMaps A S := fun a => (LinearMap.snd K _ _).comp (w a)
  obtain ⟨gS,hgS⟩ := hS wS
  let wR : ArrowMaps A R := fun a => (LinearMap.fst K _ _).comp (w a)+
    (z a).comp (gS (Q.source a))
  obtain ⟨gR,hgR⟩ := hR wR
  refine ⟨fun v => (gR v).prod (gS v),?_⟩
  funext a
  apply LinearMap.ext
  intro x
  have hR' := LinearMap.congr_fun (congrFun hgR a) x
  have hS' := LinearMap.congr_fun (congrFun hgS a) x
  change gR (Q.target a) (A.arrow a x)-R.arrow a (gR (Q.source a) x)=
    (w a x).1+z a (gS (Q.source a) x) at hR'
  change gS (Q.target a) (A.arrow a x)-S.arrow a (gS (Q.source a) x)=(w a x).2 at hS'
  apply Prod.ext
  · change gR (Q.target a) (A.arrow a x)-
      (R.arrow a (gR (Q.source a) x)+z a (gS (Q.source a) x))=(w a x).1
    rw [sub_eq_iff_eq_add.mp hR']
    abel
  · exact hS'


/-- Coboundary surjectivity is invariant under an actual source isomorphism. -/
theorem coboundary_surjective_iso_source {R R' S : Rep K Q} (e : Iso R R')
    (h : Function.Surjective (coboundary R S)) :
    Function.Surjective (coboundary R' S) := by
  intro w
  let w' : ArrowMaps R S := fun a => (w a).comp (e.map (Q.source a)).toLinearMap
  obtain ⟨g,hg⟩ := h w'
  refine ⟨fun v => (g v).comp (e.map v).symm.toLinearMap,?_⟩
  funext a
  apply LinearMap.ext
  intro x
  have hg' := LinearMap.congr_fun (congrFun hg a) ((e.map (Q.source a)).symm x)
  change g (Q.target a) (R.arrow a ((e.map (Q.source a)).symm x))-
    S.arrow a (g (Q.source a) ((e.map (Q.source a)).symm x))=
    w a (e.map (Q.source a) ((e.map (Q.source a)).symm x)) at hg'
  change g (Q.target a) ((e.map (Q.target a)).symm (R'.arrow a x))-
    S.arrow a (g (Q.source a) ((e.map (Q.source a)).symm x))=w a x
  have hc := e.symm.toHom.comm_apply a x
  change (e.map (Q.target a)).symm (R'.arrow a x)=
    R.arrow a ((e.map (Q.source a)).symm x) at hc
  rw [hc]
  simpa only [LinearEquiv.apply_symm_apply] using hg'

/-- Coboundary surjectivity is invariant under an actual target isomorphism. -/
theorem coboundary_surjective_iso_target {R S S' : Rep K Q} (e : Iso S S')
    (h : Function.Surjective (coboundary R S)) :
    Function.Surjective (coboundary R S') := by
  intro w
  let w' : ArrowMaps R S := fun a => (e.map (Q.target a)).symm.toLinearMap.comp (w a)
  obtain ⟨g,hg⟩ := h w'
  refine ⟨fun v => (e.map v).toLinearMap.comp (g v),?_⟩
  funext a
  apply LinearMap.ext
  intro x
  have hg' := LinearMap.congr_fun (congrFun hg a) x
  change g (Q.target a) (R.arrow a x)-S.arrow a (g (Q.source a) x)=
    (e.map (Q.target a)).symm (w a x) at hg'
  change e.map (Q.target a) (g (Q.target a) (R.arrow a x))-
    S'.arrow a (e.map (Q.source a) (g (Q.source a) x))=w a x
  have hc := e.toHom.comm_apply a (g (Q.source a) x)
  change e.map (Q.target a) (S.arrow a (g (Q.source a) x))=
    S'.arrow a (e.map (Q.source a) (g (Q.source a) x)) at hc
  rw [←hc,←map_sub,hg',LinearEquiv.apply_symm_apply]

end UploadBroadcast.QuiverRepresentation
