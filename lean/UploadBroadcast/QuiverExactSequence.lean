import UploadBroadcast.QuiverExtensions

namespace UploadBroadcast.QuiverRepresentation
universe u
variable {K : Type u} [Field K]

/-- A pointwise exact sequence of vector spaces has an actual product chart
respecting both the injected factor and the quotient map. -/
theorem exists_linear_exact_split {A B X : Type u}
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup X] [Module K X]
    (i : A →ₗ[K] X) (p : X →ₗ[K] B) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : LinearMap.ker p = LinearMap.range i) :
    ∃ e : (A × B) ≃ₗ[K] X, (∀ a, e (a,0) = i a) ∧ ∀ x, p (e x) = x.2 := by
  classical
  obtain ⟨sec,hsec⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hp)
  have hpi (a : A) : p (i a) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [hex]
    exact ⟨a,rfl⟩
  have hps (b : B) : p (sec b) = b := LinearMap.congr_fun hsec b
  let f := i.coprod sec
  have hf (x : A × B) : p (f x) = x.2 := by simp [f,LinearMap.coprod_apply,map_add,hpi,hps]
  have hinj : Function.Injective f := by
    intro x y h
    have h₂ : x.2 = y.2 := by simpa only [hf] using congrArg p h
    have h₁ : i x.1 = i y.1 := by
      change i x.1 + sec x.2 = i y.1 + sec y.2 at h
      rw [h₂] at h
      exact add_right_cancel h
    exact Prod.ext (hi h₁) h₂
  have hsurj : Function.Surjective f := by
    intro x
    have hx : x-sec (p x) ∈ LinearMap.ker p := by
      change p (x-sec (p x)) = 0
      rw [map_sub,hps,sub_self]
    rw [hex] at hx
    obtain ⟨a,ha⟩ := hx
    refine ⟨(a,p x),?_⟩
    change i a+sec (p x)=x
    rw [ha,sub_add_cancel]
  let e := LinearEquiv.ofBijective f ⟨hinj,hsurj⟩
  refine ⟨e,?_,hf⟩
  intro a
  change i a+sec 0=i a
  simp

variable {V E : Type u} {Q : Orientation V E}

/-- Every actual pointwise exact quiver sequence has a checked block-arrow
presentation, with inclusion and projection compatibility recorded. -/
theorem exists_extension_presentation (R S X : Rep K Q) (i : Hom R X) (p : Hom X S)
    (hi : ∀ v, Function.Injective (i.map v)) (hp : ∀ v, Function.Surjective (p.map v))
    (hex : ∀ v, LinearMap.ker (p.map v) = LinearMap.range (i.map v)) :
    ∃ z : ArrowMaps S R, ∃ e : Iso (extension R S z) X,
      (∀ v r, e.map v (r,0) = i.map v r) ∧ ∀ v x, p.map v (e.map v x) = x.2 := by
  classical
  choose e he₀ he₂ using fun v => exists_linear_exact_split (i.map v) (p.map v) (hi v) (hp v) (hex v)
  let z : ArrowMaps S R := fun a =>
    (LinearMap.fst K _ _).comp ((e (Q.target a)).symm.toLinearMap.comp
      ((X.arrow a).comp ((e (Q.source a)).toLinearMap.comp (LinearMap.inr K _ _))))
  have inv_i (v : V) (r : R.space v) : (e v).symm (i.map v r) = (r,0) := by
    rw [← he₀ v r,LinearEquiv.symm_apply_apply]
  have inv_p (v : V) (x : X.space v) : ((e v).symm x).2 = p.map v x := by
    have h := he₂ v ((e v).symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hx (a : E) (x : R.space (Q.source a) × S.space (Q.source a)) :
      X.arrow a (e (Q.source a) x) = i.map (Q.target a) (R.arrow a x.1) +
        X.arrow a (e (Q.source a) (0,x.2)) := by
    have hs : e (Q.source a) x = e (Q.source a) (x.1,0) + e (Q.source a) (0,x.2) := by
      rw [← map_add]
      congr 1
      simp
    rw [hs,map_add,he₀,← i.comm_apply]
  let iso : Iso (extension R S z) X :=
    { map := e
      comm := by
        intro a
        apply LinearMap.ext
        intro x
        apply (e (Q.target a)).symm.injective
        change (e (Q.target a)).symm (e (Q.target a)
          (R.arrow a x.1+z a x.2,S.arrow a x.2)) =
          (e (Q.target a)).symm (X.arrow a (e (Q.source a) x))
        rw [LinearEquiv.symm_apply_apply,hx,map_add,inv_i]
        apply Prod.ext
        · rfl
        · change S.arrow a x.2 = 0+((e (Q.target a)).symm (X.arrow a (e (Q.source a) (0,x.2)))).2
          rw [zero_add,inv_p,p.comm_apply,he₂] }
  exact ⟨z,iso,he₀,he₂⟩

end UploadBroadcast.QuiverRepresentation
