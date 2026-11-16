import UploadBroadcast.QuiverEuler
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace UploadBroadcast.QuiverRepresentation
universe u
variable {K V E : Type u} [Field K]
  [Fintype V] [Fintype E] {Q : Orientation V E}

omit [Fintype V] [Fintype E] in
theorem Hom.comm_apply {R S : Rep K Q} (f : Hom R S) (a : E) (x : R.space (Q.source a)) :
    f.map (Q.target a) (R.arrow a x) = S.arrow a (f.map (Q.source a) x) :=
  LinearMap.congr_fun (f.comm a) x

abbrev VertexMaps (R S : Rep K Q) := ∀ v, R.space v →ₗ[K] S.space v
abbrev ArrowMaps (R S : Rep K Q) := ∀ a, R.space (Q.source a) →ₗ[K] S.space (Q.target a)

/-- The actual linear commutator constraints defining quiver morphisms. -/
def coboundary (R S : Rep K Q) : VertexMaps R S →ₗ[K] ArrowMaps R S where
  toFun g a := (g (Q.target a)).comp (R.arrow a) - (S.arrow a).comp (g (Q.source a))
  map_add' f g := by ext a x; simp [sub_add_sub_comm]
  map_smul' c f := by ext a x; simp [smul_sub]

omit [Fintype V] [Fintype E] in
theorem ker_coboundary (R S : Rep K Q) : LinearMap.ker (coboundary R S) = homSpace R S := by
  ext g
  simp only [LinearMap.mem_ker,coboundary,LinearMap.coe_mk,AddHom.coe_mk,
    funext_iff,Pi.zero_apply,sub_eq_zero]
  rfl

variable (R S : Rep K Q)
  [∀ v, FiniteDimensional K (R.space v)] [∀ v, FiniteDimensional K (S.space v)]

theorem euler_as_dimensions : eulerForm Q (dimension R) (dimension S) =
    (Module.finrank K (VertexMaps R S) : ℤ) - Module.finrank K (ArrowMaps R S) := by
  simp only [VertexMaps,ArrowMaps,Module.finrank_pi_fintype,Module.finrank_linearMap,
    eulerForm,dimension,Nat.cast_sum,Nat.cast_mul]

theorem coboundary_surjective_of_hom_eq_euler
    (h : (Module.finrank K (Hom R S) : ℤ) = eulerForm Q (dimension R) (dimension S)) :
    Function.Surjective (coboundary R S) := by
  have hk : Module.finrank K (LinearMap.ker (coboundary R S)) = Module.finrank K (Hom R S) := by
    rw [ker_coboundary]
    exact (homSpaceLinearEquiv R S).finrank_eq.symm
  have hd := (coboundary R S).finrank_range_add_finrank_ker
  rw [hk] at hd
  have hd' : (Module.finrank K (LinearMap.range (coboundary R S)) : ℤ) +
      Module.finrank K (Hom R S) = Module.finrank K (VertexMaps R S) := by exact_mod_cast hd
  rw [h,euler_as_dimensions] at hd'
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  exact_mod_cast (show (Module.finrank K (LinearMap.range (coboundary R S)) : ℤ) =
    Module.finrank K (ArrowMaps R S) by linarith)

/-- A vertexwise split extension with its actual off-diagonal arrow maps. -/
def extension (z : ArrowMaps S R) : Rep K Q where
  space v := R.space v × S.space v
  arrow a := ((R.arrow a).comp (LinearMap.fst K _ _) +
    (z a).comp (LinearMap.snd K _ _)).prod ((S.arrow a).comp (LinearMap.snd K _ _))

private def shear {A B : Type u} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (g : B →ₗ[K] A) : (A × B) ≃ₗ[K] (A × B) where
  toFun x := (x.1+g x.2,x.2)
  invFun x := (x.1-g x.2,x.2)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp [add_add_add_comm]
  map_smul' c x := by simp [smul_add]

/-- Vanishing of the explicit linear obstruction splits every extension;
no Ext functor or unproved classification theorem is assumed. -/
theorem extension_splits_of_hom_eq_euler (z : ArrowMaps S R)
    (h : (Module.finrank K (Hom S R) : ℤ) = eulerForm Q (dimension S) (dimension R)) :
    Nonempty (Iso (R.prod S) (extension R S z)) := by
  obtain ⟨g,hg⟩ := coboundary_surjective_of_hom_eq_euler S R h z
  refine ⟨{ map := fun v => shear (g v), comm := ?_ }⟩
  intro a
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change (R.arrow a) x.1 + g (Q.target a) ((S.arrow a) x.2) =
      (R.arrow a) (x.1+g (Q.source a) x.2) + z a x.2
    have hz := LinearMap.congr_fun (congrFun hg a) x.2
    change g (Q.target a) ((S.arrow a) x.2) - (R.arrow a) (g (Q.source a) x.2) = z a x.2 at hz
    rw [map_add,sub_eq_iff_eq_add.mp hz]
    abel
  · rfl

/-- A linear map whose image lies in an injected subspace has a genuine
linear lift through that injection. -/
private theorem factor_injective {A X Y : Type u} [AddCommGroup A] [Module K A]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (i : A →ₗ[K] X) (hi : Function.Injective i) (d : Y →ₗ[K] X)
    (hd : LinearMap.range d ≤ LinearMap.range i) :
    ∃ z : Y →ₗ[K] A, i.comp z = d := by
  let e := LinearEquiv.ofInjective i hi
  let q := d.codRestrict (LinearMap.range i) (fun y => hd ⟨y,rfl⟩)
  refine ⟨e.symm.toLinearMap.comp q,?_⟩
  apply LinearMap.ext
  intro y
  exact congrArg Subtype.val (e.apply_symm_apply (q y))

omit [Fintype V] [Fintype E] in
/-- Explicit Hom lifting across a pointwise exact sequence. This is the
extension-vanishing consequence needed for separating regular factor classes. -/
theorem lift_hom_of_coboundary_surjective
    (A B X U : Rep K Q)
    (i : Hom A X) (p : Hom X B)
    (hi : ∀ v, Function.Injective (i.map v))
    (hp : ∀ v, Function.Surjective (p.map v))
    (hex : ∀ v, LinearMap.ker (p.map v) = LinearMap.range (i.map v))
    (hsurj : Function.Surjective (coboundary U A))
    (f : Hom U B) : ∃ g : Hom U X, p.comp g = f := by
  classical
  choose sec hsec using fun v => (p.map v).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (hp v))
  let l : VertexMaps U X := fun v => (sec v).comp (f.map v)
  have hl (v : V) (x : U.space v) : p.map v (l v x) = f.map v x :=
    LinearMap.congr_fun (hsec v) (f.map v x)
  let d : ArrowMaps U X := coboundary U X l
  have hd (a : E) : LinearMap.range (d a) ≤ LinearMap.range (i.map (Q.target a)) := by
    rintro _ ⟨x,rfl⟩
    rw [← hex]
    change p.map (Q.target a) (l (Q.target a) (U.arrow a x) - X.arrow a (l (Q.source a) x)) = 0
    rw [map_sub,hl,p.comm_apply a,hl,
      f.comm_apply a,sub_self]
  choose z hz using fun a => factor_injective (i.map (Q.target a)) (hi _) (d a) (hd a)
  obtain ⟨g,hg⟩ := hsurj z
  let out : Hom U X :=
    { map := fun v => l v - (i.map v).comp (g v)
      comm := by
        intro a
        apply LinearMap.ext
        intro x
        have hz' : l (Q.target a) (U.arrow a x) - X.arrow a (l (Q.source a) x) =
            i.map (Q.target a) (z a x) := (LinearMap.congr_fun (hz a) x).symm
        have hg' : g (Q.target a) (U.arrow a x) - A.arrow a (g (Q.source a) x) = z a x :=
          LinearMap.congr_fun (congrFun hg a) x
        change l (Q.target a) (U.arrow a x) - i.map (Q.target a) (g (Q.target a) (U.arrow a x)) =
          X.arrow a (l (Q.source a) x - i.map (Q.source a) (g (Q.source a) x))
        rw [sub_eq_iff_eq_add.mp hz',sub_eq_iff_eq_add.mp hg',map_add,
          i.comm_apply a,map_sub]
        abel }
  refine ⟨out,?_⟩
  apply Hom.ext
  intro v
  apply LinearMap.ext
  intro x
  have hzero : p.map v (i.map v (g v x)) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [hex]
    exact ⟨g v x,rfl⟩
  change p.map v (l v x-i.map v (g v x)) = f.map v x
  rw [map_sub,hl,hzero,sub_zero]

/-- Numeric Euler equality supplies the surjectivity needed by the explicit lift. -/
theorem lift_hom_of_hom_eq_euler
    (A B X U : Rep K Q)
    [∀ v, FiniteDimensional K (A.space v)] [∀ v, FiniteDimensional K (U.space v)]
    (i : Hom A X) (p : Hom X B)
    (hi : ∀ v, Function.Injective (i.map v))
    (hp : ∀ v, Function.Surjective (p.map v))
    (hex : ∀ v, LinearMap.ker (p.map v) = LinearMap.range (i.map v))
    (hHom : (Module.finrank K (Hom U A) : ℤ) = eulerForm Q (dimension U) (dimension A))
    (f : Hom U B) : ∃ g : Hom U X, p.comp g = f :=
  lift_hom_of_coboundary_surjective A B X U i p hi hp hex
    (coboundary_surjective_of_hom_eq_euler U A hHom) f

end UploadBroadcast.QuiverRepresentation
