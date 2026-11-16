import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi

/-!
# Oriented representations and local star maps

An orientation is part of the data. No injectivity restriction is imposed on
arrows, so kernels and quotient spaces arising in reflection are representable.
The local reflection construction is developed in `ReflectionEquivalence`.
-/
namespace UploadBroadcast.QuiverRepresentation

universe u v w

@[ext] structure Orientation (V : Type v) (E : Type w) where
  source : E → V
  target : E → V

/-- Reverse precisely the arrows incident with a vertex. -/
def Orientation.reflect {V : Type v} {E : Type w} [DecidableEq V]
    (Q : Orientation V E) (s : V) : Orientation V E where
  source e := if Q.source e = s ∨ Q.target e = s then Q.target e else Q.source e
  target e := if Q.source e = s ∨ Q.target e = s then Q.source e else Q.target e

def Orientation.IsSink {V : Type v} {E : Type w} (Q : Orientation V E) (s : V) : Prop :=
  ∀ e, Q.source e ≠ s

def Orientation.IsSource {V : Type v} {E : Type w} (Q : Orientation V E) (s : V) : Prop :=
  ∀ e, Q.target e ≠ s

variable (K : Type u) [Field K] {V : Type v} {E : Type w}

structure Rep (Q : Orientation V E) where
  space : V → Type u
  [add : ∀ i, AddCommGroup (space i)]
  [module : ∀ i, Module K (space i)]
  arrow : ∀ e, space (Q.source e) →ₗ[K] space (Q.target e)

attribute [instance] Rep.add Rep.module

variable {K} {Q : Orientation V E}

structure Hom (R S : Rep K Q) where
  map : ∀ i, R.space i →ₗ[K] S.space i
  comm : ∀ e, (map (Q.target e)).comp (R.arrow e) =
    (S.arrow e).comp (map (Q.source e))

namespace Hom

def id (R : Rep K Q) : Hom R R where
  map _ := LinearMap.id
  comm _ := by simp

def comp {R S T : Rep K Q} (g : Hom S T) (f : Hom R S) : Hom R T where
  map i := (g.map i).comp (f.map i)
  comm e := by
    rw [LinearMap.comp_assoc, f.comm, ← LinearMap.comp_assoc, g.comm,
      LinearMap.comp_assoc]

@[ext] theorem ext {R S : Rep K Q} (f g : Hom R S)
    (h : ∀ i, f.map i = g.map i) : f = g := by
  cases f; cases g; simp_all only [mk.injEq]; exact funext h

def zero (R S : Rep K Q) : Hom R S where
  map _ := 0
  comm _ := by simp

end Hom

/-- The endomorphism-idempotent formulation used by reflection.
Its equivalence to direct-sum indecomposability is proved below. -/
def IdempotentsTrivial (R : Rep K Q) : Prop :=
  ∀ a : Hom R R, a.comp a = a → a = Hom.zero R R ∨ a = Hom.id R

/-- Isomorphism of actual oriented representations, commuting with every arrow. -/
structure Iso (R S : Rep K Q) where
  map : ∀ i, R.space i ≃ₗ[K] S.space i
  comm : ∀ e, (map (Q.target e)).toLinearMap.comp (R.arrow e) =
    (S.arrow e).comp (map (Q.source e)).toLinearMap

namespace Iso

def refl (R : Rep K Q) : Iso R R where
  map _ := LinearEquiv.refl K _
  comm _ := by simp

def toHom {R S : Rep K Q} (f : Iso R S) : Hom R S := ⟨fun i => (f.map i).toLinearMap, f.comm⟩

def symm {R S : Rep K Q} (f : Iso R S) : Iso S R where
  map v := (f.map v).symm
  comm e := by
    apply LinearMap.ext
    intro x
    apply (f.map (Q.target e)).injective
    have hh := LinearMap.congr_fun (f.comm e) ((f.map (Q.source e)).symm x)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hh.symm

def trans {R S T : Rep K Q} (f : Iso R S) (g : Iso S T) : Iso R T where
  map v := (f.map v).trans (g.map v)
  comm e := by
    change ((g.map (Q.target e)).toLinearMap.comp (f.map (Q.target e)).toLinearMap).comp
      (R.arrow e) = (T.arrow e).comp
        ((g.map (Q.source e)).toLinearMap.comp (f.map (Q.source e)).toLinearMap)
    rw [LinearMap.comp_assoc, f.comm, ← LinearMap.comp_assoc, g.comm, LinearMap.comp_assoc]

@[simp] theorem symm_comp {R S : Rep K Q} (f : Iso R S) :
    f.symm.toHom.comp f.toHom = Hom.id R := by
  apply Hom.ext
  intro v
  ext x
  exact (f.map v).symm_apply_apply x

@[simp] theorem comp_symm {R S : Rep K Q} (f : Iso R S) :
    f.toHom.comp f.symm.toHom = Hom.id S := by
  apply Hom.ext
  intro v
  ext x
  exact (f.map v).apply_symm_apply x

/-- Build an isomorphism from two mutually inverse representation morphisms. -/
def ofInverse {R S : Rep K Q} (f : Hom R S) (g : Hom S R)
    (hgf : g.comp f = Hom.id R) (hfg : f.comp g = Hom.id S) : Iso R S where
  map v := {
    toLinearMap := f.map v
    invFun := g.map v
    left_inv := fun x => LinearMap.congr_fun (congrArg (fun h => h.map v) hgf) x
    right_inv := fun x => LinearMap.congr_fun (congrArg (fun h => h.map v) hfg) x }
  comm := f.comm

end Iso

/-- Vertexwise direct sum (binary product) with the actual block-diagonal arrows. -/
def Rep.prod (R S : Rep K Q) : Rep K Q where
  space v := R.space v × S.space v
  arrow e := (R.arrow e).prodMap (S.arrow e)

/-- Zero means every vertex space is zero. -/
def IsZero (R : Rep K Q) : Prop := ∀ v (x : R.space v), x = 0

/-- Direct-sum indecomposability, stated without chosen coordinates or dimensions. -/
def Indecomposable (R : Rep K Q) : Prop :=
  ¬ IsZero R ∧ ∀ S T : Rep K Q, Iso R (S.prod T) → IsZero S ∨ IsZero T

/-- Kernels of an endomorphism form a subrepresentation. -/
def kernelRep {R : Rep K Q} (a : Hom R R) : Rep K Q where
  space v := LinearMap.ker (a.map v)
  arrow e := ((R.arrow e).comp (LinearMap.ker (a.map (Q.source e))).subtype).codRestrict
    (LinearMap.ker (a.map (Q.target e))) (by
      intro x
      change a.map (Q.target e) (R.arrow e x.val) = 0
      have h := LinearMap.congr_fun (a.comm e) x.val
      simpa using h)

/-- Images of an endomorphism form a subrepresentation. -/
def imageRep {R : Rep K Q} (a : Hom R R) : Rep K Q where
  space v := LinearMap.range (a.map v)
  arrow e := ((R.arrow e).comp (LinearMap.range (a.map (Q.source e))).subtype).codRestrict
    (LinearMap.range (a.map (Q.target e))) (by
      rintro ⟨_, y, rfl⟩
      exact ⟨R.arrow e y, LinearMap.congr_fun (a.comm e) y⟩)

/-- The elementary splitting of a linear idempotent. -/
def splitIdempotent {X : Type u} [AddCommGroup X] [Module K X]
    (p : X →ₗ[K] X) (hpp : p.comp p = p) :
    X ≃ₗ[K] (LinearMap.ker p × LinearMap.range p) where
  toFun x := (⟨x - p x, by
    change p (x - p x) = 0
    rw [map_sub, show p (p x) = p x from LinearMap.congr_fun hpp x, sub_self]⟩, ⟨p x, ⟨x, rfl⟩⟩)
  invFun x := x.1.val + x.2.val
  left_inv x := sub_add_cancel x (p x)
  right_inv x := by
    obtain ⟨x, y⟩ := x
    obtain ⟨y, z, rfl⟩ := y
    apply Prod.ext <;> apply Subtype.ext
    · change x.val + p z - p (x.val + p z) = x.val
      rw [map_add, show p x.val = 0 from x.property,
        show p (p z) = p z from LinearMap.congr_fun hpp z, zero_add, add_sub_cancel_right]
    · change p (x.val + p z) = p z
      rw [map_add, show p x.val = 0 from x.property,
        show p (p z) = p z from LinearMap.congr_fun hpp z, zero_add]
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext
    · change x + y - p (x + y) = (x - p x) + (y - p y)
      rw [map_add]; abel
    · exact map_add p x y
  map_smul' c x := by
    apply Prod.ext <;> apply Subtype.ext
    · change c • x - p (c • x) = c • (x - p x)
      rw [map_smul, smul_sub]
    · exact map_smul p c x

/-- Every representation idempotent splits as an actual quiver isomorphism. -/
def splitIso {R : Rep K Q} (a : Hom R R) (haa : a.comp a = a) :
    Iso R ((kernelRep a).prod (imageRep a)) where
  map v := splitIdempotent (a.map v) (congrArg (fun b => b.map v) haa)
  comm e := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;> apply Subtype.ext
    · change R.arrow e x - a.map (Q.target e) (R.arrow e x) =
        R.arrow e (x - a.map (Q.source e) x)
      rw [map_sub, show a.map (Q.target e) (R.arrow e x) =
        R.arrow e (a.map (Q.source e) x) from LinearMap.congr_fun (a.comm e) x]
    · exact LinearMap.congr_fun (a.comm e) x

/-- A direct-sum indecomposable has no nontrivial idempotents. -/
theorem Indecomposable.idempotentsTrivial {R : Rep K Q} (h : Indecomposable R) :
    IdempotentsTrivial R := by
  intro a haa
  rcases h.2 (kernelRep a) (imageRep a) (splitIso a haa) with hk | hi
  · right
    apply Hom.ext
    intro v
    apply LinearMap.ext
    intro x
    have hx := congrArg Subtype.val (hk v ((splitIdempotent (a.map v)
      (congrArg (fun b => b.map v) haa) x).1))
    change x - a.map v x = 0 at hx
    exact (sub_eq_zero.mp hx).symm
  · left
    apply Hom.ext
    intro v
    apply LinearMap.ext
    intro x
    exact congrArg Subtype.val (hi v ⟨a.map v x, ⟨x, rfl⟩⟩)

/-- Pull back the projection onto the first factor of any actual decomposition. -/
def decompositionIdempotent {R S T : Rep K Q} (h : Iso R (S.prod T)) : Hom R R where
  map v := (h.map v).symm.toLinearMap.comp
    ((LinearMap.inl K (S.space v) (T.space v)).comp
      ((LinearMap.fst K (S.space v) (T.space v)).comp (h.map v).toLinearMap))
  comm e := by
    apply LinearMap.ext
    intro x
    apply (h.map (Q.target e)).injective
    have hc := LinearMap.congr_fun (h.comm e) x
    have hd := LinearMap.congr_fun (h.comm e)
      ((h.map (Q.source e)).symm ((h.map (Q.source e) x).1, 0))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply,
      LinearMap.fst_apply, LinearEquiv.apply_symm_apply] at *
    change ((h.map (Q.target e) (R.arrow e x)).1, 0) =
      h.map (Q.target e) (R.arrow e ((h.map (Q.source e)).symm ((h.map (Q.source e) x).1, 0)))
    rw [hd]
    simp only [Rep.prod, LinearMap.prodMap_apply, LinearEquiv.apply_symm_apply, map_zero]
    exact congrArg (fun y => (y.1, (0 : T.space (Q.target e)))) hc

theorem decompositionIdempotent_sq {R S T : Rep K Q} (h : Iso R (S.prod T)) :
    (decompositionIdempotent h).comp (decompositionIdempotent h) = decompositionIdempotent h := by
  apply Hom.ext
  intro v
  apply LinearMap.ext
  intro x
  change (h.map v).symm ((h.map v ((h.map v).symm ((h.map v x).1, 0))).1, 0) =
    (h.map v).symm ((h.map v x).1, 0)
  rw [LinearEquiv.apply_symm_apply]

/-- The idempotent criterion is equivalent to genuine direct-sum indecomposability,
provided the representation itself is nonzero. -/
theorem indecomposable_iff (R : Rep K Q) :
    Indecomposable R ↔ ¬ IsZero R ∧ IdempotentsTrivial R := by
  constructor
  · intro h; exact ⟨h.1, h.idempotentsTrivial⟩
  · rintro ⟨hne, h⟩
    refine ⟨hne, ?_⟩
    intro S T iso
    rcases h (decompositionIdempotent iso) (decompositionIdempotent_sq iso) with hz | hi
    · left
      intro v x
      have hx := LinearMap.congr_fun (congrArg (fun b => b.map v) hz)
        ((iso.map v).symm (x, 0))
      have hh := congrArg (iso.map v) hx
      change (iso.map v ((iso.map v).symm ((iso.map v ((iso.map v).symm (x, 0))).1, 0))) = iso.map v 0 at hh
      simpa using congrArg Prod.fst hh
    · right
      intro v x
      have hx := LinearMap.congr_fun (congrArg (fun b => b.map v) hi)
        ((iso.map v).symm (0, x))
      have hh := congrArg (iso.map v) hx
      change (iso.map v ((iso.map v).symm ((iso.map v ((iso.map v).symm (0, x))).1, 0))) =
        iso.map v ((iso.map v).symm (0, x)) at hh
      simpa using (congrArg Prod.snd hh).symm

/-- The affine E6 tree, with orientation represented separately from incidence. -/
inductive E6Vertex where
  | center
  | middle (arm : Fin 3)
  | outer (arm : Fin 3)
  deriving DecidableEq

inductive E6Edge where
  | inner (arm : Fin 3)
  | outer (arm : Fin 3)
  deriving DecidableEq

def inwardE6 : Orientation E6Vertex E6Edge where
  source
    | .inner i => .middle i
    | .outer i => .outer i
  target
    | .inner _ => .center
    | .outer i => .middle i

section Attachment

variable {I : Type u} [Fintype I] [DecidableEq I]

/-- Attach a new sink to an arbitrary peripheral quiver. Parallel edges and
multiple incidences at one neighbour are allowed. -/
def attachSinkOrientation (Q : Orientation V E) (neighbour : I → V) :
    Orientation (Option V) (Sum E I) where
  source
    | .inl e => some (Q.source e)
    | .inr i => some (neighbour i)
  target
    | .inl e => some (Q.target e)
    | .inr _ => none

/-- The same peripheral quiver with all incident arrows reversed. -/
def attachSourceOrientation (Q : Orientation V E) (neighbour : I → V) :
    Orientation (Option V) (Sum E I) where
  source
    | .inl e => some (Q.source e)
    | .inr _ => none
  target
    | .inl e => some (Q.target e)
    | .inr i => some (neighbour i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem reflect_attachSink [DecidableEq V] (Q : Orientation V E)
    (neighbour : I → V) :
    (attachSinkOrientation Q neighbour).reflect none = attachSourceOrientation Q neighbour := by
  apply Orientation.ext <;> funext e <;> cases e <;>
    simp [Orientation.reflect, attachSinkOrientation, attachSourceOrientation]

omit [Fintype I] [DecidableEq I] in
@[simp] theorem reflect_attachSource [DecidableEq V] (Q : Orientation V E)
    (neighbour : I → V) :
    (attachSourceOrientation Q neighbour).reflect none = attachSinkOrientation Q neighbour := by
  apply Orientation.ext <;> funext e <;> cases e <;>
    simp [Orientation.reflect, attachSinkOrientation, attachSourceOrientation]

variable (R : Rep K Q) (neighbour : I → V)

abbrev Boundary := ∀ i, R.space (neighbour i)

/-- Incoming arrows are the components of the aggregate map on coordinate inclusions. -/
def attachSink {X : Type u} [AddCommGroup X] [Module K X]
    (f : Boundary R neighbour →ₗ[K] X) : Rep K (attachSinkOrientation Q neighbour) where
  space
    | none => X
    | some v => R.space v
  add
    | none => inferInstance
    | some _ => inferInstance
  module
    | none => inferInstance
    | some _ => inferInstance
  arrow
    | .inl e => R.arrow e
    | .inr i => by
      dsimp [attachSinkOrientation]
      exact f.comp (LinearMap.single K (fun j => R.space (neighbour j)) i)

/-- Outgoing arrows are the coordinate projections of the aggregate map. -/
def attachSource {X : Type u} [AddCommGroup X] [Module K X]
    (g : X →ₗ[K] Boundary R neighbour) : Rep K (attachSourceOrientation Q neighbour) where
  space
    | none => X
    | some v => R.space v
  add
    | none => inferInstance
    | some _ => inferInstance
  module
    | none => inferInstance
    | some _ => inferInstance
  arrow
    | .inl e => R.arrow e
    | .inr i => (LinearMap.proj i).comp g

/-- Every list of incoming arrows has a unique aggregate map. This ensures the
attachment API is not restricted to a special class of incoming stars. -/
noncomputable def aggregateIncoming {X : Type u} [AddCommGroup X] [Module K X] :
    (∀ i, R.space (neighbour i) →ₗ[K] X) ≃ₗ[K] (Boundary R neighbour →ₗ[K] X) :=
  LinearMap.lsum K (fun i => R.space (neighbour i)) K

end Attachment

/-- A local sink is represented by the actual aggregate incoming linear map.
For finitely many neighbours, `W` is their product/direct sum. -/
structure SinkStar (W X : Type u) [AddCommGroup W] [Module K W]
    [AddCommGroup X] [Module K X] where
  incoming : W →ₗ[K] X

/-- The reversed local star has its actual aggregate outgoing map. -/
structure SourceStar (W X : Type u) [AddCommGroup W] [Module K W]
    [AddCommGroup X] [Module K X] where
  outgoing : X →ₗ[K] W

end UploadBroadcast.QuiverRepresentation
