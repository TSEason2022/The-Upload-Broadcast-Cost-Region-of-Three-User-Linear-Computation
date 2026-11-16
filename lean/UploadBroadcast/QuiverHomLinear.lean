import UploadBroadcast.SourceHomVanishing

/-! Linear structure on actual quiver Hom spaces and linear reflection equivalences. -/
namespace UploadBroadcast.QuiverRepresentation
open ReflectionEquivalence

universe u
variable {K V E : Type u} [Field K] {Q : Orientation V E}

def homSpace (R S : Rep K Q) : Submodule K (∀ v, R.space v →ₗ[K] S.space v) where
  carrier := {f | ∀ e, (f (Q.target e)).comp (R.arrow e) = (S.arrow e).comp (f (Q.source e))}
  zero_mem' := by intro e; simp
  add_mem' := by
    intro f g hf hg e
    simp only [Pi.add_apply, LinearMap.add_comp, LinearMap.comp_add]
    exact congrArg₂ (· + ·) (hf e) (hg e)
  smul_mem' := by
    intro c f hf e
    simp only [Pi.smul_apply, LinearMap.smul_comp, LinearMap.comp_smul]
    exact congrArg (c • ·) (hf e)

def homSpaceEquiv (R S : Rep K Q) : Hom R S ≃ homSpace R S where
  toFun f := ⟨f.map, f.comm⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (R S : Rep K Q) : AddCommGroup (Hom R S) := (homSpaceEquiv R S).addCommGroup
instance (R S : Rep K Q) : Module K (Hom R S) := (homSpaceEquiv R S).module K

def homSpaceLinearEquiv (R S : Rep K Q) : Hom R S ≃ₗ[K] homSpace R S :=
  (homSpaceEquiv R S).linearEquiv K

@[simp] theorem Hom.zero_eq (R S : Rep K Q) : (0 : Hom R S) = Hom.zero R S := rfl
@[simp] theorem Hom.add_map (R S : Rep K Q) (f g : Hom R S) (v : V) :
    (f + g).map v = f.map v + g.map v := rfl
@[simp] theorem Hom.smul_map (R S : Rep K Q) (c : K) (f : Hom R S) (v : V) :
    (c • f).map v = c • f.map v := rfl

instance hom_finite [Fintype V] (R S : Rep K Q)
    [∀ v, FiniteDimensional K (R.space v)] [∀ v, FiniteDimensional K (S.space v)] :
    FiniteDimensional K (Hom R S) := (homSpaceLinearEquiv R S).symm.finiteDimensional

/-- A coordinate relabelling is a linear equivalence on Hom spaces. -/
def pullbackHomLinearEquiv {V' E' : Type u} {Q' : Orientation V' E'}
    (a : GraphIso Q Q') (R S : Rep K Q') : Hom R S ≃ₗ[K] Hom (pullback a R) (pullback a S) where
  toEquiv := pullbackHomEquiv a R S
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Conjugation by representation isomorphisms is linear. -/
def Iso.homLinearCongr {R S R' S' : Rep K Q} (a : Iso R R') (b : Iso S S') :
    Hom R S ≃ₗ[K] Hom R' S' where
  toEquiv := a.homCongr b
  map_add' f g := by
    apply Hom.ext
    intro v
    apply LinearMap.ext
    intro x
    simp [Iso.homCongr, Hom.comp, Iso.toHom]
  map_smul' c f := by
    apply Hom.ext
    intro v
    apply LinearMap.ext
    intro x
    simp [Iso.homCongr, Hom.comp, Iso.toHom]

section Attached
variable {I : Type u} [Fintype I] [DecidableEq I] (R S : Rep K Q) (neighbour : I → V)
  {X Y : Type u} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

noncomputable def attachedSinkHomLinearEquiv
    (f : Boundary R neighbour →ₗ[K] X) (g : Boundary S neighbour →ₗ[K] Y)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Hom (attachSink R neighbour f) (attachSink S neighbour g) ≃ₗ[K]
      Hom (attachSource R neighbour (sink f)) (attachSource S neighbour (sink g)) where
  toEquiv := attachedSinkHomEquiv hf hg
  map_add' a b := by
    apply Hom.ext
    intro v
    cases v <;> rfl
  map_smul' c a := by
    apply Hom.ext
    intro v
    cases v <;> rfl

noncomputable def attachedSourceHomLinearEquiv
    (f : X →ₗ[K] Boundary R neighbour) (g : Y →ₗ[K] Boundary S neighbour)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Hom (attachSource R neighbour f) (attachSource S neighbour g) ≃ₗ[K]
      Hom (attachSink R neighbour (source f)) (attachSink S neighbour (source g)) where
  toEquiv := attachedSourceHomEquiv hf hg
  map_add' a b := by
    apply Hom.ext
    intro v
    cases v with
    | some v => rfl
    | none =>
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with | H w => rfl
  map_smul' c a := by
    apply Hom.ext
    intro v
    cases v with
    | some v => rfl
    | none =>
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with | H w => rfl

end Attached

section Reflection
variable [DecidableEq V] [DecidableEq E] [Fintype E] {s : V}

namespace SinkWord

/-- At every selected sink, some other vertex has a nonzero dimension. -/
def NonSimpleDims : {Q Q' : Orientation V E} → SinkWord Q Q' → (V → ℤ) → Prop
  | _, _, .nil _, _ => True
  | Q, _, .cons s _ tail, d =>
      (∃ v, v ≠ s ∧ d v ≠ 0) ∧ tail.NonSimpleDims (sinkDimension Q s d)

omit [DecidableEq E] in
@[simp] theorem nonSimpleDims_castTarget {Q Q' Q'' : Orientation V E}
    (w : SinkWord Q Q') (h : Q' = Q'') (d : V → ℤ) :
    (w.castTarget h).NonSimpleDims d ↔ w.NonSimpleDims d := by cases h; rfl

omit [DecidableEq E] in
@[simp] theorem nonSimpleDims_append {Q Q' Q'' : Orientation V E}
    (a : SinkWord Q Q') (b : SinkWord Q' Q'') (d : V → ℤ) :
    (a.append b).NonSimpleDims d ↔ a.NonSimpleDims d ∧ b.NonSimpleDims (a.action d) := by
  induction a generalizing d with
  | nil => simp [append, NonSimpleDims, action]
  | cons s hs tail ih => simp only [append, NonSimpleDims, action, ih, and_assoc]

omit [DecidableEq E] in
@[simp] theorem nonSimpleDims_power_zero {Q : Orientation V E} (w : SinkWord Q Q) (d : V → ℤ) :
    (w.power 0).NonSimpleDims d := True.intro

omit [DecidableEq E] in
@[simp] theorem nonSimpleDims_power_succ {Q : Orientation V E} (w : SinkWord Q Q)
    (n : ℕ) (d : V → ℤ) : (w.power (n+1)).NonSimpleDims d ↔
      (w.power n).NonSimpleDims d ∧ w.NonSimpleDims ((w.power n).action d) :=
  nonSimpleDims_append _ _ _

/-- The actual aggregate incoming maps are surjective throughout the word. -/
def SurjectiveAlong : {Q Q' : Orientation V E} → SinkWord Q Q' → Rep K Q → Prop
  | _, _, .nil _, _ => True
  | _, _, .cons _ hs tail, R =>
      Function.Surjective (sinkIncoming R hs) ∧ tail.SurjectiveAlong (sinkReflect R hs)

theorem valid_of_dims {Q Q' : Orientation V E} (w : SinkWord Q Q') (R : Rep K Q)
    [∀ v, FiniteDimensional K (R.space v)] (hR : Indecomposable R)
    (hc : w.NonSimpleDims (dimension R)) :
    w.SurjectiveAlong R ∧ Indecomposable (w.run R) ∧ dimension (w.run R) = w.action (dimension R) := by
  induction w with
  | nil => exact ⟨True.intro, hR, rfl⟩
  | @cons Q Q' s hs tail ih =>
    obtain ⟨⟨v, hv, hdv⟩, ht⟩ := hc
    have hn : Nontrivial (R.space v) := by
      rcases subsingleton_or_nontrivial (R.space v) with hh | hh
      · letI := hh
        exact False.elim (hdv (by simp [dimension, Module.finrank_zero_of_subsingleton]))
      · exact hh
    letI := hn
    have he := sinkIncoming_surjective R hs hR v hv
    have hi := sinkReflect_indecomposable R hs hR v hv
    have hd := dimension_sinkReflect R hs he
    rw [← hd] at ht
    obtain ⟨ha, hf, hfD⟩ := ih (sinkReflect R hs) hi ht
    refine ⟨⟨he, ha⟩, hf, ?_⟩
    change dimension (tail.run (sinkReflect R hs)) = tail.action (sinkDimension Q s (dimension R))
    rw [hfD, hd]

noncomputable def homEquiv : {Q Q' : Orientation V E} → (w : SinkWord Q Q') →
    (R S : Rep K Q) → w.SurjectiveAlong R → w.SurjectiveAlong S →
    (Hom R S ≃ Hom (w.run R) (w.run S))
  | _, _, .nil _, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ hs tail, R, S, hR, hS =>
      (sinkReflectHomEquiv R S hs hR.1 hS.1).trans
        (tail.homEquiv (sinkReflect R hs) (sinkReflect S hs) hR.2 hS.2)

end SinkWord

noncomputable def sinkReflectHomLinearEquiv (R S : Rep K Q) (hs : Q.IsSink s)
    (hR : Function.Surjective (sinkIncoming R hs)) (hS : Function.Surjective (sinkIncoming S hs)) :
    Hom R S ≃ₗ[K] Hom (sinkReflect R hs) (sinkReflect S hs) :=
  (pullbackHomLinearEquiv (sinkChartGraph Q s hs) R S).trans
    (((sinkChartIso R hs).homLinearCongr (sinkChartIso S hs)).trans
      ((attachedSinkHomLinearEquiv _ _ _ _ _ hR hS).trans
        (pullbackHomLinearEquiv (sinkReflectedChartGraph Q s hs).symm _ _)))

noncomputable def sourceReflectHomLinearEquiv (R S : Rep K Q) (hs : Q.IsSource s)
    (hR : Function.Injective (sourceOutgoing R hs)) (hS : Function.Injective (sourceOutgoing S hs)) :
    Hom R S ≃ₗ[K] Hom (sourceReflect R hs) (sourceReflect S hs) :=
  (pullbackHomLinearEquiv (sourceChartGraph Q s hs) R S).trans
    (((sourceChartIso R hs).homLinearCongr (sourceChartIso S hs)).trans
      ((attachedSourceHomLinearEquiv _ _ _ _ _ hR hS).trans
        (pullbackHomLinearEquiv (sourceReflectedChartGraph Q s hs).symm _ _)))

noncomputable def SourceWord.homLinearEquiv : {Q Q' : Orientation V E} → (w : SourceWord Q Q') →
    (R S : Rep K Q) → w.InjectiveAlong R → w.InjectiveAlong S →
    (Hom R S ≃ₗ[K] Hom (w.run R) (w.run S))
  | _, _, .nil _, _, _, _, _ => LinearEquiv.refl K _
  | _, _, .cons _ hs tail, R, S, hR, hS =>
      (sourceReflectHomLinearEquiv R S hs hR.1 hS.1).trans
        (tail.homLinearEquiv (sourceReflect R hs) (sourceReflect S hs) hR.2 hS.2)

noncomputable def SinkWord.homLinearEquiv : {Q Q' : Orientation V E} → (w : SinkWord Q Q') →
    (R S : Rep K Q) → w.SurjectiveAlong R → w.SurjectiveAlong S →
    (Hom R S ≃ₗ[K] Hom (w.run R) (w.run S))
  | _, _, .nil _, _, _, _, _ => LinearEquiv.refl K _
  | _, _, .cons _ hs tail, R, S, hR, hS =>
      (sinkReflectHomLinearEquiv R S hs hR.1 hS.1).trans
        (tail.homLinearEquiv (sinkReflect R hs) (sinkReflect S hs) hR.2 hS.2)

theorem SinkWord.hom_finrank {Q Q' : Orientation V E} (w : SinkWord Q Q')
    (R S : Rep K Q) (hR : w.SurjectiveAlong R) (hS : w.SurjectiveAlong S) :
    Module.finrank K (Hom R S) = Module.finrank K (Hom (w.run R) (w.run S)) :=
  (w.homLinearEquiv R S hR hS).finrank_eq

/-- Hom dimensions are invariants of the actual certified reflection trajectory. -/
theorem SourceWord.hom_finrank {Q Q' : Orientation V E} (w : SourceWord Q Q')
    (R S : Rep K Q) (hR : w.InjectiveAlong R) (hS : w.InjectiveAlong S) :
    Module.finrank K (Hom R S) = Module.finrank K (Hom (w.run R) (w.run S)) :=
  (w.homLinearEquiv R S hR hS).finrank_eq

end Reflection

end UploadBroadcast.QuiverRepresentation
