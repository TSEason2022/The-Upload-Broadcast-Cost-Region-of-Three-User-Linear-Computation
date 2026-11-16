import UploadBroadcast.E6Reflection

/-! Zero-preserving Hom transport along certified source words. -/
namespace UploadBroadcast.QuiverRepresentation
open ReflectionEquivalence

universe u
variable {K V E : Type u} [Field K] [DecidableEq V] [DecidableEq E] [Fintype E]

namespace SourceWord

/-- At every selected source, some other vertex has a nonzero dimension. -/
def NonSimpleDims : {Q Q' : Orientation V E} → SourceWord Q Q' → (V → ℤ) → Prop
  | _, _, .nil _, _ => True
  | Q, _, .cons s _ tail, d =>
      (∃ v, v ≠ s ∧ d v ≠ 0) ∧ tail.NonSimpleDims (sourceDimension Q s d)

omit [DecidableEq E] in
@[simp] theorem nonSimpleDims_castTarget {Q Q' Q'' : Orientation V E}
    (w : SourceWord Q Q') (h : Q' = Q'') (d : V → ℤ) :
    (w.castTarget h).NonSimpleDims d ↔ w.NonSimpleDims d := by cases h; rfl

omit [DecidableEq E] in
@[simp] theorem nonSimpleDims_append {Q Q' Q'' : Orientation V E}
    (a : SourceWord Q Q') (b : SourceWord Q' Q'') (d : V → ℤ) :
    (a.append b).NonSimpleDims d ↔ a.NonSimpleDims d ∧ b.NonSimpleDims (a.action d) := by
  induction a generalizing d with
  | nil => simp [append, NonSimpleDims, action]
  | cons s hs tail ih => simp only [append, NonSimpleDims, action, ih, and_assoc]

omit [DecidableEq E] in
@[simp] theorem nonSimpleDims_power_zero {Q : Orientation V E} (w : SourceWord Q Q) (d : V → ℤ) :
    (w.power 0).NonSimpleDims d := True.intro

omit [DecidableEq E] in
@[simp] theorem nonSimpleDims_power_succ {Q : Orientation V E} (w : SourceWord Q Q)
    (n : ℕ) (d : V → ℤ) : (w.power (n+1)).NonSimpleDims d ↔
      (w.power n).NonSimpleDims d ∧ w.NonSimpleDims ((w.power n).action d) :=
  nonSimpleDims_append _ _ _

/-- The actual aggregate outgoing maps are injective throughout the word. -/
def InjectiveAlong : {Q Q' : Orientation V E} → SourceWord Q Q' → Rep K Q → Prop
  | _, _, .nil _, _ => True
  | _, _, .cons _ hs tail, R =>
      Function.Injective (sourceOutgoing R hs) ∧ tail.InjectiveAlong (sourceReflect R hs)

theorem valid_of_dims {Q Q' : Orientation V E} (w : SourceWord Q Q') (R : Rep K Q)
    [∀ v, FiniteDimensional K (R.space v)] (hR : Indecomposable R)
    (hc : w.NonSimpleDims (dimension R)) :
    w.InjectiveAlong R ∧ Indecomposable (w.run R) ∧ dimension (w.run R) = w.action (dimension R) := by
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
    have he := sourceOutgoing_injective R hs hR v hv
    have hi := sourceReflect_indecomposable R hs hR v hv
    have hd := dimension_sourceReflect R hs he
    rw [← hd] at ht
    obtain ⟨ha, hf, hfD⟩ := ih (sourceReflect R hs) hi ht
    refine ⟨⟨he, ha⟩, hf, ?_⟩
    change dimension (tail.run (sourceReflect R hs)) = tail.action (sourceDimension Q s (dimension R))
    rw [hfD, hd]

noncomputable def homEquiv : {Q Q' : Orientation V E} → (w : SourceWord Q Q') →
    (R S : Rep K Q) → w.InjectiveAlong R → w.InjectiveAlong S →
    (Hom R S ≃ Hom (w.run R) (w.run S))
  | _, _, .nil _, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ hs tail, R, S, hR, hS =>
      (sourceReflectHomEquiv R S hs hR.1 hS.1).trans
        (tail.homEquiv (sourceReflect R hs) (sourceReflect S hs) hR.2 hS.2)

end SourceWord

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
@[simp] theorem Iso.homCongr_zero {Q : Orientation V E} {R S R' S' : Rep K Q}
    (a : Iso R R') (b : Iso S S') : a.homCongr b (Hom.zero R S) = Hom.zero R' S' := by
  apply Hom.ext
  intro v
  apply LinearMap.ext
  intro x
  simp [Iso.homCongr, Hom.comp, Iso.toHom, Hom.zero]

@[simp] theorem sourceReflectHomEquiv_zero {Q : Orientation V E} (R S : Rep K Q) {s : V}
    (hs : Q.IsSource s) (hR : Function.Injective (sourceOutgoing R hs))
    (hS : Function.Injective (sourceOutgoing S hs)) :
    sourceReflectHomEquiv R S hs hR hS (Hom.zero R S) =
      Hom.zero (sourceReflect R hs) (sourceReflect S hs) := by
  change pullbackHom _ (reflectAttachedSourceHom
    ((sourceChartIso R hs).homCongr (sourceChartIso S hs)
      (pullbackHom (sourceChartGraph Q s hs) (Hom.zero R S)))) = _
  rw [pullbackHom_zero, Iso.homCongr_zero, reflectAttachedSourceHom_zero, pullbackHom_zero]
  rfl

@[simp] theorem SourceWord.homEquiv_zero {Q Q' : Orientation V E} (w : SourceWord Q Q')
    (R S : Rep K Q) (hR : w.InjectiveAlong R) (hS : w.InjectiveAlong S) :
    w.homEquiv R S hR hS (Hom.zero R S) = Hom.zero (w.run R) (w.run S) := by
  induction w with
  | nil => rfl
  | cons s hs tail ih =>
    change tail.homEquiv _ _ _ _ (sourceReflectHomEquiv R S hs hR.1 hS.1 (Hom.zero R S)) = _
    rw [sourceReflectHomEquiv_zero, ih]
    rfl

omit [DecidableEq E] [Fintype E] in
/-- A representation supported at a source has no nonzero maps to a representation
whose aggregate outgoing map at that source is injective. -/
theorem supportedSource_hom_zero {Q : Orientation V E} (R S : Rep K Q) {s : V}
    (hs : Q.IsSource s) (hp : SupportedAt R s)
    (hi : Function.Injective (sourceOutgoing S hs)) (f : Hom R S) : f = Hom.zero R S := by
  have hg : sourceOutgoing R hs = 0 := by
    apply LinearMap.ext
    intro x
    funext e
    exact hp (Q.target e.val) (hs e.val) _
  let sq := attachedSourceSquare
    ((sourceChartIso R hs).homCongr (sourceChartIso S hs) (pullbackHom (sourceChartGraph Q s hs) f))
  apply Hom.ext
  intro v
  apply LinearMap.ext
  intro x
  by_cases hv : v = s
  · subst v
    apply hi
    change sourceOutgoing S hs (f.map s x) = sourceOutgoing S hs 0
    rw [map_zero]
    have hh := LinearMap.congr_fun sq.comm x
    change sourceOutgoing S hs (f.map s x) = sq.boundary (sourceOutgoing R hs x) at hh
    simpa [hg] using hh
  · rw [hp v hv x, map_zero]
    rfl

/-- Vanishing at the certified terminal source transports all the way back. -/
theorem SourceWord.hom_zero_of_terminal {Q Q' : Orientation V E} (w : SourceWord Q Q')
    (R S : Rep K Q) (hR : w.InjectiveAlong R) (hS : w.InjectiveAlong S)
    {s : V} (hs : Q'.IsSource s) (hp : SupportedAt (w.run R) s)
    (hi : Function.Injective (sourceOutgoing (w.run S) hs)) (f : Hom R S) : f = Hom.zero R S := by
  apply (w.homEquiv R S hR hS).injective
  rw [SourceWord.homEquiv_zero]
  exact supportedSource_hom_zero _ _ hs hp hi _

end UploadBroadcast.QuiverRepresentation
