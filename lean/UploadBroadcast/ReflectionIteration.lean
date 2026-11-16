import UploadBroadcast.QuiverReindex
import UploadBroadcast.ReflectionReduction
import Mathlib.Tactic.NormNum

/-! Actual reflection trajectories and their certified dimension transformations. -/
namespace UploadBroadcast.QuiverRepresentation

universe u
variable {K V E : Type u} [Field K] [DecidableEq V] [DecidableEq E] [Fintype E]

/-- Integral dimensions of the actual vertex modules. -/
noncomputable def dimension {Q : Orientation V E} (R : Rep K Q) (v : V) : ℤ := Module.finrank K (R.space v)

def sinkDimension (Q : Orientation V E) (s : V) (d : V → ℤ) (v : V) : ℤ :=
  if v = s then (∑ e : SinkIncident Q s, d (Q.source e.val)) - d s else d v

def sourceDimension (Q : Orientation V E) (s : V) (d : V → ℤ) (v : V) : ℤ :=
  if v = s then (∑ e : SourceIncident Q s, d (Q.target e.val)) - d s else d v

theorem dimension_sinkReflect {Q : Orientation V E} (R : Rep K Q) {s : V} (hs : Q.IsSink s)
    [∀ v, FiniteDimensional K (R.space v)] (hf : Function.Surjective (sinkIncoming R hs)) :
    dimension (sinkReflect R hs) = sinkDimension Q s (dimension R) := by
  funext v
  by_cases hv : v = s
  · subst v
    have h := sinkReflect_finrank_center R hs hf
    have hh : (Module.finrank K ((sinkReflect R hs).space s) : ℤ) +
        (Module.finrank K (R.space s) : ℤ) =
        ∑ e : SinkIncident Q s, (Module.finrank K (R.space (Q.source e.val)) : ℤ) := by
      exact_mod_cast h
    dsimp [dimension, sinkDimension]
    rw [if_pos rfl]
    linarith
  · simp only [dimension, sinkDimension, if_neg hv, sinkReflect_finrank_away R hs v hv]

theorem dimension_sourceReflect {Q : Orientation V E} (R : Rep K Q) {s : V} (hs : Q.IsSource s)
    [∀ v, FiniteDimensional K (R.space v)] (hg : Function.Injective (sourceOutgoing R hs)) :
    dimension (sourceReflect R hs) = sourceDimension Q s (dimension R) := by
  funext v
  by_cases hv : v = s
  · subst v
    have h := sourceReflect_finrank_center R hs hg
    have hh : (Module.finrank K ((sourceReflect R hs).space s) : ℤ) +
        (Module.finrank K (R.space s) : ℤ) =
        ∑ e : SourceIncident Q s, (Module.finrank K (R.space (Q.target e.val)) : ℤ) := by
      exact_mod_cast h
    dsimp [dimension, sourceDimension]
    rw [if_pos rfl]
    linarith
  · simp only [dimension, sourceDimension, if_neg hv, sourceReflect_finrank_away R hs v hv]

/-- Equal actual dimensions give vertexwise linear equivalences. At a supported
sink these automatically commute with every arrow. -/
noncomputable def supportedSinkIso {Q : Orientation V E} (R S : Rep K Q) {s : V}
    (hs : Q.IsSink s) [∀ v, FiniteDimensional K (R.space v)]
    [∀ v, FiniteDimensional K (S.space v)] (hp : SupportedAt R s)
    (hd : dimension R = dimension S) : Iso R S where
  map v := LinearEquiv.ofFinrankEq _ _ (Int.ofNat_inj.mp (congrFun hd v))
  comm e := by
    apply LinearMap.ext
    intro x
    rw [hp (Q.source e) (hs e) x]
    simp

noncomputable def supportedSourceIso {Q : Orientation V E} (R S : Rep K Q) {s : V}
    (hs : Q.IsSource s) [∀ v, FiniteDimensional K (R.space v)]
    [∀ v, FiniteDimensional K (S.space v)] (hp : SupportedAt R s)
    (hd : dimension R = dimension S) : Iso R S where
  map v := LinearEquiv.ofFinrankEq _ _ (Int.ofNat_inj.mp (congrFun hd v))
  comm e := by
    apply LinearMap.ext
    intro x
    apply (LinearEquiv.ofFinrankEq (R.space (Q.target e)) (S.space (Q.target e))
      (Int.ofNat_inj.mp (congrFun hd (Q.target e)))).symm.injective
    exact (hp (Q.target e) (hs e) _).trans (hp (Q.target e) (hs e) _).symm

/-- Reachability only uses reflection steps satisfying the local epi/mono condition.
It therefore records actual invertible reflection steps, rather than a numeric orbit. -/
inductive ReflectionReach : {Q Q' : Orientation V E} → Rep K Q → Rep K Q' → Prop
  | refl {Q} (R : Rep K Q) : ReflectionReach R R
  | sink {Q} (R : Rep K Q) {s} (hs : Q.IsSink s)
      (hf : Function.Surjective (sinkIncoming R hs)) : ReflectionReach R (sinkReflect R hs)
  | source {Q} (R : Rep K Q) {s} (hs : Q.IsSource s)
      (hg : Function.Injective (sourceOutgoing R hs)) : ReflectionReach R (sourceReflect R hs)
  | trans {Q Q' Q''} {R : Rep K Q} {S : Rep K Q'} {T : Rep K Q''} :
      ReflectionReach R S → ReflectionReach S T → ReflectionReach R T

def ReachesSimple {Q : Orientation V E} (R : Rep K Q) : Prop :=
  ∃ (Q' : Orientation V E) (S : Rep K Q') (s : V), ReflectionReach R S ∧ VertexSimple S s

/-- An admissible word contains the actual successive sink proofs. -/
inductive SinkWord : Orientation V E → Orientation V E → Type u
  | nil (Q) : SinkWord Q Q
  | cons {Q Q'} (s : V) (hs : Q.IsSink s) (tail : SinkWord (Q.reflect s) Q') : SinkWord Q Q'

namespace SinkWord

noncomputable def run : {Q Q' : Orientation V E} → SinkWord Q Q' → Rep K Q → Rep K Q'
  | _, _, .nil _, R => R
  | _, _, .cons _ hs tail, R => tail.run (sinkReflect R hs)

def action : {Q Q' : Orientation V E} → SinkWord Q Q' → (V → ℤ) → (V → ℤ)
  | _, _, .nil _, d => d
  | Q, _, .cons s _ tail, d => tail.action (sinkDimension Q s d)

instance run_finite {Q Q' : Orientation V E} (w : SinkWord Q Q') (R : Rep K Q)
    [∀ v, FiniteDimensional K (R.space v)] (v : V) : FiniteDimensional K ((w.run R).space v) := by
  induction w with
  | nil => exact inferInstanceAs (FiniteDimensional K (R.space v))
  | @cons Q Q' s hs tail ih =>
    exact ih (sinkReflect R hs)

/-- Along every admissible word, either an actual simple is reached, or the
actual output remains indecomposable and follows the proved dimension rule. -/
theorem dichotomy {Q Q' : Orientation V E} (w : SinkWord Q Q') (R : Rep K Q)
    [∀ v, FiniteDimensional K (R.space v)] (hR : Indecomposable R) :
    ReachesSimple R ∨ (Indecomposable (w.run R) ∧ ReflectionReach R (w.run R) ∧
      dimension (w.run R) = w.action (dimension R)) := by
  induction w with
  | nil => exact Or.inr ⟨hR, .refl R, rfl⟩
  | @cons Q Q' s hs tail ih =>
    rcases sink_step R hs hR with hsimple | ⟨hnew, hepi⟩
    · exact Or.inl ⟨Q, R, s, .refl R, hsimple⟩
    · rcases ih (sinkReflect R hs) hnew with hsimple | ⟨hi, hr, hd⟩
      · obtain ⟨Qt, T, t, ht, hsimple⟩ := hsimple
        exact Or.inl ⟨Qt, T, t, .trans (.sink R hs hepi) ht, hsimple⟩
      · refine Or.inr ⟨hi, .trans (.sink R hs hepi) hr, ?_⟩
        change dimension (tail.run (sinkReflect R hs)) =
          tail.action (sinkDimension Q s (dimension R))
        rw [hd, dimension_sinkReflect R hs hepi]

/-- Any numerically negative endpoint forces an actual simple along the word. -/
theorem reachesSimple_of_negative {Q Q' : Orientation V E} (w : SinkWord Q Q') (R : Rep K Q)
    [∀ v, FiniteDimensional K (R.space v)] (hR : Indecomposable R)
    (v : V) (hneg : w.action (dimension R) v < 0) : ReachesSimple R := by
  rcases w.dichotomy R hR with h | ⟨_, _, hd⟩
  · exact h
  · rw [← hd] at hneg
    exact False.elim (not_lt_of_ge (Int.natCast_nonneg _) hneg)

/-- A word whose dimension action becomes negative proves base-field uniqueness
by reflecting two actual indecomposables together and reversing their isomorphisms. -/
theorem unique_of_negative {Q Q' : Orientation V E} (w : SinkWord Q Q') (R S : Rep K Q)
    [∀ v, FiniteDimensional K (R.space v)] [∀ v, FiniteDimensional K (S.space v)]
    (hR : Indecomposable R) (hS : Indecomposable S) (hd : dimension R = dimension S)
    (v : V) (hneg : w.action (dimension R) v < 0) : Nonempty (Iso R S) := by
  induction w with
  | nil => exact False.elim (not_lt_of_ge (Int.natCast_nonneg _) hneg)
  | @cons Q Q' s hs tail ih =>
    rcases sink_step R hs hR with hr | ⟨hiR, heR⟩
    · exact ⟨supportedSinkIso R S hs hr.1 hd⟩
    · rcases sink_step S hs hS with hsimp | ⟨hiS, heS⟩
      · exact ⟨(supportedSinkIso S R hs hsimp.1 hd.symm).symm⟩
      · have hd' : dimension (sinkReflect R hs) = dimension (sinkReflect S hs) := by
          rw [dimension_sinkReflect R hs heR, dimension_sinkReflect S hs heS, hd]
        have hn' : tail.action (dimension (sinkReflect R hs)) v < 0 := by
          rw [dimension_sinkReflect R hs heR]
          exact hneg
        obtain ⟨f⟩ := ih (sinkReflect R hs) (sinkReflect S hs) hiR hiS hd' hn'
        exact ⟨sinkUnreflectIso R S hs heR heS f⟩

def castTarget {Q Q' Q'' : Orientation V E} (w : SinkWord Q Q') (h : Q' = Q'') : SinkWord Q Q'' :=
  h ▸ w

omit [DecidableEq E] in
@[simp] theorem action_castTarget {Q Q' Q'' : Orientation V E} (w : SinkWord Q Q') (h : Q' = Q'')
    (d : V → ℤ) : (w.castTarget h).action d = w.action d := by cases h; rfl

def append : {Q Q' Q'' : Orientation V E} → SinkWord Q Q' → SinkWord Q' Q'' → SinkWord Q Q''
  | _, _, _, .nil _, w => w
  | _, _, _, .cons s hs tail, w => .cons s hs (tail.append w)

omit [DecidableEq E] in
@[simp] theorem action_append {Q Q' Q'' : Orientation V E} (a : SinkWord Q Q') (b : SinkWord Q' Q'')
    (d : V → ℤ) : (a.append b).action d = b.action (a.action d) := by
  induction a generalizing d with
  | nil => rfl
  | cons s hs tail ih => exact ih b _

def power {Q : Orientation V E} (w : SinkWord Q Q) : ℕ → SinkWord Q Q
  | 0 => .nil Q
  | n + 1 => (power w n).append w

omit [DecidableEq E] in
@[simp] theorem action_power {Q : Orientation V E} (w : SinkWord Q Q) (n : ℕ) (d : V → ℤ) :
    (w.power n).action d = (w.action)^[n] d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    simp only [power, action_append, ih, Function.iterate_succ_apply']

end SinkWord

/-- An admissible word contains the actual successive source proofs. -/
inductive SourceWord : Orientation V E → Orientation V E → Type u
  | nil (Q) : SourceWord Q Q
  | cons {Q Q'} (s : V) (hs : Q.IsSource s) (tail : SourceWord (Q.reflect s) Q') : SourceWord Q Q'

namespace SourceWord

noncomputable def run : {Q Q' : Orientation V E} → SourceWord Q Q' → Rep K Q → Rep K Q'
  | _, _, .nil _, R => R
  | _, _, .cons _ hs tail, R => tail.run (sourceReflect R hs)

def action : {Q Q' : Orientation V E} → SourceWord Q Q' → (V → ℤ) → (V → ℤ)
  | _, _, .nil _, d => d
  | Q, _, .cons s _ tail, d => tail.action (sourceDimension Q s d)

instance run_finite {Q Q' : Orientation V E} (w : SourceWord Q Q') (R : Rep K Q)
    [∀ v, FiniteDimensional K (R.space v)] (v : V) : FiniteDimensional K ((w.run R).space v) := by
  induction w with
  | nil => exact inferInstanceAs (FiniteDimensional K (R.space v))
  | @cons Q Q' s hs tail ih =>
    exact ih (sourceReflect R hs)

/-- Along every admissible word, either an actual simple is reached, or the
actual output remains indecomposable and follows the proved dimension rule. -/
theorem dichotomy {Q Q' : Orientation V E} (w : SourceWord Q Q') (R : Rep K Q)
    [∀ v, FiniteDimensional K (R.space v)] (hR : Indecomposable R) :
    ReachesSimple R ∨ (Indecomposable (w.run R) ∧ ReflectionReach R (w.run R) ∧
      dimension (w.run R) = w.action (dimension R)) := by
  induction w with
  | nil => exact Or.inr ⟨hR, .refl R, rfl⟩
  | @cons Q Q' s hs tail ih =>
    rcases source_step R hs hR with hsimple | ⟨hnew, hepi⟩
    · exact Or.inl ⟨Q, R, s, .refl R, hsimple⟩
    · rcases ih (sourceReflect R hs) hnew with hsimple | ⟨hi, hr, hd⟩
      · obtain ⟨Qt, T, t, ht, hsimple⟩ := hsimple
        exact Or.inl ⟨Qt, T, t, .trans (.source R hs hepi) ht, hsimple⟩
      · refine Or.inr ⟨hi, .trans (.source R hs hepi) hr, ?_⟩
        change dimension (tail.run (sourceReflect R hs)) =
          tail.action (sourceDimension Q s (dimension R))
        rw [hd, dimension_sourceReflect R hs hepi]

/-- Any numerically negative endpoint forces an actual simple along the word. -/
theorem reachesSimple_of_negative {Q Q' : Orientation V E} (w : SourceWord Q Q') (R : Rep K Q)
    [∀ v, FiniteDimensional K (R.space v)] (hR : Indecomposable R)
    (v : V) (hneg : w.action (dimension R) v < 0) : ReachesSimple R := by
  rcases w.dichotomy R hR with h | ⟨_, _, hd⟩
  · exact h
  · rw [← hd] at hneg
    exact False.elim (not_lt_of_ge (Int.natCast_nonneg _) hneg)

/-- A word whose dimension action becomes negative proves base-field uniqueness
by reflecting two actual indecomposables together and reversing their isomorphisms. -/
theorem unique_of_negative {Q Q' : Orientation V E} (w : SourceWord Q Q') (R S : Rep K Q)
    [∀ v, FiniteDimensional K (R.space v)] [∀ v, FiniteDimensional K (S.space v)]
    (hR : Indecomposable R) (hS : Indecomposable S) (hd : dimension R = dimension S)
    (v : V) (hneg : w.action (dimension R) v < 0) : Nonempty (Iso R S) := by
  induction w with
  | nil => exact False.elim (not_lt_of_ge (Int.natCast_nonneg _) hneg)
  | @cons Q Q' s hs tail ih =>
    rcases source_step R hs hR with hr | ⟨hiR, heR⟩
    · exact ⟨supportedSourceIso R S hs hr.1 hd⟩
    · rcases source_step S hs hS with hsimp | ⟨hiS, heS⟩
      · exact ⟨(supportedSourceIso S R hs hsimp.1 hd.symm).symm⟩
      · have hd' : dimension (sourceReflect R hs) = dimension (sourceReflect S hs) := by
          rw [dimension_sourceReflect R hs heR, dimension_sourceReflect S hs heS, hd]
        have hn' : tail.action (dimension (sourceReflect R hs)) v < 0 := by
          rw [dimension_sourceReflect R hs heR]
          exact hneg
        obtain ⟨f⟩ := ih (sourceReflect R hs) (sourceReflect S hs) hiR hiS hd' hn'
        exact ⟨sourceUnreflectIso R S hs heR heS f⟩

def castTarget {Q Q' Q'' : Orientation V E} (w : SourceWord Q Q') (h : Q' = Q'') : SourceWord Q Q'' :=
  h ▸ w

omit [DecidableEq E] in
@[simp] theorem action_castTarget {Q Q' Q'' : Orientation V E} (w : SourceWord Q Q') (h : Q' = Q'')
    (d : V → ℤ) : (w.castTarget h).action d = w.action d := by cases h; rfl

def append : {Q Q' Q'' : Orientation V E} → SourceWord Q Q' → SourceWord Q' Q'' → SourceWord Q Q''
  | _, _, _, .nil _, w => w
  | _, _, _, .cons s hs tail, w => .cons s hs (tail.append w)

omit [DecidableEq E] in
@[simp] theorem action_append {Q Q' Q'' : Orientation V E} (a : SourceWord Q Q') (b : SourceWord Q' Q'')
    (d : V → ℤ) : (a.append b).action d = b.action (a.action d) := by
  induction a generalizing d with
  | nil => rfl
  | cons s hs tail ih => exact ih b _

def power {Q : Orientation V E} (w : SourceWord Q Q) : ℕ → SourceWord Q Q
  | 0 => .nil Q
  | n + 1 => (power w n).append w

omit [DecidableEq E] in
@[simp] theorem action_power {Q : Orientation V E} (w : SourceWord Q Q) (n : ℕ) (d : V → ℤ) :
    (w.power n).action d = (w.action)^[n] d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    simp only [power, action_append, ih, Function.iterate_succ_apply']

end SourceWord

end UploadBroadcast.QuiverRepresentation
