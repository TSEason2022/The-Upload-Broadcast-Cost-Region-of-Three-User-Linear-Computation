import UploadBroadcast.E6Reflection

/-! Tits-form preservation follows from actual reflection dimension formulas. -/
namespace UploadBroadcast.QuiverRepresentation

universe u
variable {K V E : Type u} [Field K] [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]

/-- The orientation-independent quadratic form of the underlying graph. -/
def titsForm (Q : Orientation V E) (d : V → ℤ) : ℤ :=
  (∑ v, (d v)^2) - ∑ e, d (Q.source e) * d (Q.target e)

def Loopless (Q : Orientation V E) : Prop := ∀ e, Q.source e ≠ Q.target e

omit [DecidableEq E] [Fintype V] [Fintype E] in
theorem Loopless.reflect {Q : Orientation V E} (h : Loopless Q) (s : V) : Loopless (Q.reflect s) := by
  intro e
  dsimp [Orientation.reflect]
  split_ifs
  · exact (h e).symm
  · exact h e

omit [DecidableEq E] [Fintype V] in
theorem sum_sinkIncident_eq (Q : Orientation V E) (s : V) (f : E → ℤ) :
    ∑ e : SinkIncident Q s, f e.val = ∑ e, if Q.target e = s then f e else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by intro e; simp) f).symm

omit [DecidableEq E] [Fintype V] in
theorem sum_sourceIncident_eq (Q : Orientation V E) (s : V) (f : E → ℤ) :
    ∑ e : SourceIncident Q s, f e.val = ∑ e, if Q.source e = s then f e else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by intro e; simp) f).symm

omit [DecidableEq E] in
theorem titsForm_sinkDimension (Q : Orientation V E) (s : V) (hs : Q.IsSink s) (d : V → ℤ) :
    titsForm (Q.reflect s) (sinkDimension Q s d) = titsForm Q d := by
  let n := ∑ e : SinkIncident Q s, d (Q.source e.val)
  have hv : (∑ v, (sinkDimension Q s d v)^2) = (∑ v, (d v)^2) + ((n-d s)^2-(d s)^2) := by
    calc
      _ = ∑ v, ((d v)^2 + if v = s then (n-d s)^2-(d s)^2 else 0) := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases h : v = s
        · subst v; simp [sinkDimension, n]
        · simp [sinkDimension, h]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have he : ∀ e, sinkDimension Q s d ((Q.reflect s).source e) *
      sinkDimension Q s d ((Q.reflect s).target e) =
      d (Q.source e) * d (Q.target e) +
        (if Q.target e = s then d (Q.source e) else 0) * (n - 2*d s) := by
    intro e
    by_cases ht : Q.target e = s
    · simp [Orientation.reflect, sinkDimension, hs e, ht, n]
      ring
    · simp [Orientation.reflect, sinkDimension, hs e, ht]
  have heSum : (∑ e, sinkDimension Q s d ((Q.reflect s).source e) *
      sinkDimension Q s d ((Q.reflect s).target e)) =
      (∑ e, d (Q.source e) * d (Q.target e)) + n * (n-2*d s) := by
    simp_rw [he]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← sum_sinkIncident_eq Q s (fun e => d (Q.source e))]
  unfold titsForm
  rw [hv, heSum]
  ring

omit [DecidableEq E] in
theorem titsForm_sourceDimension (Q : Orientation V E) (s : V) (hs : Q.IsSource s) (d : V → ℤ) :
    titsForm (Q.reflect s) (sourceDimension Q s d) = titsForm Q d := by
  let n := ∑ e : SourceIncident Q s, d (Q.target e.val)
  have hv : (∑ v, (sourceDimension Q s d v)^2) = (∑ v, (d v)^2) + ((n-d s)^2-(d s)^2) := by
    calc
      _ = ∑ v, ((d v)^2 + if v = s then (n-d s)^2-(d s)^2 else 0) := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases h : v = s
        · subst v; simp [sourceDimension, n]
        · simp [sourceDimension, h]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have he : ∀ e, sourceDimension Q s d ((Q.reflect s).source e) *
      sourceDimension Q s d ((Q.reflect s).target e) =
      d (Q.source e) * d (Q.target e) +
        (if Q.source e = s then d (Q.target e) else 0) * (n - 2*d s) := by
    intro e
    by_cases ht : Q.source e = s
    · simp [Orientation.reflect, sourceDimension, hs e, ht, n]
      ring
    · simp [Orientation.reflect, sourceDimension, hs e, ht]
  have heSum : (∑ e, sourceDimension Q s d ((Q.reflect s).source e) *
      sourceDimension Q s d ((Q.reflect s).target e)) =
      (∑ e, d (Q.source e) * d (Q.target e)) + n * (n-2*d s) := by
    simp_rw [he]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← sum_sourceIncident_eq Q s (fun e => d (Q.target e))]
  unfold titsForm
  rw [hv, heSum]
  ring

omit [DecidableEq E] [Fintype V] [Fintype E] in
theorem VertexSimple.dimension {Q : Orientation V E} {R : Rep K Q} {s : V} (h : VertexSimple R s) :
    dimension R = fun v => if v = s then 1 else 0 := by
  funext v
  by_cases hv : v = s
  · subst v; simp [QuiverRepresentation.dimension, h.2]
  · letI : Subsingleton (R.space v) := ⟨fun x y => (h.1 v hv x).trans (h.1 v hv y).symm⟩
    simp [QuiverRepresentation.dimension, hv, Module.finrank_zero_of_subsingleton]

omit [DecidableEq E] in
theorem titsForm_vertexSimple {Q : Orientation V E} {R : Rep K Q} {s : V}
    (hQ : Loopless Q) (h : VertexSimple R s) : titsForm Q (dimension R) = 1 := by
  rw [h.dimension]
  have he : ∀ e, (if Q.source e = s then (1 : ℤ) else 0) *
      (if Q.target e = s then (1 : ℤ) else 0) = 0 := by
    intro e
    by_cases hs : Q.source e = s
    · have ht : Q.target e ≠ s := fun ht => hQ e (hs.trans ht.symm)
      simp [hs, ht]
    · simp [hs]
  simp [titsForm, he]

omit [Fintype V] in
theorem ReflectionReach.loopless {Q Q' : Orientation V E} {R : Rep K Q} {S : Rep K Q'}
    (h : ReflectionReach R S) (hQ : Loopless Q) : Loopless Q' := by
  induction h with
  | refl => exact hQ
  | sink R hs hf => exact hQ.reflect _
  | source R hs hg => exact hQ.reflect _
  | trans h1 h2 ih1 ih2 => exact ih2 (ih1 hQ)

omit [Fintype V] in
theorem ReflectionReach.finite {Q Q' : Orientation V E} {R : Rep K Q} {S : Rep K Q'}
    (h : ReflectionReach R S) : (∀ v, FiniteDimensional K (R.space v)) →
    ∀ v, FiniteDimensional K (S.space v) := by
  induction h with
  | refl => exact fun hfin => hfin
  | sink R hs hf => intro hfin; letI := hfin; intro v; infer_instance
  | source R hs hg => intro hfin; letI := hfin; intro v; infer_instance
  | trans h1 h2 ih1 ih2 => exact fun hfin => ih2 (ih1 hfin)

theorem ReflectionReach.titsForm_eq {Q Q' : Orientation V E} {R : Rep K Q} {S : Rep K Q'}
    (h : ReflectionReach R S) : (∀ v, FiniteDimensional K (R.space v)) →
    titsForm Q (dimension R) = titsForm Q' (dimension S) := by
  induction h with
  | refl => intro _; rfl
  | sink R hs hf =>
    intro hfin
    letI := hfin
    rw [dimension_sinkReflect R hs hf]
    exact (titsForm_sinkDimension _ _ hs _).symm
  | source R hs hg =>
    intro hfin
    letI := hfin
    rw [dimension_sourceReflect R hs hg]
    exact (titsForm_sourceDimension _ _ hs _).symm
  | trans h1 h2 ih1 ih2 =>
    intro hfin
    exact (ih1 hfin).trans (ih2 (h1.finite hfin))

theorem ReachesSimple.titsForm_eq_one {Q : Orientation V E} {R : Rep K Q}
    [∀ v, FiniteDimensional K (R.space v)] (hQ : Loopless Q) (h : ReachesSimple R) :
    titsForm Q (dimension R) = 1 := by
  obtain ⟨Q', S, s, hr, hs⟩ := h
  rw [hr.titsForm_eq (fun v => inferInstance)]
  exact titsForm_vertexSimple (hr.loopless hQ) hs

end UploadBroadcast.QuiverRepresentation

namespace UploadBroadcast.E6Reflection
open QuiverRepresentation

@[simp] theorem sum_vertices (f : E6Vertex → ℤ) :
    ∑ v, f v = f .center + f (.middle 0) + f (.middle 1) + f (.middle 2) +
      f (.outer 0) + f (.outer 1) + f (.outer 2) := by
  have h : (Finset.univ : Finset E6Vertex) =
      {.center, .middle 0, .middle 1, .middle 2, .outer 0, .outer 1, .outer 2} := by decide
  rw [h]
  simp [add_assoc]

theorem inward_loopless : Loopless inwardE6 := by
  intro e
  cases e <;> simp [inwardE6]

theorem titsForm_inward (d : E6Vertex → ℤ) :
    titsForm inwardE6 d = ReflectionReduction.tits (vector d) := by
  simp [titsForm, sum_vertices, sum_edges, inwardE6, ReflectionReduction.tits, vector, Structural.tits]
  ring

/-- The nonzero-defect real-root conclusion now follows from actual indecomposable
representations, with no assumed Tits bound, Kac classification, or normal form. -/
theorem nonzero_defect_tits_one {K : Type} [Field K] (R : Rep K inwardE6)
    [∀ v, FiniteDimensional K (R.space v)] (hR : Indecomposable R)
    (hd : ReflectionReduction.defect (vector (dimension R)) ≠ 0) :
    ReflectionReduction.tits (vector (dimension R)) = 1 := by
  rw [← titsForm_inward]
  exact (nonzero_defect_reaches_simple R hR hd).titsForm_eq_one inward_loopless

end UploadBroadcast.E6Reflection
