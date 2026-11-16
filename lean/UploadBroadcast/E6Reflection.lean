import UploadBroadcast.ReflectionIteration
import Mathlib.Tactic.FinCases

/-! Admissible E6 reflection words and their actual-representation consequences. -/
namespace UploadBroadcast.E6Reflection
open QuiverRepresentation

private def edgeEquiv : (Fin 3 ⊕ Fin 3) ≃ E6Edge where
  toFun | .inl i => .inner i | .inr i => .outer i
  invFun | .inner i => .inl i | .outer i => .inr i
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

instance : Fintype E6Edge := Fintype.ofEquiv _ edgeEquiv

private def vertexEquiv : Option (Fin 3 ⊕ Fin 3) ≃ E6Vertex where
  toFun | none => .center | some (.inl i) => .middle i | some (.inr i) => .outer i
  invFun | .center => none | .middle i => some (.inl i) | .outer i => some (.inr i)
  left_inv x := by cases x with
    | none => rfl
    | some x => cases x <;> rfl
  right_inv x := by cases x <;> rfl

instance : Fintype E6Vertex := Fintype.ofEquiv _ vertexEquiv

@[simp] theorem sum_edges (f : E6Edge → ℤ) :
    ∑ e, f e = f (.inner 0) + f (.inner 1) + f (.inner 2) +
      (f (.outer 0) + f (.outer 1) + f (.outer 2)) := by
  rw [← Fintype.sum_equiv edgeEquiv (f ∘ edgeEquiv) f (fun _ => rfl)]
  simp [Fintype.sum_sum_type, Fin.sum_univ_three, edgeEquiv]

theorem sum_sinkIncident (Q : Orientation E6Vertex E6Edge) (s : E6Vertex) (f : E6Edge → ℤ) :
    ∑ e : SinkIncident Q s, f e.val = ∑ e, if Q.target e = s then f e else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by intro e; simp) f).symm

theorem sum_sourceIncident (Q : Orientation E6Vertex E6Edge) (s : E6Vertex) (f : E6Edge → ℤ) :
    ∑ e : SourceIncident Q s, f e.val = ∑ e, if Q.source e = s then f e else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by intro e; simp) f).symm

abbrev Q0 := inwardE6
def Q1 := Q0.reflect .center
def Q2 := Q1.reflect (.middle 0)
def Q3 := Q2.reflect (.middle 1)
def Q4 := Q3.reflect (.middle 2)
def Q5 := Q4.reflect (.outer 0)
def Q6 := Q5.reflect (.outer 1)
def Q7 := Q6.reflect (.outer 2)

theorem sink0 : Q0.IsSink .center := by intro e; cases e <;> rename_i i <;> fin_cases i <;> decide
theorem sink1 : Q1.IsSink (.middle 0) := by intro e; cases e <;> rename_i i <;> fin_cases i <;> decide
theorem sink2 : Q2.IsSink (.middle 1) := by intro e; cases e <;> rename_i i <;> fin_cases i <;> decide
theorem sink3 : Q3.IsSink (.middle 2) := by intro e; cases e <;> rename_i i <;> fin_cases i <;> decide
theorem sink4 : Q4.IsSink (.outer 0) := by intro e; cases e <;> rename_i i <;> fin_cases i <;> decide
theorem sink5 : Q5.IsSink (.outer 1) := by intro e; cases e <;> rename_i i <;> fin_cases i <;> decide
theorem sink6 : Q6.IsSink (.outer 2) := by intro e; cases e <;> rename_i i <;> fin_cases i <;> decide

theorem sink_return : Q7 = Q0 := by
  ext e <;> cases e <;> rename_i i <;> fin_cases i <;> rfl

def sinkWordRaw : SinkWord Q0 Q7 :=
  .cons .center sink0 (.cons (.middle 0) sink1 (.cons (.middle 1) sink2
    (.cons (.middle 2) sink3 (.cons (.outer 0) sink4 (.cons (.outer 1) sink5
      (.cons (.outer 2) sink6 (.nil Q7)))))))

def encode (x : ReflectionReduction.Dimension) : E6Vertex → ℤ
  | .center => x.f
  | .middle i => ![x.u₁, x.u₂, x.u₃] i
  | .outer i => ![x.a₁, x.a₂, x.a₃] i

def vector (d : E6Vertex → ℤ) : ReflectionReduction.Dimension :=
  ⟨d .center, d (.middle 0), d (.middle 1), d (.middle 2),
    d (.outer 0), d (.outer 1), d (.outer 2)⟩

@[simp] theorem vector_encode (d : ReflectionReduction.Dimension) : vector (encode d) = d := by
  cases d; rfl

@[simp] theorem encode_vector (d : E6Vertex → ℤ) : encode (vector d) = d := by
  funext v
  cases v with
  | center => rfl
  | middle i => fin_cases i <;> rfl
  | outer i => fin_cases i <;> rfl

def neighbourSum (d : E6Vertex → ℤ) : E6Vertex → ℤ
  | .center => d (.middle 0) + d (.middle 1) + d (.middle 2)
  | .middle i => d .center + d (.outer i)
  | .outer i => d (.middle i)

def reflectDimension (s : E6Vertex) (d : E6Vertex → ℤ) (v : E6Vertex) : ℤ :=
  if v = s then neighbourSum d s - d s else d v

theorem sinkDimension0 (d : E6Vertex → ℤ) :
    sinkDimension Q0 .center d = reflectDimension .center d := by
  funext v
  unfold sinkDimension reflectDimension
  rw [sum_sinkIncident Q0 .center (fun e => d (Q0.source e)), sum_edges]
  simp [neighbourSum, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Orientation.reflect, inwardE6]

theorem sinkDimension1 (d : E6Vertex → ℤ) :
    sinkDimension Q1 (.middle 0) d = reflectDimension (.middle 0) d := by
  funext v
  unfold sinkDimension reflectDimension
  rw [sum_sinkIncident Q1 (.middle 0) (fun e => d (Q1.source e)), sum_edges]
  simp [neighbourSum, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Orientation.reflect, inwardE6]

theorem sinkDimension2 (d : E6Vertex → ℤ) :
    sinkDimension Q2 (.middle 1) d = reflectDimension (.middle 1) d := by
  funext v
  unfold sinkDimension reflectDimension
  rw [sum_sinkIncident Q2 (.middle 1) (fun e => d (Q2.source e)), sum_edges]
  simp [neighbourSum, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Orientation.reflect, inwardE6]

theorem sinkDimension3 (d : E6Vertex → ℤ) :
    sinkDimension Q3 (.middle 2) d = reflectDimension (.middle 2) d := by
  funext v
  unfold sinkDimension reflectDimension
  rw [sum_sinkIncident Q3 (.middle 2) (fun e => d (Q3.source e)), sum_edges]
  simp [neighbourSum, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Orientation.reflect, inwardE6]

theorem sinkDimension4 (d : E6Vertex → ℤ) :
    sinkDimension Q4 (.outer 0) d = reflectDimension (.outer 0) d := by
  funext v
  unfold sinkDimension reflectDimension
  rw [sum_sinkIncident Q4 (.outer 0) (fun e => d (Q4.source e)), sum_edges]
  simp [neighbourSum, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Orientation.reflect, inwardE6]

theorem sinkDimension5 (d : E6Vertex → ℤ) :
    sinkDimension Q5 (.outer 1) d = reflectDimension (.outer 1) d := by
  funext v
  unfold sinkDimension reflectDimension
  rw [sum_sinkIncident Q5 (.outer 1) (fun e => d (Q5.source e)), sum_edges]
  simp [neighbourSum, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Orientation.reflect, inwardE6]

theorem sinkDimension6 (d : E6Vertex → ℤ) :
    sinkDimension Q6 (.outer 2) d = reflectDimension (.outer 2) d := by
  funext v
  unfold sinkDimension reflectDimension
  rw [sum_sinkIncident Q6 (.outer 2) (fun e => d (Q6.source e)), sum_edges]
  simp [neighbourSum, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Orientation.reflect, inwardE6]

theorem sinkWordRaw_action (d : E6Vertex → ℤ) :
    sinkWordRaw.action d = encode (ReflectionReduction.sinkCycle (vector d)) := by
  simp only [sinkWordRaw, SinkWord.action]
  change sinkDimension Q6 (.outer 2) (sinkDimension Q5 (.outer 1)
    (sinkDimension Q4 (.outer 0) (sinkDimension Q3 (.middle 2)
      (sinkDimension Q2 (.middle 1) (sinkDimension Q1 (.middle 0)
        (sinkDimension Q0 .center d)))))) = _
  rw [sinkDimension0, sinkDimension1, sinkDimension2, sinkDimension3,
    sinkDimension4, sinkDimension5, sinkDimension6]
  funext v
  cases v with
  | center =>
    simp [reflectDimension, neighbourSum, encode, vector, ReflectionReduction.sinkCycle]
  | middle i =>
    fin_cases i <;>
      simp [reflectDimension, neighbourSum, encode, vector, ReflectionReduction.sinkCycle]
  | outer i =>
    fin_cases i <;>
      simp [reflectDimension, neighbourSum, encode, vector, ReflectionReduction.sinkCycle] <;> ring

abbrev P0 := inwardE6
def P1 := P0.reflect (.outer 0)
def P2 := P1.reflect (.outer 1)
def P3 := P2.reflect (.outer 2)
def P4 := P3.reflect (.middle 0)
def P5 := P4.reflect (.middle 1)
def P6 := P5.reflect (.middle 2)
def P7 := P6.reflect .center

theorem source0 : P0.IsSource (.outer 0) := by
  intro e; cases e <;> rename_i i <;> fin_cases i <;> decide
theorem source1 : P1.IsSource (.outer 1) := by
  intro e; cases e <;> rename_i i <;> fin_cases i <;> decide
theorem source2 : P2.IsSource (.outer 2) := by
  intro e; cases e <;> rename_i i <;> fin_cases i <;> decide
theorem source3 : P3.IsSource (.middle 0) := by
  intro e; cases e <;> rename_i i <;> fin_cases i <;> decide
theorem source4 : P4.IsSource (.middle 1) := by
  intro e; cases e <;> rename_i i <;> fin_cases i <;> decide
theorem source5 : P5.IsSource (.middle 2) := by
  intro e; cases e <;> rename_i i <;> fin_cases i <;> decide
theorem source6 : P6.IsSource .center := by
  intro e; cases e <;> rename_i i <;> fin_cases i <;> decide

theorem source_return : P7 = P0 := by
  ext e <;> cases e <;> rename_i i <;> fin_cases i <;> rfl

def sourceWordRaw : SourceWord P0 P7 :=
  .cons (.outer 0) source0 (.cons (.outer 1) source1 (.cons (.outer 2) source2
    (.cons (.middle 0) source3 (.cons (.middle 1) source4 (.cons (.middle 2) source5
      (.cons .center source6 (.nil P7)))))))

theorem sourceDimension0 (d : E6Vertex → ℤ) :
    sourceDimension P0 (.outer 0) d = reflectDimension (.outer 0) d := by
  funext v
  unfold sourceDimension reflectDimension
  rw [sum_sourceIncident P0 (.outer 0) (fun e => d (P0.target e)), sum_edges]
  simp [neighbourSum, P1, P2, P3, P4, P5, P6, P7, Orientation.reflect, inwardE6]

theorem sourceDimension1 (d : E6Vertex → ℤ) :
    sourceDimension P1 (.outer 1) d = reflectDimension (.outer 1) d := by
  funext v
  unfold sourceDimension reflectDimension
  rw [sum_sourceIncident P1 (.outer 1) (fun e => d (P1.target e)), sum_edges]
  simp [neighbourSum, P1, P2, P3, P4, P5, P6, P7, Orientation.reflect, inwardE6]

theorem sourceDimension2 (d : E6Vertex → ℤ) :
    sourceDimension P2 (.outer 2) d = reflectDimension (.outer 2) d := by
  funext v
  unfold sourceDimension reflectDimension
  rw [sum_sourceIncident P2 (.outer 2) (fun e => d (P2.target e)), sum_edges]
  simp [neighbourSum, P1, P2, P3, P4, P5, P6, P7, Orientation.reflect, inwardE6]

theorem sourceDimension3 (d : E6Vertex → ℤ) :
    sourceDimension P3 (.middle 0) d = reflectDimension (.middle 0) d := by
  funext v
  unfold sourceDimension reflectDimension
  rw [sum_sourceIncident P3 (.middle 0) (fun e => d (P3.target e)), sum_edges]
  simp [neighbourSum, P1, P2, P3, P4, P5, P6, P7, Orientation.reflect, inwardE6]

theorem sourceDimension4 (d : E6Vertex → ℤ) :
    sourceDimension P4 (.middle 1) d = reflectDimension (.middle 1) d := by
  funext v
  unfold sourceDimension reflectDimension
  rw [sum_sourceIncident P4 (.middle 1) (fun e => d (P4.target e)), sum_edges]
  simp [neighbourSum, P1, P2, P3, P4, P5, P6, P7, Orientation.reflect, inwardE6]

theorem sourceDimension5 (d : E6Vertex → ℤ) :
    sourceDimension P5 (.middle 2) d = reflectDimension (.middle 2) d := by
  funext v
  unfold sourceDimension reflectDimension
  rw [sum_sourceIncident P5 (.middle 2) (fun e => d (P5.target e)), sum_edges]
  simp [neighbourSum, P1, P2, P3, P4, P5, P6, P7, Orientation.reflect, inwardE6]

theorem sourceDimension6 (d : E6Vertex → ℤ) :
    sourceDimension P6 .center d = reflectDimension .center d := by
  funext v
  unfold sourceDimension reflectDimension
  rw [sum_sourceIncident P6 .center (fun e => d (P6.target e)), sum_edges]
  simp [neighbourSum, P1, P2, P3, P4, P5, P6, P7, Orientation.reflect, inwardE6]

theorem sourceWordRaw_action (d : E6Vertex → ℤ) :
    sourceWordRaw.action d = encode (ReflectionReduction.sourceCycle (vector d)) := by
  simp only [sourceWordRaw, SourceWord.action]
  change sourceDimension P6 .center (sourceDimension P5 (.middle 2)
    (sourceDimension P4 (.middle 1) (sourceDimension P3 (.middle 0)
      (sourceDimension P2 (.outer 2) (sourceDimension P1 (.outer 1)
        (sourceDimension P0 (.outer 0) d)))))) = _
  rw [sourceDimension0, sourceDimension1, sourceDimension2, sourceDimension3,
    sourceDimension4, sourceDimension5, sourceDimension6]
  funext v
  cases v with
  | center =>
    simp [reflectDimension, neighbourSum, encode, vector, ReflectionReduction.sourceCycle]
    ring
  | middle i =>
    fin_cases i <;>
      simp [reflectDimension, neighbourSum, encode, vector, ReflectionReduction.sourceCycle] <;> ring
  | outer i =>
    fin_cases i <;>
      simp [reflectDimension, neighbourSum, encode, vector, ReflectionReduction.sourceCycle]

def sinkWord : SinkWord inwardE6 inwardE6 := sinkWordRaw.castTarget sink_return
def sourceWord : SourceWord inwardE6 inwardE6 := sourceWordRaw.castTarget source_return

@[simp] theorem sinkWord_action (d : E6Vertex → ℤ) :
    sinkWord.action d = encode (ReflectionReduction.sinkCycle (vector d)) := by
  rw [sinkWord, SinkWord.action_castTarget, sinkWordRaw_action]

@[simp] theorem sourceWord_action (d : E6Vertex → ℤ) :
    sourceWord.action d = encode (ReflectionReduction.sourceCycle (vector d)) := by
  rw [sourceWord, SourceWord.action_castTarget, sourceWordRaw_action]

def sinkBlockWord := sinkWord.power 6
def sourceBlockWord := sourceWord.power 6

@[simp] theorem sinkBlockWord_action (d : E6Vertex → ℤ) :
    sinkBlockWord.action d = encode (ReflectionReduction.sixSinks (vector d)) := by
  simp [sinkBlockWord, SinkWord.power, SinkWord.action_append, sinkWord_action,
    vector_encode, SinkWord.action, ReflectionReduction.sixSinks]

@[simp] theorem sourceBlockWord_action (d : E6Vertex → ℤ) :
    sourceBlockWord.action d = encode (ReflectionReduction.sixSources (vector d)) := by
  simp [sourceBlockWord, SourceWord.power, SourceWord.action_append, sourceWord_action,
    vector_encode, SourceWord.action, ReflectionReduction.sixSources]

theorem sinkBlocks_action (n : ℕ) (d : E6Vertex → ℤ) :
    (sinkBlockWord.power n).action d = encode (ReflectionReduction.sinkBlocks n (vector d)) := by
  induction n with
  | zero => simp [SinkWord.power, SinkWord.action, ReflectionReduction.sinkBlocks]
  | succ n ih =>
    rw [SinkWord.power, SinkWord.action_append, ih, sinkBlockWord_action, vector_encode]
    rfl

theorem sourceBlocks_action (n : ℕ) (d : E6Vertex → ℤ) :
    (sourceBlockWord.power n).action d = encode (ReflectionReduction.sourceBlocks n (vector d)) := by
  induction n with
  | zero => simp [SourceWord.power, SourceWord.action, ReflectionReduction.sourceBlocks]
  | succ n ih =>
    rw [SourceWord.power, SourceWord.action_append, ih, sourceBlockWord_action, vector_encode]
    rfl

/-- Negative defect now terminates an actual representation-reflection sequence
at an actual one-dimensional vertex representation. -/
theorem negative_defect_reaches_simple {K : Type} [Field K] (R : Rep K inwardE6)
    [∀ v, FiniteDimensional K (R.space v)] (hR : Indecomposable R)
    (hd : ReflectionReduction.defect (vector (dimension R)) < 0) : ReachesSimple R := by
  obtain ⟨n, hn⟩ := ReflectionReduction.negative_defect_terminates (vector (dimension R)) hd
  apply (sinkBlockWord.power n).reachesSimple_of_negative R hR .center
  rw [sinkBlocks_action]
  exact hn

/-- Positive defect is handled by actual cokernel reflections, with the local
injectivity conditions derived from indecomposability along the trajectory. -/
theorem positive_defect_reaches_simple {K : Type} [Field K] (R : Rep K inwardE6)
    [∀ v, FiniteDimensional K (R.space v)] (hR : Indecomposable R)
    (hd : 0 < ReflectionReduction.defect (vector (dimension R))) : ReachesSimple R := by
  obtain ⟨n, hn⟩ := ReflectionReduction.positive_defect_terminates (vector (dimension R)) hd
  apply (sourceBlockWord.power n).reachesSimple_of_negative R hR .center
  rw [sourceBlocks_action]
  exact hn

theorem nonzero_defect_reaches_simple {K : Type} [Field K] (R : Rep K inwardE6)
    [∀ v, FiniteDimensional K (R.space v)] (hR : Indecomposable R)
    (hd : ReflectionReduction.defect (vector (dimension R)) ≠ 0) : ReachesSimple R := by
  rcases lt_or_gt_of_ne hd with hn | hp
  · exact negative_defect_reaches_simple R hR hn
  · exact positive_defect_reaches_simple R hR hp

/-- Original-field uniqueness for nonzero-defect indecomposables is obtained by
actual reflection and reverse isomorphism transport, without Kac as a hypothesis. -/
theorem nonzero_defect_unique {K : Type} [Field K] (R S : Rep K inwardE6)
    [∀ v, FiniteDimensional K (R.space v)] [∀ v, FiniteDimensional K (S.space v)]
    (hR : Indecomposable R) (hS : Indecomposable S) (heq : dimension R = dimension S)
    (hd : ReflectionReduction.defect (vector (dimension R)) ≠ 0) : Nonempty (Iso R S) := by
  rcases lt_or_gt_of_ne hd with hn | hp
  · obtain ⟨n, hneg⟩ := ReflectionReduction.negative_defect_terminates (vector (dimension R)) hn
    apply (sinkBlockWord.power n).unique_of_negative R S hR hS heq .center
    rw [sinkBlocks_action]
    exact hneg
  · obtain ⟨n, hneg⟩ := ReflectionReduction.positive_defect_terminates (vector (dimension R)) hp
    apply (sourceBlockWord.power n).unique_of_negative R S hR hS heq .center
    rw [sourceBlocks_action]
    exact hneg

end UploadBroadcast.E6Reflection
