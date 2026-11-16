import UploadBroadcast.QuiverTits
import UploadBroadcast.QuiverHomTerminal

/-! Directed Euler form and actual simultaneous-reflection Hom ranks. -/
namespace UploadBroadcast.QuiverRepresentation

universe u
variable {K V E : Type u} [Field K] [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]

def eulerForm (Q : Orientation V E) (d e : V → ℤ) : ℤ :=
  (∑ v, d v * e v) - ∑ a, d (Q.source a) * e (Q.target a)

omit [DecidableEq E] in
/-- Simultaneous source reflection preserves the directed Euler pairing. -/
theorem eulerForm_sourceDimension (Q : Orientation V E) (s : V) (hs : Q.IsSource s)
    (d e : V → ℤ) :
    eulerForm (Q.reflect s) (sourceDimension Q s d) (sourceDimension Q s e) = eulerForm Q d e := by
  let nd := ∑ a : SourceIncident Q s, d (Q.target a.val)
  let ne := ∑ a : SourceIncident Q s, e (Q.target a.val)
  have hv : (∑ v, sourceDimension Q s d v * sourceDimension Q s e v) =
      (∑ v, d v * e v) + ((nd-d s)*(ne-e s)-d s*e s) := by
    calc
      _ = ∑ v, (d v * e v + if v = s then (nd-d s)*(ne-e s)-d s*e s else 0) := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases h : v = s
        · subst v; simp [sourceDimension, nd, ne]
        · simp [sourceDimension, h]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have ha : ∀ a, sourceDimension Q s d ((Q.reflect s).source a) *
      sourceDimension Q s e ((Q.reflect s).target a) =
      d (Q.source a)*e (Q.target a) +
        (if Q.source a = s then d (Q.target a) else 0)*(ne-e s) -
        d s*(if Q.source a = s then e (Q.target a) else 0) := by
    intro a
    by_cases ht : Q.source a = s
    · simp [Orientation.reflect, sourceDimension, hs a, ht, ne]
    · simp [Orientation.reflect, sourceDimension, hs a, ht]
  have hsum : (∑ a, sourceDimension Q s d ((Q.reflect s).source a) *
      sourceDimension Q s e ((Q.reflect s).target a)) =
      (∑ a, d (Q.source a)*e (Q.target a)) + nd*(ne-e s)-d s*ne := by
    simp_rw [ha]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      ← sum_sourceIncident_eq Q s (fun a => d (Q.target a)),
      ← sum_sourceIncident_eq Q s (fun a => e (Q.target a))]
  unfold eulerForm
  rw [hv, hsum]
  ring

omit [DecidableEq E] in
theorem eulerForm_sourceSimple_target {Q : Orientation V E} (R S : Rep K Q) {s : V}
    (hs : Q.IsSource s) (hS : VertexSimple S s) :
    eulerForm Q (dimension R) (dimension S) = dimension R s := by
  rw [hS.dimension]
  have hz (a : E) : Q.target a ≠ s := hs a
  simp [eulerForm, hz, mul_ite]

omit [DecidableEq E] in
theorem eulerForm_sourceSimple_domain {Q : Orientation V E} (R S : Rep K Q) {s : V}
    (hR : VertexSimple R s) : eulerForm Q (dimension R) (dimension S) =
      dimension S s - ∑ a : SourceIncident Q s, dimension S (Q.target a.val) := by
  rw [hR.dimension, sum_sourceIncident_eq Q s (fun a => dimension S (Q.target a))]
  simp [eulerForm, ite_mul]

theorem eulerForm_sourceSimple_nonpos {Q : Orientation V E} (R S : Rep K Q) {s : V}
    [∀ v, FiniteDimensional K (S.space v)] (hs : Q.IsSource s) (hR : VertexSimple R s)
    (hi : Function.Injective (sourceOutgoing S hs)) : eulerForm Q (dimension R) (dimension S) ≤ 0 := by
  rw [eulerForm_sourceSimple_domain R S hR]
  have hh := congrFun (dimension_sourceReflect S hs hi) s
  simp [sourceDimension] at hh
  have hn : 0 ≤ dimension (sourceReflect S hs) s := Int.natCast_nonneg _
  linarith

/-- Exact Hom rank from a source word with negative target endpoint. The proof
stops at whichever actual indecomposable becomes a selected vertex-simple first;
no regularity or survival assumption on the source object is required. -/
theorem SourceWord.hom_finrank_eq_max_euler_of_negative {Q Q' : Orientation V E}
    (w : SourceWord Q Q') (R S : Rep K Q)
    [∀ v, FiniteDimensional K (R.space v)] [∀ v, FiniteDimensional K (S.space v)]
    (hR : Indecomposable R) (hS : Indecomposable S)
    (v : V) (hneg : w.action (dimension S) v < 0) :
    (Module.finrank K (Hom R S) : ℤ) = max 0 (eulerForm Q (dimension R) (dimension S)) := by
  induction w with
  | nil => exact False.elim (not_lt_of_ge (Int.natCast_nonneg _) hneg)
  | @cons Q Q' s hs tail ih =>
    rcases source_step S hs hS with hsimp | ⟨hiS, heS⟩
    · rw [hom_finrank_sourceSimpleTarget R S hs hsimp, eulerForm_sourceSimple_target R S hs hsimp]
      exact (max_eq_right (Int.natCast_nonneg _)).symm
    · rcases source_step R hs hR with hrimp | ⟨hiR, heR⟩
      · haveI : Subsingleton (Hom R S) := ⟨fun f g =>
          (supportedSource_hom_zero R S hs hrimp.1 heS f).trans
            (supportedSource_hom_zero R S hs hrimp.1 heS g).symm⟩
        rw [Module.finrank_zero_of_subsingleton]
        exact (max_eq_left (eulerForm_sourceSimple_nonpos R S hs hrimp heS)).symm
      · have hn' : tail.action (dimension (sourceReflect S hs)) v < 0 := by
          rw [dimension_sourceReflect S hs heS]
          exact hneg
        rw [(sourceReflectHomLinearEquiv R S hs heR heS).finrank_eq]
        rw [ih (sourceReflect R hs) (sourceReflect S hs) hiR hiS hn']
        rw [dimension_sourceReflect R hs heR, dimension_sourceReflect S hs heS,
          eulerForm_sourceDimension Q s hs]

end UploadBroadcast.QuiverRepresentation

namespace UploadBroadcast.E6Reflection
open QuiverRepresentation

/-- Any indecomposable probe against a positive-defect indecomposable has the
maximal Hom rank, computed by a checked Euler pairing rather than a genericity assumption. -/
theorem hom_finrank_eq_max_euler_of_positive_defect {K : Type} [Field K]
    (R S : Rep K inwardE6) [∀ v, FiniteDimensional K (R.space v)]
    [∀ v, FiniteDimensional K (S.space v)] (hR : Indecomposable R) (hS : Indecomposable S)
    (hd : 0 < ReflectionReduction.defect (vector (dimension S))) :
    (Module.finrank K (Hom R S) : ℤ) = max 0 (eulerForm inwardE6 (dimension R) (dimension S)) := by
  obtain ⟨n, hn⟩ := ReflectionReduction.positive_defect_terminates (vector (dimension S)) hd
  apply (sourceBlockWord.power n).hom_finrank_eq_max_euler_of_negative R S hR hS .center
  rw [sourceBlocks_action]
  exact hn

end UploadBroadcast.E6Reflection
