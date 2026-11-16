import UploadBroadcast.IntersectionProbes
import UploadBroadcast.NonzeroDefectProfile
import UploadBroadcast.EdgeExtraction
import UploadBroadcast.QuiverEuler

/-!
# Actual ranks of the nonzero-defect families

This file assembles the concrete intersection computations into the geometric
rank conditions used by the fifteen-entry profile calculation.
-/
namespace UploadBroadcast.NonzeroFamilyRanks
open Module NonzeroDefectProfile IntersectionProbes QuiverRepresentation

variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Family membership records only the seven dimensions of the original task. -/
structure Dimensions (T : UploadBroadcast.Task K F) (g : Family) (n : ℕ) : Prop where
  ambient : finrank K F = fullAmbient g n
  side : ∀ i, finrank K ↥(T.A i) = fullSide g n i
  signal : ∀ i, finrank K ↥(T.U i) = fullSignal g n i

omit [FiniteDimensional K F] in
lemma triple_inf_eq (T : UploadBroadcast.Task K F) (i j k : Three)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (T.U i ⊓ T.U j) ⊓ T.U k = (T.U 0 ⊓ T.U 1) ⊓ T.U 2 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all only [ne_eq, not_true_eq_false, Submodule.mem_inf] <;>
    ext x <;> simp only [Submodule.mem_inf] <;> tauto

/-- The dimension identities force the actual joins and conditional ranks.
This intermediate lemma is purely modular linear algebra; its hypotheses are
subspace dimensions, not any of the fifteen desired profile entries. -/
theorem rankConditions_of_intersection_dimensions
    (T : UploadBroadcast.Task K F) (a u : Three → ℕ)
    (ha : ∀ i, finrank K ↥(T.A i) = a i)
    (hu : ∀ i, finrank K ↥(T.U i) = u i)
    (hpair : ∀ i j, i ≠ j →
      finrank K ↥(T.U i ⊓ T.U j) + finrank K F = u i + u j)
    (htriple : finrank K ↥(T.U 0 ⊓ T.U 1 ⊓ T.U 2) + 2 * finrank K F =
      u 0 + u 1 + u 2)
    (has : ∀ i j, i ≠ j → finrank K ↥(T.A j ⊓ T.U i) + finrank K F = a j + u i)
    (hat : ∀ i, finrank K ↥((T.U 0 ⊓ T.U 1 ⊓ T.U 2) ⊓ T.A i) = 0) :
    RankConditions T ⊤ a u := by
  have hpairSpan (i j : Three) (hij : i ≠ j) : T.U i ⊔ T.U j = ⊤ := by
    apply Submodule.eq_of_le_of_finrank_eq le_top
    have hh := Submodule.finrank_sup_add_finrank_inf_eq (T.U i) (T.U j)
    have hp := hpair i j hij
    simp only [hu, finrank_top] at *
    omega
  have hjoint (i j k : Three) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      (T.U i ⊓ T.U j) ⊔ T.U k = ⊤ := by
    apply Submodule.eq_of_le_of_finrank_eq le_top
    have hh := Submodule.finrank_sup_add_finrank_inf_eq (T.U i ⊓ T.U j) (T.U k)
    rw [triple_inf_eq T i j k hij hik hjk, hu] at hh
    have hp := hpair i j hij
    have hsum : u 0 + u 1 + u 2 = u i + u j + u k := by
      have he := sum_three_perm u i j k hij hik hjk
      simpa [Fin.sum_univ_succ, add_assoc] using he
    simp only [finrank_top]
    omega
  refine ⟨ha,hu,fun _ => le_top,hpairSpan,?_,?_,?_⟩
  · intro i j k hij hik hjk
    exact pair_intersections_span_of_join _ _ _ _ le_top (hjoint i j k hij hik hjk)
  · intro i j hij
    have hc := condRank_add_intersection (T.U i ⊓ T.U j) (T.A j)
    have he : T.A j ⊓ (T.U i ⊓ T.U j) = T.A j ⊓ T.U i := by
      ext x
      exact ⟨fun h => ⟨h.1,h.2.1⟩, fun h => ⟨h.1,h.2,T.side_le_signal j h.1⟩⟩
    rw [he] at hc
    have hp := hpair i j hij
    have hs := has i j hij
    have haj : a j ≤ u j := by
      simpa only [ha,hu] using Submodule.finrank_mono (T.side_le_signal j)
    simp only [finrank_top]
    omega
  · intro i
    have hc := condRank_add_intersection (T.U 0 ⊓ T.U 1 ⊓ T.U 2) (T.A i)
    rw [inf_comm (T.A i) (T.U 0 ⊓ T.U 1 ⊓ T.U 2), hat i, add_zero] at hc
    simp only [finrank_top]
    omega

lemma full_pair_nonnegative (g : Family) (n : ℕ) (hn : 1 ≤ n) (i j : Three) :
    fullAmbient g n ≤ fullSignal g n i + fullSignal g n j := by
  cases g <;> fin_cases i <;> fin_cases j <;>
    simp [fullAmbient,fullSignal] <;> omega

lemma full_side_signal_nonnegative (g : Family) (n : ℕ) (_hn : 1 ≤ n) (i j : Three) (hij : i ≠ j) :
    fullAmbient g n ≤ fullSide g n j + fullSignal g n i := by
  cases g <;> fin_cases i <;> fin_cases j <;>
    simp_all [fullAmbient,fullSide,fullSignal] <;> omega

lemma full_triple_nonnegative (g : Family) (n : ℕ) (_hn : 1 ≤ n) :
    2 * fullAmbient g n ≤ fullSignal g n 0 + fullSignal g n 1 + fullSignal g n 2 := by
  cases g <;> simp [fullAmbient,fullSignal] <;> omega

lemma full_side_triple_nonpositive (g : Family) (n : ℕ) (hn : 1 ≤ n) (i : Three) :
    fullSide g n i + fullSignal g n 0 + fullSignal g n 1 + fullSignal g n 2 ≤
      2 * fullAmbient g n + fullSignal g n i := by
  cases g <;> fin_cases i <;> simp_all [fullAmbient,fullSide,fullSignal] <;> omega

lemma sum_vertices (f : E6Vertex → ℤ) :
    ∑ v, f v = f .center + f (.middle 0) + f (.middle 1) + f (.middle 2) +
      f (.outer 0) + f (.outer 1) + f (.outer 2) := by
  have h : (Finset.univ : Finset E6Vertex) =
      {.center,.middle 0,.middle 1,.middle 2,.outer 0,.outer 1,.outer 2} := by decide
  rw [h]
  simp [add_assoc]

lemma euler_signalPair (d : E6Vertex → ℤ) (i j : Three) (hij : i ≠ j) :
    eulerForm inwardE6 (signalPair i j).dimension d =
      d (.middle i) + d (.middle j) - d .center := by
  simp only [eulerForm,sum_vertices,E6Reflection.sum_edges]
  fin_cases i <;> fin_cases j <;>
    simp_all [Probe.dimension,signalPair,inwardE6] <;> ring

lemma euler_sideSignal (d : E6Vertex → ℤ) (i j : Three) (hij : i ≠ j) :
    eulerForm inwardE6 (sideSignal i j).dimension d =
      d (.outer i) + d (.middle j) - d .center := by
  simp only [eulerForm,sum_vertices,E6Reflection.sum_edges]
  fin_cases i <;> fin_cases j <;>
    simp_all [Probe.dimension,sideSignal,inwardE6] <;> ring

lemma euler_signalTriple (d : E6Vertex → ℤ) :
    eulerForm inwardE6 signalTriple.dimension d =
      d (.middle 0) + d (.middle 1) + d (.middle 2) - 2 * d .center := by
  simp [eulerForm,sum_vertices,E6Reflection.sum_edges,Probe.dimension,signalTriple,inwardE6]
  ring

lemma euler_sideTriple (d : E6Vertex → ℤ) (i : Three) :
    eulerForm inwardE6 (sideTriple i).dimension d =
      d (.outer i) + d (.middle 0) + d (.middle 1) + d (.middle 2) -
        d (.middle i) - 2 * d .center := by
  simp only [eulerForm,sum_vertices,E6Reflection.sum_edges]
  fin_cases i <;> simp [Probe.dimension,sideTriple,inwardE6] <;> ring

lemma euler_sidePair (d : E6Vertex → ℤ) (i j : Three) (hij : i ≠ j) :
    eulerForm inwardE6 (sidePair i j).dimension d =
      d (.outer i) + d (.outer j) - d .center := by
  simp only [eulerForm,sum_vertices,E6Reflection.sum_edges]
  fin_cases i <;> fin_cases j <;>
    simp_all [Probe.dimension,sidePair,inwardE6] <;> ring

/-- Probe ranks from actual indecomposability and positive defect, over the
original field and with no generic-orbit hypothesis. -/
theorem probe_intersection_finrank (T : TaskDecomposition.Task K F)
    (hT : TaskDecomposition.Indecomposable T.spaces ⊤)
    (hd : 0 < ReflectionReduction.defect T.dimensionVector) (p : Probe) :
    (finrank K (p.intersection T) : ℤ) =
      max 0 (eulerForm inwardE6 p.dimension (dimension T.toRep)) := by
  rw [← p.hom_finrank T]
  have hh := E6Reflection.hom_finrank_eq_max_euler_of_positive_defect
    (p.task K).toRep T.toRep (p.rep_indecomposable K) (T.rep_indec_of_indec hT) hd
  simpa only [Probe.rep_dimension] using hh

omit [FiniteDimensional K F] in
lemma Dimensions.positive_defect (T : UploadBroadcast.Task K F) (g : Family) (n : ℕ)
    (h : Dimensions T g n) :
    0 < ReflectionReduction.defect (EdgeExtraction.configuration T).dimensionVector := by
  simp only [TaskDecomposition.Task.dimensionVector, EdgeExtraction.configuration,
    ReflectionReduction.defect, h.ambient, h.side, h.signal]
  cases g <;> simp_all [fullAmbient,fullSide,fullSignal] <;> omega

/-- Actual signal-pair intersection dimension for every listed full family. -/
theorem full_signal_pair_dimension (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n)
    (i j : Three) (hij : i ≠ j) :
    finrank K ↥(T.U i ⊓ T.U j) + finrank K F = fullSignal g n i + fullSignal g n j := by
  have hh := probe_intersection_finrank (EdgeExtraction.configuration T) hT
    (h.positive_defect T g n) (signalPair i j)
  rw [signalPair_intersection, euler_signalPair _ i j hij] at hh
  change (finrank K ↥(T.U i ⊓ T.U j) : ℤ) =
    max 0 ((finrank K (T.U i) : ℤ) + finrank K (T.U j) - finrank K F) at hh
  rw [h.signal,h.signal,h.ambient] at hh
  have hb := full_pair_nonnegative g n hn i j
  rw [h.ambient]
  omega

/-- Actual side-signal intersection dimension, obtained from the regular path probe. -/
theorem full_side_signal_dimension (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n)
    (i j : Three) (hij : i ≠ j) :
    finrank K ↥(T.A j ⊓ T.U i) + finrank K F = fullSide g n j + fullSignal g n i := by
  have hh := probe_intersection_finrank (EdgeExtraction.configuration T) hT
    (h.positive_defect T g n) (sideSignal j i)
  rw [sideSignal_intersection, euler_sideSignal _ j i hij.symm] at hh
  change (finrank K ↥(T.A j ⊓ T.U i) : ℤ) =
    max 0 ((finrank K (T.A j) : ℤ) + finrank K (T.U i) - finrank K F) at hh
  rw [h.side,h.signal,h.ambient] at hh
  have hb := full_side_signal_nonnegative g n hn i j hij
  rw [h.ambient]
  omega

/-- Actual triple signal dimension, obtained from its three-arm thin probe. -/
theorem full_signal_triple_dimension (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) :
    finrank K ↥(T.U 0 ⊓ T.U 1 ⊓ T.U 2) + 2 * finrank K F =
      fullSignal g n 0 + fullSignal g n 1 + fullSignal g n 2 := by
  have hh := probe_intersection_finrank (EdgeExtraction.configuration T) hT
    (h.positive_defect T g n) signalTriple
  rw [signalTriple_intersection, euler_signalTriple] at hh
  change (finrank K ↥(T.U 0 ⊓ T.U 1 ⊓ T.U 2) : ℤ) =
    max 0 ((finrank K (T.U 0) : ℤ) + finrank K (T.U 1) + finrank K (T.U 2) -
      2 * finrank K F) at hh
  rw [h.signal,h.signal,h.signal,h.ambient] at hh
  have hb := full_triple_nonnegative g n hn
  rw [h.ambient]
  omega

/-- Each side is disjoint from the common triple signal space. -/
theorem full_side_triple_dimension (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) (i : Three) :
    finrank K ↥((T.U 0 ⊓ T.U 1 ⊓ T.U 2) ⊓ T.A i) = 0 := by
  have hh := probe_intersection_finrank (EdgeExtraction.configuration T) hT
    (h.positive_defect T g n) (sideTriple i)
  rw [sideTriple_intersection, euler_sideTriple] at hh
  change (finrank K ↥((T.U 0 ⊓ T.U 1 ⊓ T.U 2) ⊓ T.A i) : ℤ) =
    max 0 ((finrank K (T.A i) : ℤ) + finrank K (T.U 0) + finrank K (T.U 1) +
      finrank K (T.U 2) - finrank K (T.U i) - 2 * finrank K F) at hh
  rw [h.side,h.signal,h.signal,h.signal,h.signal,h.ambient] at hh
  have hb := full_side_triple_nonpositive g n hn i
  omega

/-- Full-task geometric ranks for all eight actual indecomposable families.
Only indecomposability and the seven defining dimensions are assumed. -/
theorem full_rankConditions (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) :
    RankConditions T ⊤ (fullSide g n) (fullSignal g n) :=
  rankConditions_of_intersection_dimensions T _ _ h.side h.signal
    (full_signal_pair_dimension T hT g n hn h)
    (full_signal_triple_dimension T hT g n hn h)
    (full_side_signal_dimension T hT g n hn h)
    (full_side_triple_dimension T hT g n hn h)

lemma full_side_pair_nonpositive (g : Family) (n : ℕ) (hn : 1 ≤ n) (i j : Three)
    (hij : i ≠ j) : fullSide g n i + fullSide g n j ≤ fullAmbient g n := by
  cases g <;> fin_cases i <;> fin_cases j <;>
    simp_all [fullAmbient,fullSide] <;> omega

/-- Pairwise disjointness is derived from the actual configuration as well. -/
theorem full_side_pair_eq_bot (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n)
    (i j : Three) (hij : i ≠ j) : T.A i ⊓ T.A j = ⊥ := by
  have hh := probe_intersection_finrank (EdgeExtraction.configuration T) hT
    (h.positive_defect T g n) (sidePair i j)
  rw [sidePair_intersection,euler_sidePair _ i j hij] at hh
  change (finrank K ↥(T.A i ⊓ T.A j) : ℤ) =
    max 0 ((finrank K (T.A i) : ℤ) + finrank K (T.A j) - finrank K F) at hh
  rw [h.side,h.side,h.ambient] at hh
  have hb := full_side_pair_nonpositive g n hn i j hij
  exact Submodule.finrank_eq_zero.mp (by omega)

/-- The original side spaces necessarily span the full ambient space. -/
theorem full_spanning (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) : T.Spanning := by
  have hs := (full_rankConditions T hT g n hn h).pair_span 0 1 (by decide)
  apply top_unique
  rw [←hs]
  exact sup_le (T.feasible 0) (T.feasible 1)

/-- All six full first-family entries for the actual nonzero-defect task. -/
theorem full_first_profile (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) (r : Fin 6) :
    Profile.entry T (.inl r) = (fullFirst g n r : ℝ) :=
  full_first_entries T ⊤ g n hn (by simpa using h.ambient)
    (full_rankConditions T hT g n hn h) r

/-- All nine full doubled second-family entries for the actual task. -/
theorem full_second_profile (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) (i ell : Three) :
    2 * Profile.entry T (.inr (i,ell)) = (doubledSecond g n : ℝ) :=
  full_second_entries T ⊤ g n hn (by simpa using h.ambient)
    (full_rankConditions T hT g n hn h) i ell

end UploadBroadcast.NonzeroFamilyRanks
