import UploadBroadcast.RankLoss
import UploadBroadcast.ProfileTransport

/-!
# Fifteen-entry rank calculations for nonzero-defect families

These are conditional on explicit geometric spanning and maximal conditional
rank hypotheses. They do not assume the desired fifteen-entry profile, nor do
they assert the unproved dense-orbit transfer to classified indecomposables.
-/
namespace UploadBroadcast.NonzeroDefectProfile
open Module Profile
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Sufficient geometric ranks used by the source calculation. The last
condition is the triple rank after using `0 ≤ t ≤ min m_i`. -/
structure RankConditions (T : Task K F) (V : Submodule K F)
    (a u : Three → ℕ) : Prop where
  side_dimension : ∀ i, finrank K (T.A i) = a i
  signal_dimension : ∀ i, finrank K (T.U i) = u i
  signal_le : ∀ i, T.U i ≤ V
  pair_span : ∀ i j, i ≠ j → T.U i ⊔ T.U j = V
  pair_intersections_span : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k) = T.U i
  pair_rank : ∀ i j, i ≠ j → condRank (T.U i ⊓ T.U j) (T.A j) =
    min (u j - a j) (u i + u j - finrank K V)
  triple_rank : ∀ ell, condRank (T.U 0 ⊓ T.U 1 ⊓ T.U 2) (T.A ell) =
    (u 0 + u 1 + u 2 - 2 * finrank K V)

lemma sum_three_perm (m : Three → ℕ) (i j k : Three)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ r, m r = m i + m j + m k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [Fin.sum_univ_succ] <;> omega

lemma condRank_signal (T : Task K F) (i : Three) :
    condRank (T.U i) (T.A i) = finrank K (T.U i) - finrank K (T.A i) := by
  rw [condRank, sup_eq_right.mpr (T.side_le_signal i)]

/-- All six first-family entries from the geometric rank hypotheses. -/
theorem firstEntry_formula (T : Task K F) (V : Submodule K F) (a u : Three → ℕ)
    (h : RankConditions T V a u) (i j k : Three)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    firstEntry T i j k = ((u i - a i : ℕ) : ℝ) + ((u j - a j : ℕ) : ℝ) -
      (min (u j - a j) (u i + u j - finrank K V) : ℕ) := by
  have htotal : totalDemand T = (u i - a i) + (u j - a j) + (u k - a k) := by
    simp only [totalDemand, h.side_dimension, h.signal_dimension]
    exact sum_three_perm _ i j k hij hik hjk
  rw [firstEntry, htotal, h.pair_span i j hij,
    inf_eq_left.mpr (h.signal_le k), condRank_signal,
    h.side_dimension, h.signal_dimension, h.pair_rank i j hij]
  push_cast
  ring

/-- All nine doubled second-family entries from the same geometric hypotheses. -/
theorem secondEntry_formula (T : Task K F) (V : Submodule K F) (a u : Three → ℕ)
    (h : RankConditions T V a u) (i j k ell : Three)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    2 * secondEntry T i j k ell =
      ((u 0 - a 0 : ℕ) : ℝ) + ((u 1 - a 1 : ℕ) : ℝ) +
        ((u 2 - a 2 : ℕ) : ℝ) -
        ((u 0 + u 1 + u 2 - 2 * finrank K V : ℕ) : ℝ) := by
  have htotal : (totalDemand T : ℝ) =
      ((u i - a i : ℕ) : ℝ) + ((u j - a j : ℕ) : ℝ) +
        ((u k - a k : ℕ) : ℝ) := by
    have hh : totalDemand T = (u i - a i) + (u j - a j) + (u k - a k) := by
      simp only [totalDemand, h.side_dimension, h.signal_dimension]
      exact sum_three_perm _ i j k hij hik hjk
    rw [hh]; push_cast; rfl
  have htotal' : (totalDemand T : ℝ) =
      ((u 0 - a 0 : ℕ) : ℝ) + ((u 1 - a 1 : ℕ) : ℝ) +
        ((u 2 - a 2 : ℕ) : ℝ) := by
    simp [totalDemand, h.side_dimension, h.signal_dimension, Fin.sum_univ_succ, add_assoc]
  rw [secondEntry, h.pair_intersections_span i j k hij hik hjk,
    h.pair_span i k hik, h.pair_span i j hij,
    inf_eq_left.mpr (h.signal_le j), inf_eq_left.mpr (h.signal_le k),
    condRank_signal, condRank_signal, condRank_signal,
    h.triple_rank, h.side_dimension, h.side_dimension, h.side_dimension,
    h.signal_dimension, h.signal_dimension, h.signal_dimension]
  linarith

inductive Family | T1 | T2 | T3 | R0 | R1 | R2 | O | H
  deriving DecidableEq, Fintype

def fullAmbient (g : Family) (n : ℕ) : ℕ :=
  match g with
  | .T1 | .T2 | .T3 => 3*n+2
  | .R0 | .R1 | .R2 => 3*n+1
  | .O | .H => 3*n

def fullSide (g : Family) (n : ℕ) : Three → ℕ :=
  match g with
  | .T1 | .T2 | .T3 | .R2 => ![n+1,n+1,n+1]
  | .R0 | .R1 => ![n,n+1,n+1]
  | .O | .H => ![n,n,n+1]

def fullSignal (g : Family) (n : ℕ) : Three → ℕ :=
  match g with
  | .T1 => ![2*n+2,2*n+1,2*n+1]
  | .T2 => ![2*n+2,2*n+2,2*n+1]
  | .T3 => ![2*n+2,2*n+2,2*n+2]
  | .R0 => ![2*n,2*n+1,2*n+1]
  | .R1 | .R2 => ![2*n+1,2*n+1,2*n+1]
  | .O => ![2*n,2*n,2*n]
  | .H => ![2*n,2*n,2*n+1]

def sideDrop (g : Family) : Three → ℕ :=
  match g with
  | .T1 | .T3 | .O => ![1,0,1]
  | .T2 => ![1,1,0]
  | .R0 | .R1 | .H => ![0,1,1]
  | .R2 => ![1,1,2]

def codimension (g : Family) : ℕ := if g = .R2 then 2 else 1

def inducedSide (g : Family) (n : ℕ) (i : Three) : ℕ := fullSide g n i - sideDrop g i
def inducedSignal (g : Family) (n : ℕ) (i : Three) : ℕ := fullSignal g n i - sideDrop g i

def fullFirst (g : Family) (n : ℕ) : Fin 6 → ℕ :=
  match g with
  | .T1 | .R1 => ![n+1,n+1,n,n,n,n]
  | .T2 => ![n+1,n+1,n+1,n+1,n,n]
  | .T3 => ![n+1,n+1,n+1,n+1,n+1,n+1]
  | .O => ![n,n,n,n,n-1,n-1]
  | .R0 | .R2 | .H => ![n,n,n,n,n,n]

def firstIncrement (g : Family) : Fin 6 → ℕ :=
  match g with
  | .T1 | .O => ![0,0,0,0,1,0]
  | _ => ![0,0,0,0,0,0]

def doubledSecond (g : Family) (n : ℕ) : ℕ :=
  match g with
  | .T1 | .T2 | .T3 => 3*n+1
  | .R0 | .R1 => 3*n
  | .R2 | .O | .H => 3*n-1


/-- Natural-valued dimension formula, with no truncated subtraction after
casting because the minimum is bounded by the second demand. -/
theorem firstEntry_nat_formula (T : Task K F) (V : Submodule K F) (a u : Three → ℕ)
    (h : RankConditions T V a u) (i j k : Three)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    firstEntry T i j k =
      (((u i - a i) + (u j - a j) -
        min (u j - a j) (u i + u j - finrank K V) : ℕ) : ℝ) := by
  rw [firstEntry_formula T V a u h i j k hij hik hjk]
  have hb : min (u j - a j) (u i + u j - finrank K V) ≤
      (u i - a i) + (u j - a j) := by omega
  rw [Nat.cast_sub hb, Nat.cast_add]


omit [FiniteDimensional K F] in
/-- A triple join implies the pair-intersection spanning identity used in
`RankConditions`; this is the modular-lattice step in the paper. -/
theorem pair_intersections_span_of_join (A B C V : Submodule K F)
    (hA : A ≤ V) (hjoin : (A ⊓ B) ⊔ C = V) :
    (A ⊓ B) ⊔ (A ⊓ C) = A := by
  have hm := sup_inf_assoc_of_le C (inf_le_left : A ⊓ B ≤ A)
  rw [hjoin, inf_eq_right.mpr hA] at hm
  simpa only [inf_comm C A] using hm.symm

/-- The displayed dimension-only maximum formula for every first-family
entry, derived from subspace ranks rather than postulated as a profile. -/
theorem firstEntry_max (T : Task K F) (V : Submodule K F) (a u : Three → ℕ)
    (h : RankConditions T V a u) (i j k : Three)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    firstEntry T i j k =
      ((max (u i - a i) (finrank K V - a i - a j) : ℕ) : ℝ) := by
  have hi : a i ≤ u i := by
    simpa only [h.side_dimension, h.signal_dimension] using
      Submodule.finrank_mono (T.side_le_signal i)
  have hj : a j ≤ u j := by
    simpa only [h.side_dimension, h.signal_dimension] using
      Submodule.finrank_mono (T.side_le_signal j)
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (T.U i) (T.U j)
  rw [h.pair_span i j hij, h.signal_dimension, h.signal_dimension] at hd
  rw [firstEntry_nat_formula T V a u h i j k hij hik hjk]
  congr 1
  omega

/-- Exact arithmetic of the six full-task entries for every listed family. -/
theorem full_first_arithmetic (g : Family) (n : ℕ) (hn : 1 ≤ n) (r : Fin 6) :
    let i := (firstOrder r).1
    let j := (firstOrder r).2.1
    (fullSignal g n i - fullSide g n i) + (fullSignal g n j - fullSide g n j) -
      min (fullSignal g n j - fullSide g n j)
        (fullSignal g n i + fullSignal g n j - fullAmbient g n) = fullFirst g n r := by
  cases g <;> fin_cases r <;>
    simp [firstOrder, fullSignal, fullSide, fullAmbient, fullFirst] <;> omega

/-- Exact arithmetic after the geometric kernel dimension drops. -/
theorem induced_first_arithmetic (g : Family) (n : ℕ) (hn : 1 ≤ n) (r : Fin 6) :
    let i := (firstOrder r).1
    let j := (firstOrder r).2.1
    (inducedSignal g n i - inducedSide g n i) + (inducedSignal g n j - inducedSide g n j) -
      min (inducedSignal g n j - inducedSide g n j)
        (inducedSignal g n i + inducedSignal g n j - (fullAmbient g n - codimension g)) =
      fullFirst g n r + firstIncrement g r := by
  cases g <;> fin_cases r <;>
    simp [firstOrder, inducedSignal, inducedSide, fullSignal, fullSide,
      fullAmbient, sideDrop, codimension, fullFirst, firstIncrement] <;> omega

/-- The full and induced triple/demand differences give the same nine
second-family entries. The equality with an added term also certifies that
none of the natural subtractions in the formula is spuriously truncated. -/
theorem second_arithmetic (g : Family) (n : ℕ) (hn : 1 ≤ n) :
    ((fullSignal g n 0 - fullSide g n 0) + (fullSignal g n 1 - fullSide g n 1) +
      (fullSignal g n 2 - fullSide g n 2) = doubledSecond g n +
      (fullSignal g n 0 + fullSignal g n 1 + fullSignal g n 2 - 2*fullAmbient g n)) ∧
    ((inducedSignal g n 0 - inducedSide g n 0) + (inducedSignal g n 1 - inducedSide g n 1) +
      (inducedSignal g n 2 - inducedSide g n 2) = doubledSecond g n +
      (inducedSignal g n 0 + inducedSignal g n 1 + inducedSignal g n 2 -
        2*(fullAmbient g n - codimension g))) := by
  cases g <;> simp [fullSignal, fullSide, fullAmbient, doubledSecond,
    inducedSignal, inducedSide, sideDrop, codimension] <;> omega

/-- All six actual full-task first entries, not an abstract profile surrogate. -/
theorem full_first_entries (T : Task K F) (V : Submodule K F)
    (g : Family) (n : ℕ) (hn : 1 ≤ n)
    (hd : finrank K V = fullAmbient g n)
    (h : RankConditions T V (fullSide g n) (fullSignal g n)) (r : Fin 6) :
    entry T (.inl r) = (fullFirst g n r : ℝ) := by
  change firstEntry T (firstOrder r).1 (firstOrder r).2.1 (firstOrder r).2.2 = _
  rw [firstEntry_nat_formula T V _ _ h _ _ _
    (by fin_cases r <;> decide) (by fin_cases r <;> decide) (by fin_cases r <;> decide), hd]
  exact congrArg (fun k : ℕ => (k : ℝ)) (full_first_arithmetic g n hn r)

/-- All six actual induced-task first entries and their prescribed increments. -/
theorem induced_first_entries (T : Task K F) (V : Submodule K F)
    (g : Family) (n : ℕ) (hn : 1 ≤ n)
    (hd : finrank K V = fullAmbient g n - codimension g)
    (h : RankConditions T V (inducedSide g n) (inducedSignal g n)) (r : Fin 6) :
    entry T (.inl r) = (fullFirst g n r : ℝ) + (firstIncrement g r : ℝ) := by
  change firstEntry T (firstOrder r).1 (firstOrder r).2.1 (firstOrder r).2.2 = _
  rw [firstEntry_nat_formula T V _ _ h _ _ _
    (by fin_cases r <;> decide) (by fin_cases r <;> decide) (by fin_cases r <;> decide), hd,
    show ((fullFirst g n r : ℝ) + (firstIncrement g r : ℝ)) =
      ((fullFirst g n r + firstIncrement g r : ℕ) : ℝ) by simp]
  exact congrArg (fun k : ℕ => (k : ℝ)) (induced_first_arithmetic g n hn r)

/-- All nine actual full-task doubled second entries. -/
theorem full_second_entries (T : Task K F) (V : Submodule K F)
    (g : Family) (n : ℕ) (hn : 1 ≤ n)
    (hd : finrank K V = fullAmbient g n)
    (h : RankConditions T V (fullSide g n) (fullSignal g n)) (i ell : Three) :
    2 * entry T (.inr (i,ell)) = (doubledSecond g n : ℝ) := by
  change 2 * secondEntry T i (i+1) (i+2) ell = _
  rw [secondEntry_formula T V _ _ h _ _ _ _
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide), hd]
  have ha := congrArg (fun k : ℕ => (k : ℝ)) (second_arithmetic g n hn).1
  push_cast at ha
  linarith

/-- All nine actual induced-task doubled second entries. -/
theorem induced_second_entries (T : Task K F) (V : Submodule K F)
    (g : Family) (n : ℕ) (hn : 1 ≤ n)
    (hd : finrank K V = fullAmbient g n - codimension g)
    (h : RankConditions T V (inducedSide g n) (inducedSignal g n)) (i ell : Three) :
    2 * entry T (.inr (i,ell)) = (doubledSecond g n : ℝ) := by
  change 2 * secondEntry T i (i+1) (i+2) ell = _
  rw [secondEntry_formula T V _ _ h _ _ _ _
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide), hd]
  have ha := congrArg (fun k : ℕ => (k : ℝ)) (second_arithmetic g n hn).2
  push_cast at ha
  linarith

end UploadBroadcast.NonzeroDefectProfile
