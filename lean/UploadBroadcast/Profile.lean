import UploadBroadcast.Model
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The fifteen actual LCBC conditional-rank entries

The rank maximum here is not defined to be the operational broadcast optimum.
The operational identification is proved separately in GeneralBroadcastOptimum.lean.
-/
namespace UploadBroadcast.Profile
open Module
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

abbrev Index := Fin 6 ⊕ (Three × Three)

def firstOrder : Fin 6 → Three × Three × Three :=
  ![(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1),(2,1,0)]

noncomputable def totalDemand (T : Task K F) : ℕ :=
  ∑ i, (finrank K (T.U i) - finrank K (T.A i))

noncomputable def firstEntry (T : Task K F) (i j k : Three) : ℝ :=
  (totalDemand T : ℝ) - condRank (T.U i ⊓ T.U j) (T.A j) -
    condRank (T.U k ⊓ (T.U i ⊔ T.U j)) (T.A k)

noncomputable def secondEntry (T : Task K F) (i j k ell : Three) : ℝ :=
  (totalDemand T : ℝ) -
    ((condRank (T.U 0 ⊓ T.U 1 ⊓ T.U 2) (T.A ell) : ℝ) +
      condRank ((T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)) (T.A i) +
      condRank (T.U j ⊓ (T.U i ⊔ T.U k)) (T.A j) +
      condRank (T.U k ⊓ (T.U i ⊔ T.U j)) (T.A k)) / 2

noncomputable def entry (T : Task K F) : Index → ℝ
  | .inl r => firstEntry T (firstOrder r).1 (firstOrder r).2.1 (firstOrder r).2.2
  | .inr (i,ell) => secondEntry T i (i+1) (i+2) ell

/-- The finite maximum of the fifteen rank entries, before any operational
capacity theorem is imported. -/
noncomputable def rankBound (T : Task K F) : ℝ :=
  Finset.univ.sup' (by simp) (entry T)

/-- A real number whose double is an integer. -/
def HalfInteger (x : ℝ) : Prop := ∃ z : ℤ, x = (z:ℝ)/2

theorem profile_has_fifteen_entries : Fintype.card Index = 15 := by
  simp [Index, Three]

theorem firstEntry_integral (T : Task K F) (i j k : Three) :
    ∃ z : ℤ, firstEntry T i j k = z := by
  refine ⟨(totalDemand T : ℤ) - condRank (T.U i ⊓ T.U j) (T.A j) -
    condRank (T.U k ⊓ (T.U i ⊔ T.U j)) (T.A k), ?_⟩
  simp [firstEntry]

theorem firstEntry_halfInteger (T : Task K F) (i j k : Three) :
    HalfInteger (firstEntry T i j k) := by
  obtain ⟨z,hz⟩ := firstEntry_integral T i j k
  refine ⟨2*z, ?_⟩
  rw [hz]
  push_cast
  ring

theorem secondEntry_halfInteger (T : Task K F) (i j k ell : Three) :
    HalfInteger (secondEntry T i j k ell) := by
  refine ⟨2*(totalDemand T : ℤ) -
    ((condRank (T.U 0 ⊓ T.U 1 ⊓ T.U 2) (T.A ell) : ℤ) +
      condRank ((T.U i ⊓ T.U j) ⊔ (T.U i ⊓ T.U k)) (T.A i) +
      condRank (T.U j ⊓ (T.U i ⊔ T.U k)) (T.A j) +
      condRank (T.U k ⊓ (T.U i ⊔ T.U j)) (T.A k)), ?_⟩
  simp only [secondEntry, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
    Int.cast_add, Int.cast_natCast]
  ring

theorem entry_halfInteger (T : Task K F) (r : Index) : HalfInteger (entry T r) := by
  cases r with
  | inl r => exact firstEntry_halfInteger T _ _ _
  | inr r => exact secondEntry_halfInteger T _ _ _ _

/-- The maximum is still a half-integer; this alone is not a proof about
operational D*, absent the LCBC identification theorem. -/
theorem rankBound_halfInteger (T : Task K F) : HalfInteger (rankBound T) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    (by simp : (Finset.univ : Finset Index).Nonempty) (entry T)
  change HalfInteger (Finset.univ.sup' _ (entry T))
  rw [hi]
  exact entry_halfInteger T i


section DirectSum
variable {G : Type*} [AddCommGroup G] [Module K G] [FiniteDimensional K G]

/-- The submodule product has the expected product of vector spaces. -/
def submoduleProdEquiv (A : Submodule K F) (B : Submodule K G) :
    A.prod B ≃ₗ[K] A × B where
  toFun x := (⟨x.1.1,x.2.1⟩, ⟨x.1.2,x.2.2⟩)
  invFun x := ⟨(x.1.1,x.2.1), x.1.2,x.2.2⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

theorem finrank_submodule_prod (A : Submodule K F) (B : Submodule K G) :
    finrank K (A.prod B) = finrank K A + finrank K B := by
  rw [(submoduleProdEquiv A B).finrank_eq, Module.finrank_prod]

theorem condRank_prod (C A : Submodule K F) (D B : Submodule K G) :
    condRank (C.prod D) (A.prod B) = condRank C A + condRank D B := by
  unfold condRank
  rw [Submodule.prod_sup_prod]
  simp only [finrank_submodule_prod]
  have hA := Submodule.finrank_mono (show A ≤ A ⊔ C from le_sup_left)
  have hB := Submodule.finrank_mono (show B ≤ B ⊔ D from le_sup_left)
  omega

theorem three_iSup {α : Type*} [CompleteLattice α] (a : Three → α) :
    (⨆ i, a i) = (a 0 ⊔ a 1) ⊔ a 2 := by
  apply le_antisymm
  · apply iSup_le
    intro i
    fin_cases i
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right
  · exact sup_le (sup_le (le_iSup a 0) (le_iSup a 1)) (le_iSup a 2)

/-- Task direct sum, represented on a binary product coefficient space. -/
def directSum (T : Task K F) (S : Task K G) : Task K (F × G) where
  A i := (T.A i).prod (S.A i)
  U i := (T.U i).prod (S.U i)
  side_le_signal i := Submodule.prod_mono (T.side_le_signal i) (S.side_le_signal i)
  feasible i := by
    have h : (⨆ j, T.A j).prod (⨆ j, S.A j) = ⨆ j, (T.A j).prod (S.A j) := by
      simp only [three_iSup, Submodule.prod_sup_prod]
    exact (Submodule.prod_mono (T.feasible i) (S.feasible i)).trans (le_of_eq h)

theorem totalDemand_directSum (T : Task K F) (S : Task K G) :
    totalDemand (directSum T S) = totalDemand T + totalDemand S := by
  unfold totalDemand
  simp only [directSum, finrank_submodule_prod]
  have h (i : Three) :
      (finrank K (T.U i) + finrank K (S.U i) -
        (finrank K (T.A i) + finrank K (S.A i))) =
      (finrank K (T.U i) - finrank K (T.A i)) +
        (finrank K (S.U i) - finrank K (S.A i)) := by
    have hT := Submodule.finrank_mono (T.side_le_signal i)
    have hS := Submodule.finrank_mono (S.side_le_signal i)
    omega
  simp_rw [h]
  exact Finset.sum_add_distrib

theorem firstEntry_directSum (T : Task K F) (S : Task K G) (i j k : Three) :
    firstEntry (directSum T S) i j k = firstEntry T i j k + firstEntry S i j k := by
  simp only [firstEntry]
  rw [totalDemand_directSum]
  simp only [directSum,
    Submodule.prod_inf_prod, Submodule.prod_sup_prod, condRank_prod, Nat.cast_add]
  ring

theorem secondEntry_directSum (T : Task K F) (S : Task K G) (i j k ell : Three) :
    secondEntry (directSum T S) i j k ell =
      secondEntry T i j k ell + secondEntry S i j k ell := by
  simp only [secondEntry]
  rw [totalDemand_directSum]
  simp only [directSum,
    Submodule.prod_inf_prod, Submodule.prod_sup_prod, condRank_prod, Nat.cast_add]
  ring

/-- Entrywise profile additivity, rather than additivity of the maxima. -/
theorem entry_directSum (T : Task K F) (S : Task K G) (r : Index) :
    entry (directSum T S) r = entry T r + entry S r := by
  cases r with
  | inl r => exact firstEntry_directSum T S _ _ _
  | inr r => exact secondEntry_directSum T S _ _ _ _

theorem entry_le_rankBound (T : Task K F) (r : Index) : entry T r ≤ rankBound T := by
  exact Finset.le_sup' (entry T) (Finset.mem_univ r)

/-- Direct-sum broadcast rank maxima are subadditive, not generally additive. -/
theorem rankBound_directSum_le (T : Task K F) (S : Task K G) :
    rankBound (directSum T S) ≤ rankBound T + rankBound S := by
  apply Finset.sup'_le
  intro r _
  rw [entry_directSum]
  exact add_le_add (entry_le_rankBound T r) (entry_le_rankBound S r)

/-- Two identical instances do scale the rank maximum exactly. -/
theorem rankBound_double (T : Task K F) : rankBound (directSum T T) = 2 * rankBound T := by
  apply le_antisymm
  · simpa only [two_mul] using rankBound_directSum_le T T
  · obtain ⟨r, _, hr⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
      (by simp : (Finset.univ : Finset Index).Nonempty) (entry T)
    have h := entry_le_rankBound (directSum T T) r
    rw [entry_directSum] at h
    change rankBound T = entry T r at hr
    rw [hr]
    simpa only [two_mul] using h

end DirectSum

end UploadBroadcast.Profile
