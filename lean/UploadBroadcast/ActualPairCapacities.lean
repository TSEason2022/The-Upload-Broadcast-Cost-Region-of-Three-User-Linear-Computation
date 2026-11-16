import UploadBroadcast.EdgeProfile
import UploadBroadcast.FiniteRelayAssembly
import UploadBroadcast.BinaryMenuAllocation
import UploadBroadcast.ResonantFiniteAssembly
import UploadBroadcast.R2PermutedMenus

namespace UploadBroadcast.ActualPairCapacities
open Module Profile BinaryMenuAllocation
open scoped BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Conditional-rank submodularity in the actual coefficient lattice. -/
theorem condRank_submodular (X Y A : Submodule K V) :
    (condRank (X ⊔ Y) A : ℝ)+condRank (X ⊓ Y) A ≤
      (condRank X A : ℝ)+condRank Y A := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ X) (A ⊔ Y)
  have hm := Submodule.finrank_mono (show A ⊔ (X ⊓ Y) ≤ (A ⊔ X) ⊓ (A ⊔ Y) from
    sup_le (le_inf le_sup_left le_sup_left)
      (le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans le_sup_right)))
  have he : (A ⊔ X) ⊔ (A ⊔ Y) = A ⊔ (X ⊔ Y) := by simp [sup_assoc,sup_comm,sup_left_comm]
  rw [he] at h
  have hr : (finrank K ↥(A ⊔ (X ⊔ Y)) : ℝ)+finrank K ↥((A ⊔ X) ⊓ (A ⊔ Y))=
      finrank K ↥(A ⊔ X)+finrank K ↥(A ⊔ Y) := by exact_mod_cast h
  have hmr : (finrank K ↥(A ⊔ (X ⊓ Y)) : ℝ) ≤ finrank K ↥((A ⊔ X) ⊓ (A ⊔ Y)) := by exact_mod_cast hm
  simp only [condRank, Nat.cast_sub (Submodule.finrank_mono le_sup_left)]
  linarith only [hr,hmr]

/-- Opposite first-family entries are bounded by the matching doubled
second-family entry. The common triple is the literal original intersection. -/
theorem paired_first_le (T : Task K V) (i j k : Three)
    (htr : T.U 0 ⊓ T.U 1 ⊓ T.U 2 = T.U i ⊓ T.U j ⊓ T.U k) :
    firstEntry T i j k + firstEntry T k j i ≤ 2*secondEntry T j i k j := by
  have h := condRank_submodular (T.U i ⊓ T.U j) (T.U k ⊓ T.U j) (T.A j)
  have hi : (T.U i ⊓ T.U j) ⊓ (T.U k ⊓ T.U j)=T.U 0 ⊓ T.U 1 ⊓ T.U 2 := by rw [htr]; simp [inf_assoc,inf_comm,inf_left_comm]
  rw [hi] at h
  unfold firstEntry secondEntry
  rw [inf_comm (T.U j) (T.U i),inf_comm (T.U j) (T.U k)]
  rw [sup_comm (T.U j) (T.U k),sup_comm (T.U j) (T.U i)]
  linarith only [h]

def secondIndex : Fin 3 → Three × Three := ![(1,1),(2,2),(0,0)]
noncomputable def margin (T : Task K V) (p : Fin 3) : ℝ :=
  2*entry T (.inr (secondIndex p))-
    (entry T (.inl (pairLeft p))+entry T (.inl (pairRight p)))

/-- All three actual pair margins are nonnegative for every task, including
arbitrary profile-preserving zero-excess and omniscience remainders. -/
theorem margin_nonneg (T : Task K V) (p : Fin 3) : 0 ≤ margin T p := by
  have h₀ := paired_first_le T 2 1 0 (by simp [inf_assoc,inf_comm,inf_left_comm])
  have h₁ := paired_first_le T 0 2 1 (by simp [inf_assoc,inf_comm,inf_left_comm])
  have h₂ := paired_first_le T 1 0 2 (by simp [inf_assoc,inf_comm,inf_left_comm])
  fin_cases p <;>
    norm_num only [margin,entry,secondIndex,pairLeft,pairRight,firstOrder,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,Matrix.cons_val_succ,Matrix.head_cons,Fin.reduceAdd]
  · change 0 ≤ 2*secondEntry T 1 2 0 1-(firstEntry T 0 1 2+firstEntry T 2 1 0)
    linarith only [h₀]
  · change 0 ≤ 2*secondEntry T 2 0 1 2-(firstEntry T 0 2 1+firstEntry T 1 2 0)
    linarith only [h₁]
  · change 0 ≤ 2*secondEntry T 0 1 2 0-(firstEntry T 1 0 2+firstEntry T 2 0 1)
    linarith only [h₂]

/-- Omniscience contributes zero to each matching opposite-pair margin. -/
theorem omniscience_margin (T : Task K V) (hU : ∀ i, T.U i=⊤) (p : Fin 3) :
    margin T p=0 := by
  fin_cases p
  · change 2*secondEntry T 1 2 0 1-(firstEntry T 0 1 2+firstEntry T 2 1 0)=0
    simp only [firstEntry,secondEntry,hU,inf_top_eq,sup_top_eq]
    ring
  · change 2*secondEntry T 2 0 1 2-(firstEntry T 0 2 1+firstEntry T 1 2 0)=0
    simp only [firstEntry,secondEntry,hU,inf_top_eq,sup_top_eq]
    ring
  · change 2*secondEntry T 0 1 2 0-(firstEntry T 1 0 2+firstEntry T 2 0 1)=0
    simp only [firstEntry,secondEntry,hU,inf_top_eq,sup_top_eq]
    ring

/-- The six first entries have literal signed integer representatives. -/
noncomputable def firstInteger (T : Task K V) (r : Fin 6) : ℤ :=
  Classical.choose (firstEntry_integral T (firstOrder r).1
    (firstOrder r).2.1 (firstOrder r).2.2)

theorem firstInteger_cast (T : Task K V) (r : Fin 6) :
    (firstInteger T r : ℝ) = entry T (.inl r) :=
  (Classical.choose_spec (firstEntry_integral T (firstOrder r).1
    (firstOrder r).2.1 (firstOrder r).2.2)).symm

/-- Exact, rather than rounded, integer slack at an integer scalar target. -/
noncomputable def capacity (T : Task K V) (D : ℤ) (r : Fin 6) : ℤ :=
  D-firstInteger T r

theorem capacity_cast (T : Task K V) (D : ℤ) (r : Fin 6) :
    (capacity T D r : ℝ) = (D : ℝ)-entry T (.inl r) := by
  simp only [capacity,Int.cast_sub,firstInteger_cast]

theorem capacity_nonneg (T : Task K V) (D : ℤ)
    (hD : rankBound T ≤ (D : ℝ)) (r : Fin 6) : 0 ≤ capacity T D r := by
  have h := (entry_le_rankBound T (.inl r)).trans hD
  have hc : (0 : ℝ) ≤ (capacity T D r : ℝ) := by rw [capacity_cast]; linarith
  exact_mod_cast hc

/-- The actual second entry pays any charge proved below the matching
conditional-rank margin. No opposite-pair budget is assumed. -/
theorem charge_fits_capacity (T : Task K V) (D : ℤ)
    (hD : rankBound T ≤ (D : ℝ)) (q : Fin 3 → ℤ)
    (hq : ∀ p, (q p : ℝ) ≤ margin T p) (p : Fin 3) :
    q p ≤ capacity T D (pairLeft p)+capacity T D (pairRight p) := by
  have hb := (entry_le_rankBound T (.inr (secondIndex p))).trans hD
  have hm := hq p
  have hc : (q p : ℝ) ≤ (capacity T D (pairLeft p) : ℝ)+capacity T D (pairRight p) := by
    rw [capacity_cast,capacity_cast]
    unfold margin at hm
    linarith only [hm,hb]
  exact_mod_cast hc

section DirectSum
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem margin_directSum (T : Task K V) (R : Task K W) (p : Fin 3) :
    margin (Profile.directSum T R) p = margin T p+margin R p := by
  simp only [margin,Profile.entry_directSum]
  ring
end DirectSum

variable {I : Type*} [Fintype I] {F : I → Type*}
  [∀ t, AddCommGroup (F t)] [∀ t, Module K (F t)] [∀ t, FiniteDimensional K (F t)]

theorem margin_finite_task (T : (t : I) → Task K (F t)) (p : Fin 3) :
    margin (FiniteRelayAssembly.task T) p=∑ t, margin (T t) p := by
  simp only [margin,FiniteRelayAssembly.entry_task,Finset.sum_sub_distrib,
    Finset.sum_add_distrib,Finset.mul_sum]

/-- Summed component charge bounds turn the original fifteen-entry budget
into actual signed-integer opposite-pair capacities. -/
theorem charges_fit_original_budget (T : (t : I) → Task K (F t))
    (q : I → Fin 3 → ℤ) (hq : ∀ t p, (q t p : ℝ) ≤ margin (T t) p)
    (D : ℝ) (hD : rankBound (FiniteRelayAssembly.task T) ≤ D)
    (c : Fin 6 → ℤ) (hc : ∀ r, (c r : ℝ)=D-entry (FiniteRelayAssembly.task T) (.inl r)) :
    ∀ p, (∑ t, q t p) ≤ c (pairLeft p)+c (pairRight p) := by
  intro p
  have hq' : (∑ t, (q t p : ℝ)) ≤ margin (FiniteRelayAssembly.task T) p := by
    rw [margin_finite_task]
    exact Finset.sum_le_sum fun t _ => hq t p
  have hb := (entry_le_rankBound (FiniteRelayAssembly.task T) (.inr (secondIndex p))).trans hD
  have hL := hc (pairLeft p)
  have hR := hc (pairRight p)
  unfold margin at hq'
  have hh : (∑ t, (q t p : ℝ)) ≤ (c (pairLeft p) : ℝ)+c (pairRight p) := by
    linarith only [hq',hb,hL,hR]
  exact_mod_cast hh

/-- Each actual original resonant copy contributes at least one unit to
every opposite-pair capacity, regardless of its Jordan length. -/
theorem resonant_margin (n : ℕ) (p : Fin 3) :
    margin (ResonantRelay.jordanTask K n) p=(n : ℝ)+1 := by
  unfold margin
  obtain ⟨i,l⟩ := secondIndex p
  rw [ResonantRelay.jordan_full_secondProfile,ResonantRelay.jordan_full_firstProfile,
    ResonantRelay.jordan_full_firstProfile]
  ring

end UploadBroadcast.ActualPairCapacities
