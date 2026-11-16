import UploadBroadcast.EdgeProfile
import UploadBroadcast.ResonantProfile
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Independent demand cycles supplied by orientation deficits

Actual independent vectors, with the physical directed-edge flags, are
selected inside the maximal edge blocks. Their total span is split from the
original six-subspace task. The profile inequalities then give the number
of such cycles available in the resonant complement.
-/
namespace UploadBroadcast.EdgeDeficits
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open Module EdgeExtraction
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Cyclic rotation of user labels, followed by an arbitrary relabeling.
The two choices of orientation are both covered by `p`. -/
def cyclicPerm (p : Equiv.Perm Three) (a : Three) : Equiv.Perm Three :=
  (Equiv.addLeft a).trans p

/-- The three physical directed edges in a selected orientation. -/
def cycleEdge (p : Equiv.Perm Three) (a : Three) : Edge :=
  ⟨(cyclicPerm p a 0, cyclicPerm p a 1, cyclicPerm p a 2),
    (cyclicPerm p a).injective.ne (by decide),
    (cyclicPerm p a).injective.ne (by decide),
    (cyclicPerm p a).injective.ne (by decide)⟩

theorem cycleEdge_injective (p : Equiv.Perm Three) : Function.Injective (cycleEdge p) := by
  intro a b h
  have hh := congrArg (fun e : Edge => e.val.1) h
  exact p.injective (by simpa [cycleEdge, cyclicPerm] using hh)

/-- Available whole independent cycles in the chosen orientation. -/
noncomputable def cycleMultiplicity (T : Task K V) (p : Equiv.Perm Three) : ℕ :=
  min (multiplicity T (p 0) (p 1) (p 2))
    (min (multiplicity T (p 1) (p 2) (p 0)) (multiplicity T (p 2) (p 0) (p 1)))

theorem cycleMultiplicity_le (T : Task K V) (p : Equiv.Perm Three) (a : Three) :
    cycleMultiplicity T p ≤ multiplicity T
      (cyclicPerm p a 0) (cyclicPerm p a 1) (cyclicPerm p a 2) := by
  fin_cases a
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- A concrete bundle of independent cycles. Every row consists of `r`
physical edge copies, and the entire bundle is a simultaneous task summand. -/
theorem exists_cycle_bundle (T : Task K V) (p : Equiv.Perm Three) (r : ℕ)
    (hr : r ≤ cycleMultiplicity T p) :
    ∃ (v : Three → Fin r → V) (Q : Submodule K V),
      LinearIndependent K (fun x : (a : Three) × Fin r => v x.1 x.2) ∧
      (∀ a, EdgeBlock T (cyclicPerm p a 0) (cyclicPerm p a 1) (cyclicPerm p a 2)
          (Submodule.span K (Set.range (v a))) ∧
        finrank K ↥(Submodule.span K (Set.range (v a))) = r) ∧
      TaskDecomposition.Split (configuration T).spaces ⊤ Q
        (⨆ a, Submodule.span K (Set.range (v a))) := by
  classical
  have hdim (a : Three) : r ≤ finrank K (edgeExtraction T (cycleEdge p a)).W := by
    rw [(edgeExtraction T (cycleEdge p a)).dimension]
    exact hr.trans (cycleMultiplicity_le T p a)
  choose w hw using fun a => exists_linearIndependent_of_le_finrank (R := K) (hdim a)
  let v : Three → Fin r → V := fun a t => w a t
  let P : Three → Submodule K V := fun a => Submodule.span K (Set.range (v a))
  have hP (a : Three) : P a ≤ (edgeExtraction T (cycleEdge p a)).W := by
    apply Submodule.span_le.mpr
    rintro x ⟨t,rfl⟩
    exact (w a t).property
  have hv (a : Three) : LinearIndependent K (v a) := by
    exact (hw a).map' (edgeExtraction T (cycleEdge p a)).W.subtype
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hind : iSupIndep P :=
    ((edge_blocks_independent T).comp (cycleEdge_injective p)).mono hP
  have hglobal : LinearIndependent K (fun x : (a : Three) × Fin r => v x.1 x.2) := by
    apply linearIndependent_iUnion_finite hv
    intro a s _ has
    exact hind.disjoint_biSup has
  let PP : Edge → Submodule K V := fun e => ⨆ a, ⨆ (_ : cycleEdge p a = e), P a
  have hPP (e : Edge) : PP e ≤ (edgeExtraction T e).W := by
    apply iSup_le
    intro a
    apply iSup_le
    intro ha
    rw [← ha]
    exact hP a
  have htotal : (⨆ e, PP e) = ⨆ a, P a := by
    apply le_antisymm
    · apply iSup_le
      intro e
      exact iSup_le fun a => iSup_le fun _ => le_iSup P a
    · apply iSup_le
      intro a
      exact (show P a ≤ PP (cycleEdge p a) from
        le_iSup_of_le a (le_iSup_of_le (Eq.refl (cycleEdge p a)) le_rfl)).trans
        (le_iSup PP (cycleEdge p a))
  obtain ⟨_, Q, hQ⟩ := simultaneous_subblocks T PP hPP
  rw [htotal] at hQ
  refine ⟨v, Q, hglobal, ?_, hQ⟩
  intro a
  have hb := (edgeExtraction T (cycleEdge p a)).block
  refine ⟨⟨(hP a).trans hb.source, (hP a).trans hb.target,
    hb.third_zero.mono_left (hP a), hb.target_side_zero.mono_left (hP a)⟩, ?_⟩
  simpa using finrank_span_eq_card (hv a)

/-- The extracted bundle has exactly three independent source coordinates
per cycle, with no hidden common coordinate between the edges. -/
theorem cycle_bundle_finrank {r : ℕ} (v : Three → Fin r → V)
    (hv : LinearIndependent K (fun x : (a : Three) × Fin r => v x.1 x.2)) :
    finrank K ↥(⨆ a, Submodule.span K (Set.range (v a))) = 3*r := by
  have hs : Submodule.span K (Set.range (fun x : (a : Three) × Fin r => v x.1 x.2)) =
      ⨆ a, Submodule.span K (Set.range (v a)) := by
    rw [Set.range_sigma_eq_iUnion_range, Submodule.span_iUnion]
  rw [← hs, finrank_span_eq_card hv]
  simp [Fintype.card_sigma]

/-- Thus the exact minimum multiplicity is realized by independent cycles,
not merely by three numerical lower bounds. -/
theorem maximal_cycle_bundle (T : Task K V) (p : Equiv.Perm Three) :
    ∃ (v : Three → Fin (cycleMultiplicity T p) → V) (Q : Submodule K V),
      LinearIndependent K (fun x : (a : Three) × Fin (cycleMultiplicity T p) => v x.1 x.2) ∧
      (∀ a, EdgeBlock T (cyclicPerm p a 0) (cyclicPerm p a 1) (cyclicPerm p a 2)
          (Submodule.span K (Set.range (v a))) ∧
        finrank K ↥(Submodule.span K (Set.range (v a))) = cycleMultiplicity T p) ∧
      TaskDecomposition.Split (configuration T).spaces ⊤ Q
        (⨆ a, Submodule.span K (Set.range (v a))) :=
  exists_cycle_bundle T p _ le_rfl

/-- Every permutation occurs in the actual six first-family entries. -/
theorem firstOrder_covers (i j k : Three) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ r : Fin 6, Profile.firstOrder r = (i,j,k) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
  all_goals first
    | exact ⟨0,rfl⟩
    | exact ⟨1,rfl⟩
    | exact ⟨2,rfl⟩
    | exact ⟨3,rfl⟩
    | exact ⟨4,rfl⟩
    | exact ⟨5,rfl⟩

theorem secondEntry_swap (T : Task K V) (i j k l : Three) :
    Profile.secondEntry T i j k l = Profile.secondEntry T i k j l := by
  unfold Profile.secondEntry
  rw [sup_comm (T.U i ⊓ T.U j) (T.U i ⊓ T.U k)]
  ring

theorem secondEntry_as_entry (T : Task K V) (i j k l : Three)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Profile.secondEntry T i j k l = Profile.entry T (.inr (i,l)) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
  all_goals first
    | rfl
    | exact secondEntry_swap T _ _ _ _

theorem first_le_budget (T : Task K V) (p : Equiv.Perm Three) (D : ℝ)
    (hD : Profile.rankBound T ≤ D) : Profile.firstEntry T (p 0) (p 1) (p 2) ≤ D := by
  obtain ⟨r,hr⟩ := firstOrder_covers (p 0) (p 1) (p 2)
    (p.injective.ne (by decide)) (p.injective.ne (by decide)) (p.injective.ne (by decide))
  have hh := (Profile.entry_le_rankBound T (.inl r)).trans hD
  simpa [Profile.entry, hr] using hh

theorem second_le_budget (T : Task K V) (p : Equiv.Perm Three) (l : Three) (D : ℝ)
    (hD : Profile.rankBound T ≤ D) : Profile.secondEntry T (p 0) (p 1) (p 2) l ≤ D := by
  rw [secondEntry_as_entry T _ _ _ _ (p.injective.ne (by decide))
    (p.injective.ne (by decide)) (p.injective.ne (by decide))]
  exact (Profile.entry_le_rankBound T _).trans hD

/-- The source price for the edge from the third user to the second. -/
noncomputable def price (T : Task K V) (p : Equiv.Perm Three) : ℝ :=
  Profile.firstEntry T (p 0) (p 1) (p 2) +
    Profile.firstEntry T (p 1) (p 2) (p 0) -
    2 * Profile.secondEntry T (p 1) (p 0) (p 2) (p 2)

/-- Sum of the three first-family slacks in one orientation. -/
noncomputable def orientationSlack (T : Task K V) (p : Equiv.Perm Three) (D : ℝ) : ℝ :=
  (D - Profile.firstEntry T (p 0) (p 1) (p 2)) +
  (D - Profile.firstEntry T (p 1) (p 2) (p 0)) +
  (D - Profile.firstEntry T (p 2) (p 0) (p 1))

theorem orientationSlack_cyclic (T : Task K V) (p : Equiv.Perm Three) (D : ℝ) (a : Three) :
    orientationSlack T (cyclicPerm p a) D = orientationSlack T p D := by
  fin_cases a
  · rfl
  · change (D - Profile.firstEntry T (p 1) (p 2) (p 0)) +
      (D - Profile.firstEntry T (p 2) (p 0) (p 1)) +
      (D - Profile.firstEntry T (p 0) (p 1) (p 2)) = _
    unfold orientationSlack
    ring
  · change (D - Profile.firstEntry T (p 2) (p 0) (p 1)) +
      (D - Profile.firstEntry T (p 0) (p 1) (p 2)) +
      (D - Profile.firstEntry T (p 1) (p 2) (p 0)) = _
    unfold orientationSlack
    ring

/-- A budget for the actual fifteen-entry profile bounds every edge price
from below by minus its orientation slack. -/
theorem price_lower_bound (T : Task K V) (p : Equiv.Perm Three) (D : ℝ)
    (hD : Profile.rankBound T ≤ D) : -orientationSlack T p D ≤ price T p := by
  have hF := first_le_budget T (cyclicPerm p 2) D hD
  have hQ := (Profile.entry_le_rankBound T (.inr (p 1,p 2))).trans hD
  rw [← secondEntry_as_entry T (p 1) (p 0) (p 2) (p 2)
    (p.injective.ne (by decide)) (p.injective.ne (by decide)) (p.injective.ne (by decide))] at hQ
  change Profile.firstEntry T (p 2) (p 0) (p 1) ≤ D at hF
  unfold orientationSlack price
  linarith

section DirectSum
variable {G : Type*} [AddCommGroup G] [Module K G] [FiniteDimensional K G]

/-- Exact physical edge multiplicity is additive on genuine task sums. -/
theorem multiplicity_directSum (T : Task K V) (S : Task K G) (i j k : Three) :
    multiplicity (Profile.directSum T S) i j k =
      multiplicity T i j k + multiplicity S i j k := by
  simp only [EdgeProfile.extractable_multiplicity, Profile.directSum,
    Submodule.prod_inf_prod, Submodule.prod_sup_prod, Profile.condRank_prod]

theorem price_directSum (T : Task K V) (S : Task K G) (p : Equiv.Perm Three) :
    price (Profile.directSum T S) p = price T p + price S p := by
  simp only [price, Profile.firstEntry_directSum, Profile.secondEntry_directSum]
  ring

end DirectSum

/-- The first-family profile of an actual resonant block at arbitrary labels. -/
theorem jordan_first (K : Type*) [Field K] (n : ℕ) (p : Equiv.Perm Three) :
    Profile.firstEntry (ResonantRelay.jordanTask K n) (p 0) (p 1) (p 2) = (n : ℝ) + 1 := by
  obtain ⟨r,hr⟩ := firstOrder_covers (p 0) (p 1) (p 2)
    (p.injective.ne (by decide)) (p.injective.ne (by decide)) (p.injective.ne (by decide))
  simpa [Profile.entry,hr] using ResonantRelay.jordan_full_firstProfile K n r

/-- The negative edge price is derived from the actual resonant flags. -/
theorem jordan_price (K : Type*) [Field K] (n : ℕ) (p : Equiv.Perm Three) :
    price (ResonantRelay.jordanTask K n) p = -((n : ℝ) + 1) := by
  have h1 := jordan_first K n p
  have h2 := jordan_first K n (cyclicPerm p 1)
  change Profile.firstEntry (ResonantRelay.jordanTask K n) (p 1) (p 2) (p 0) = (n : ℝ)+1 at h2
  have hQ := ResonantRelay.jordan_full_secondProfile K n (p 1) (p 2)
  rw [← secondEntry_as_entry (ResonantRelay.jordanTask K n) (p 1) (p 0) (p 2) (p 2)
    (p.injective.ne (by decide)) (p.injective.ne (by decide)) (p.injective.ne (by decide))] at hQ
  unfold price
  linarith

section ResonantSum
universe u
variable (K : Type u) [Field K]

/-- Actual ambient direct sum of arbitrary positive-length resonant blocks.
A list entry `n` denotes the source block `R_(n+1)`. -/
def ResonantAmbient : List ℕ → Type u
  | [] => Fin 0 → K
  | n::L => ResonantEndomorphisms.Ambient K (JordanResonance.V K n) × ResonantAmbient L

instance resonantAdd (L : List ℕ) : AddCommGroup (ResonantAmbient K L) := by
  induction L with
  | nil => exact inferInstanceAs (AddCommGroup (Fin 0 → K))
  | cons n L ih => exact inferInstanceAs (AddCommGroup (ResonantEndomorphisms.Ambient K (JordanResonance.V K n) × ResonantAmbient K L))

instance resonantModule (L : List ℕ) : Module K (ResonantAmbient K L) := by
  induction L with
  | nil => exact inferInstanceAs (Module K (Fin 0 → K))
  | cons n L ih => exact inferInstanceAs (Module K (ResonantEndomorphisms.Ambient K (JordanResonance.V K n) × ResonantAmbient K L))

instance resonantFinite (L : List ℕ) : FiniteDimensional K (ResonantAmbient K L) := by
  induction L with
  | nil => exact inferInstanceAs (FiniteDimensional K (Fin 0 → K))
  | cons n L ih => exact inferInstanceAs (FiniteDimensional K (ResonantEndomorphisms.Ambient K (JordanResonance.V K n) × ResonantAmbient K L))

/-- Actual six-subspace sum, so neither profile additivity nor the price
of its resonant part is a hypothesis of the deficit theorem. -/
def resonantTask : (L : List ℕ) → Task K (ResonantAmbient K L)
  | [] => ⟨fun _ => ⊥, fun _ => ⊥, fun _ => le_rfl, fun _ => bot_le⟩
  | n::L => Profile.directSum (ResonantRelay.jordanTask K n) (resonantTask L)

/-- Weighted block count appearing in the exact edge-price sum. -/
def resonantWeight (L : List ℕ) : ℕ := (L.map (fun n => n+1)).sum

theorem resonant_count_le_weight (L : List ℕ) : L.length ≤ resonantWeight L := by
  induction L with
  | nil => simp [resonantWeight]
  | cons n L ih => simp only [resonantWeight, List.map_cons, List.sum_cons, List.length_cons] at *; omega

theorem resonantTask_price (L : List ℕ) (p : Equiv.Perm Three) :
    price (resonantTask K L) p = -(resonantWeight L : ℝ) := by
  induction L with
  | nil =>
    letI : Subsingleton (ResonantAmbient K []) := inferInstanceAs (Subsingleton (Fin 0 → K))
    have hz (P : Submodule K (ResonantAmbient K [])) : finrank K P = 0 :=
      Module.finrank_zero_of_subsingleton
    simp [price, Profile.firstEntry, Profile.secondEntry,
      Profile.totalDemand, condRank, hz, resonantWeight]
  | cons n L ih =>
    change price (Profile.directSum (ResonantRelay.jordanTask K n) (resonantTask K L)) p = _
    rw [price_directSum, jordan_price, ih]
    simp only [resonantWeight, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
    ring

end ResonantSum

/-- Source equation `total-edge-bound`, with the price of every actual
resonant block computed and its direct-sum additivity proved. -/
theorem complement_edge_deficit (T : Task K V) (L : List ℕ)
    (p : Equiv.Perm Three) (D : ℝ)
    (hD : Profile.rankBound (Profile.directSum (resonantTask K L) T) ≤ D) :
    max 0 ((L.length : ℝ) -
      orientationSlack (Profile.directSum (resonantTask K L) T) p D) ≤
      (multiplicity T (p 0) (p 1) (p 2) : ℝ) := by
  have hlo := price_lower_bound (Profile.directSum (resonantTask K L) T) p D hD
  rw [price_directSum, resonantTask_price] at hlo
  have hhi := EdgeProfile.edge_price_le_extractable T p
  change price T p ≤ (multiplicity T (p 0) (p 1) (p 2) : ℝ) at hhi
  have hc : (L.length : ℝ) ≤ resonantWeight L := by
    exact_mod_cast resonant_count_le_weight L
  exact max_le (Nat.cast_nonneg _) (by linarith)

/-- All three edges simultaneously meet the same orientation deficit. -/
theorem complement_cycle_deficit (T : Task K V) (L : List ℕ)
    (p : Equiv.Perm Three) (D : ℝ)
    (hD : Profile.rankBound (Profile.directSum (resonantTask K L) T) ≤ D) :
    max 0 ((L.length : ℝ) -
      orientationSlack (Profile.directSum (resonantTask K L) T) p D) ≤
      (cycleMultiplicity T p : ℝ) := by
  have hh (a : Three) := complement_edge_deficit T L (cyclicPerm p a) D hD
  simp only [orientationSlack_cyclic] at hh
  rw [cycleMultiplicity, Nat.cast_min, Nat.cast_min]
  exact le_min (hh 0) (le_min (hh 1) (hh 2))

/-- Every orientation deficit is covered by a physically extracted bundle
of independent demand cycles wholly inside the resonant complement. -/
theorem demand_cycles_from_orientation_deficit (T : Task K V) (L : List ℕ)
    (p : Equiv.Perm Three) (D : ℝ)
    (hD : Profile.rankBound (Profile.directSum (resonantTask K L) T) ≤ D) :
    ∃ (r : ℕ) (v : Three → Fin r → V) (Q : Submodule K V),
      max 0 ((L.length : ℝ) -
        orientationSlack (Profile.directSum (resonantTask K L) T) p D) ≤ (r : ℝ) ∧
      LinearIndependent K (fun x : (a : Three) × Fin r => v x.1 x.2) ∧
      (∀ a, EdgeBlock T (cyclicPerm p a 0) (cyclicPerm p a 1) (cyclicPerm p a 2)
          (Submodule.span K (Set.range (v a))) ∧
        finrank K ↥(Submodule.span K (Set.range (v a))) = r) ∧
      TaskDecomposition.Split (configuration T).spaces ⊤ Q
        (⨆ a, Submodule.span K (Set.range (v a))) := by
  obtain ⟨v,Q,hv,hblock,hQ⟩ := maximal_cycle_bundle T p
  exact ⟨cycleMultiplicity T p, v, Q, complement_cycle_deficit T L p D hD, hv,hblock,hQ⟩

section Transport
variable {G : Type*} [AddCommGroup G] [Module K G] [FiniteDimensional K G]

theorem rankBound_map (e : V ≃ₗ[K] G) (T : Task K V) :
    Profile.rankBound (Profile.mapTask e T) = Profile.rankBound T := by
  unfold Profile.rankBound
  simp only [Profile.entry_mapTask]

theorem orientationSlack_map (e : V ≃ₗ[K] G) (T : Task K V)
    (p : Equiv.Perm Three) (D : ℝ) :
    orientationSlack (Profile.mapTask e T) p D = orientationSlack T p D := by
  simp only [orientationSlack, Profile.firstEntry_mapTask]

/-- Coordinate-free form: the full task may be presented by any linear
coordinate equivalence from its resonant sum and its remaining task. -/
theorem demand_cycles_from_decomposition (T : Task K V) (L : List ℕ)
    (M : Task K G) (e : (ResonantAmbient K L × V) ≃ₗ[K] G)
    (hM : Profile.mapTask e (Profile.directSum (resonantTask K L) T) = M)
    (p : Equiv.Perm Three) (D : ℝ) (hD : Profile.rankBound M ≤ D) :
    ∃ (r : ℕ) (v : Three → Fin r → V) (Q : Submodule K V),
      max 0 ((L.length : ℝ) - orientationSlack M p D) ≤ (r : ℝ) ∧
      LinearIndependent K (fun x : (a : Three) × Fin r => v x.1 x.2) ∧
      (∀ a, EdgeBlock T (cyclicPerm p a 0) (cyclicPerm p a 1) (cyclicPerm p a 2)
          (Submodule.span K (Set.range (v a))) ∧
        finrank K ↥(Submodule.span K (Set.range (v a))) = r) ∧
      TaskDecomposition.Split (configuration T).spaces ⊤ Q
        (⨆ a, Submodule.span K (Set.range (v a))) := by
  subst M
  rw [rankBound_map] at hD
  rw [orientationSlack_map]
  exact demand_cycles_from_orientation_deficit T L p D hD

end Transport
end UploadBroadcast.EdgeDeficits
