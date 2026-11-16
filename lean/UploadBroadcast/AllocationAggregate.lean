import UploadBroadcast.Allocation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Tauto

/-! Exact numerical packing for the ten rows of Table 1.
Coordinates are reordered as (e1,e4,e5,e6,e2,e3), so opposite
pairs are (0,3), (1,4), (2,5). Ordinary rows are T1¹,T1²,T1³,
O¹,O²,O³,Z16,Z24,Z35. Repeated generators merely pad two-choice
menus to three choices and do not change the feasible selections. -/
namespace UploadBroadcast.Allocation
open scoped BigOperators
section Aggregate
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

def ordinaryMenu : Fin 9 → Fin 3 → Fin 6 → R :=
  ![![![0,0,1,0,0,0], ![0,0,0,0,0,1], ![0,0,1,0,0,0]],
    ![![0,0,0,1,0,0], ![1,0,0,0,0,0], ![0,0,0,1,0,0]],
    ![![0,1,0,0,0,0], ![0,0,0,0,1,0], ![0,1,0,0,0,0]],
    ![![1,0,0,0,0,0], ![0,0,0,0,1,0], ![0,1,0,1,0,0]],
    ![![0,1,0,0,0,0], ![0,0,0,0,0,1], ![0,0,1,0,1,0]],
    ![![0,0,0,1,0,0], ![0,0,1,0,0,0], ![1,0,0,0,0,1]],
    ![![1,0,0,0,0,0], ![0,0,0,1,0,0], ![1,0,0,0,0,0]],
    ![![0,0,0,0,1,0], ![0,1,0,0,0,0], ![0,0,0,0,1,0]],
    ![![0,0,0,0,0,1], ![0,0,1,0,0,0], ![0,0,0,0,0,1]]]

def ordinaryMargin : Fin 9 → Fin 3 → R :=
  ![![1,1,2], ![2,1,1], ![1,2,1], ![1,1,0], ![0,1,1], ![1,0,1], ![1,0,0], ![0,1,0], ![0,0,1]]

def consumption (t : Fin 9) (w : Fin 3 → R) (j : Fin 6) : R :=
  ∑ k, w k * ordinaryMenu t k j

theorem ordinary_menu_fits (t : Fin 9) (m : R) (c : Fin 6 → R)
    (hm : 0 ≤ m) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ i : Fin 3, m * ordinaryMargin t i ≤ c (Fin.castAdd 3 i) + c (Fin.natAdd 3 i)) :
    ∃ w : Fin 3 → R, (∀ k, 0 ≤ w k) ∧ (∑ k, w k)=m ∧
      ∀ j, consumption t w j ≤ c j := by
  have hc0 := hc 0
  have hc1 := hc 1
  have hc2 := hc 2
  have hc3 := hc 3
  have hc4 := hc 4
  have hc5 := hc 5
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  fin_cases t
  · change m * 1 ≤ c 0 + c 3 at hp0
    change m * 1 ≤ c 1 + c 4 at hp1
    change m * 2 ≤ c 2 + c 5 at hp2
    obtain ⟨x,y,hx,hy,hxc,hyc,he⟩ :=
      fill_two m (c 2) (c 5) hm hc2 hc5 (by linarith)
    refine ⟨![x,y,0], ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp <;> assumption
    · simpa [Fin.sum_univ_succ, add_assoc] using he
    · intro j
      fin_cases j <;> norm_num [consumption, ordinaryMenu, Fin.sum_univ_succ] <;> assumption
  · change m * 2 ≤ c 0 + c 3 at hp0
    change m * 1 ≤ c 1 + c 4 at hp1
    change m * 1 ≤ c 2 + c 5 at hp2
    obtain ⟨x,y,hx,hy,hxc,hyc,he⟩ :=
      fill_two m (c 3) (c 0) hm hc3 hc0 (by linarith)
    refine ⟨![x,y,0], ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp <;> assumption
    · simpa [Fin.sum_univ_succ, add_assoc] using he
    · intro j
      fin_cases j <;> norm_num [consumption, ordinaryMenu, Fin.sum_univ_succ] <;> assumption
  · change m * 1 ≤ c 0 + c 3 at hp0
    change m * 2 ≤ c 1 + c 4 at hp1
    change m * 1 ≤ c 2 + c 5 at hp2
    obtain ⟨x,y,hx,hy,hxc,hyc,he⟩ :=
      fill_two m (c 1) (c 4) hm hc1 hc4 (by linarith)
    refine ⟨![x,y,0], ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp <;> assumption
    · simpa [Fin.sum_univ_succ, add_assoc] using he
    · intro j
      fin_cases j <;> norm_num [consumption, ordinaryMenu, Fin.sum_univ_succ] <;> assumption
  · change m * 1 ≤ c 0 + c 3 at hp0
    change m * 1 ≤ c 1 + c 4 at hp1
    change m * 0 ≤ c 2 + c 5 at hp2
    obtain ⟨x,y,z,hx,hy,hz,hxc,hyc,hzd,hze,he⟩ :=
      o_menu_allocation m (c 0) (c 4) (c 1) (c 3) hm hc0 hc4 hc1 hc3 (by linarith) (by linarith)
    refine ⟨![x,y,z], ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp <;> assumption
    · simpa [Fin.sum_univ_succ, add_assoc] using he
    · intro j
      fin_cases j <;> norm_num [consumption, ordinaryMenu, Fin.sum_univ_succ] <;> assumption
  · change m * 0 ≤ c 0 + c 3 at hp0
    change m * 1 ≤ c 1 + c 4 at hp1
    change m * 1 ≤ c 2 + c 5 at hp2
    obtain ⟨x,y,z,hx,hy,hz,hxc,hyc,hzd,hze,he⟩ :=
      o_menu_allocation m (c 1) (c 5) (c 2) (c 4) hm hc1 hc5 hc2 hc4 (by linarith) (by linarith)
    refine ⟨![x,y,z], ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp <;> assumption
    · simpa [Fin.sum_univ_succ, add_assoc] using he
    · intro j
      fin_cases j <;> norm_num [consumption, ordinaryMenu, Fin.sum_univ_succ] <;> assumption
  · change m * 1 ≤ c 0 + c 3 at hp0
    change m * 0 ≤ c 1 + c 4 at hp1
    change m * 1 ≤ c 2 + c 5 at hp2
    obtain ⟨x,y,z,hx,hy,hz,hxc,hyc,hzd,hze,he⟩ :=
      o_menu_allocation m (c 3) (c 2) (c 5) (c 0) hm hc3 hc2 hc5 hc0 (by linarith) (by linarith)
    refine ⟨![x,y,z], ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp <;> assumption
    · simpa [Fin.sum_univ_succ, add_assoc] using he
    · intro j
      fin_cases j <;> norm_num [consumption, ordinaryMenu, Fin.sum_univ_succ] <;> assumption
  · change m * 1 ≤ c 0 + c 3 at hp0
    change m * 0 ≤ c 1 + c 4 at hp1
    change m * 0 ≤ c 2 + c 5 at hp2
    obtain ⟨x,y,hx,hy,hxc,hyc,he⟩ :=
      fill_two m (c 0) (c 3) hm hc0 hc3 (by linarith)
    refine ⟨![x,y,0], ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp <;> assumption
    · simpa [Fin.sum_univ_succ, add_assoc] using he
    · intro j
      fin_cases j <;> norm_num [consumption, ordinaryMenu, Fin.sum_univ_succ] <;> assumption
  · change m * 0 ≤ c 0 + c 3 at hp0
    change m * 1 ≤ c 1 + c 4 at hp1
    change m * 0 ≤ c 2 + c 5 at hp2
    obtain ⟨x,y,hx,hy,hxc,hyc,he⟩ :=
      fill_two m (c 4) (c 1) hm hc4 hc1 (by linarith)
    refine ⟨![x,y,0], ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp <;> assumption
    · simpa [Fin.sum_univ_succ, add_assoc] using he
    · intro j
      fin_cases j <;> norm_num [consumption, ordinaryMenu, Fin.sum_univ_succ] <;> assumption
  · change m * 0 ≤ c 0 + c 3 at hp0
    change m * 0 ≤ c 1 + c 4 at hp1
    change m * 1 ≤ c 2 + c 5 at hp2
    obtain ⟨x,y,hx,hy,hxc,hyc,he⟩ :=
      fill_two m (c 5) (c 2) hm hc5 hc2 (by linarith)
    refine ⟨![x,y,0], ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp <;> assumption
    · simpa [Fin.sum_univ_succ, add_assoc] using he
    · intro j
      fin_cases j <;> norm_num [consumption, ordinaryMenu, Fin.sum_univ_succ] <;> assumption

/-- All nine nonresonant rows can be packed simultaneously using their
listed pair-margin budgets. -/
theorem ordinary_aggregate (μ : Fin 9 → R) (c : Fin 6 → R)
    (hμ : ∀ t, 0 ≤ μ t) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ i : Fin 3, (∑ t, μ t * ordinaryMargin t i) ≤
      c (Fin.castAdd 3 i) + c (Fin.natAdd 3 i)) :
    ∃ w : Fin 9 → Fin 3 → R,
      (∀ t k, 0 ≤ w t k) ∧ (∀ t, (∑ k, w t k)=μ t) ∧
      ∀ j, (∑ t, consumption t (w t) j) ≤ c j := by
  classical
  have hq : ∀ (i : Fin 3) (t : Fin 9), 0 ≤ μ t * ordinaryMargin t i := by
    intro i t
    apply mul_nonneg (hμ t)
    fin_cases t <;> fin_cases i <;> norm_num [ordinaryMargin]
  obtain ⟨x₀,y₀,hxy₀,hx₀,hy₀⟩ := pair_reservations Finset.univ
    (fun t => μ t * ordinaryMargin t 0) (c 0) (c 3) (hc 0) (hc 3)
    (fun t _ => hq 0 t) (hp 0)
  obtain ⟨x₁,y₁,hxy₁,hx₁,hy₁⟩ := pair_reservations Finset.univ
    (fun t => μ t * ordinaryMargin t 1) (c 1) (c 4) (hc 1) (hc 4)
    (fun t _ => hq 1 t) (hp 1)
  obtain ⟨x₂,y₂,hxy₂,hx₂,hy₂⟩ := pair_reservations Finset.univ
    (fun t => μ t * ordinaryMargin t 2) (c 2) (c 5) (hc 2) (hc 5)
    (fun t _ => hq 2 t) (hp 2)
  let C : Fin 9 → Fin 6 → R := fun t => ![x₀ t,x₁ t,x₂ t,y₀ t,y₁ t,y₂ t]
  have hC : ∀ t j, 0 ≤ C t j := by
    intro t j
    have h₀ := hxy₀ t (Finset.mem_univ t)
    have h₁ := hxy₁ t (Finset.mem_univ t)
    have h₂ := hxy₂ t (Finset.mem_univ t)
    fin_cases j <;> simp [C] <;> tauto
  have hpC : ∀ (t : Fin 9) (i : Fin 3), μ t * ordinaryMargin t i ≤
      C t (Fin.castAdd 3 i) + C t (Fin.natAdd 3 i) := by
    intro t i
    have h₀ := (hxy₀ t (Finset.mem_univ t)).2.2
    have h₁ := (hxy₁ t (Finset.mem_univ t)).2.2
    have h₂ := (hxy₂ t (Finset.mem_univ t)).2.2
    fin_cases i <;> simp [C] <;> linarith
  have hall := fun t => ordinary_menu_fits t (μ t) (C t) (hμ t) (hC t) (hpC t)
  choose w hw hsum hcons using hall
  refine ⟨w,hw,hsum,?_⟩
  intro j
  have hs : (∑ t, consumption t (w t) j) ≤ ∑ t, C t j :=
    Finset.sum_le_sum (fun t _ => hcons t j)
  apply le_trans hs
  fin_cases j
  · simpa [C] using hx₀
  · simpa [C] using hx₁
  · simpa [C] using hx₂
  · simpa [C] using hy₀
  · simpa [C] using hy₁
  · simpa [C] using hy₂

def resonantConsumption (v : Fin 3 → R) : Fin 6 → R :=
  ![v 0,v 2,v 1,v 2,v 1,v 0]

/-- Actual weighted menu feasibility, with the resonant multiplicity
separated from the other nine row multiplicities. -/
def AggregateFeasible (μ : Fin 9 → R) (m : R) (c : Fin 6 → R) : Prop :=
  ∃ (w : Fin 9 → Fin 3 → R) (v : Fin 3 → R),
    (∀ t k, 0 ≤ w t k) ∧ (∀ t, (∑ k, w t k)=μ t) ∧
    (∀ k, 0 ≤ v k) ∧ (∑ k, v k)=m ∧
    ∀ j, (∑ t, consumption t (w t) j) + resonantConsumption v j ≤ c j

theorem ordinaryMenu_nonneg (t : Fin 9) (k : Fin 3) (j : Fin 6) :
    (0:R) ≤ ordinaryMenu t k j := by
  fin_cases t <;> fin_cases k <;> fin_cases j <;> norm_num [ordinaryMenu]

theorem ordinaryMargin_nonneg (t : Fin 9) (i : Fin 3) :
    (0:R) ≤ ordinaryMargin t i := by
  fin_cases t <;> fin_cases i <;> norm_num [ordinaryMargin]

/-- Full aggregate selection criterion for exactly the ten rows in the
paper's table. Since it is proved over any linearly ordered commutative
ring, specializing to ℝ gives fractional allocation and specializing to
ℤ gives the asserted integral allocation without a separate assumption. -/
theorem aggregate_selection_criterion (μ : Fin 9 → R) (m : R) (c : Fin 6 → R)
    (hμ : ∀ t, 0 ≤ μ t) (hm : 0 ≤ m) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ i : Fin 3, m + (∑ t, μ t * ordinaryMargin t i) ≤
      c (Fin.castAdd 3 i) + c (Fin.natAdd 3 i)) :
    AggregateFeasible μ m c ↔
      m ≤ c 0+c 1+c 2 ∧ m ≤ c 3+c 4+c 5 := by
  constructor
  · rintro ⟨w,v,hw,_hws,hv,hvs,hcapa⟩
    have hn : ∀ j, 0 ≤ ∑ t, consumption t (w t) j := by
      intro j
      apply Finset.sum_nonneg
      intro t _
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (hw t k) (ordinaryMenu_nonneg t k j)
    have h0 := hcapa 0
    have h1 := hcapa 1
    have h2 := hcapa 2
    have h3 := hcapa 3
    have h4 := hcapa 4
    have h5 := hcapa 5
    have hn0 := hn 0
    have hn1 := hn 1
    have hn2 := hn 2
    have hn3 := hn 3
    have hn4 := hn 4
    have hn5 := hn 5
    change _ + v 0 ≤ c 0 at h0
    change _ + v 2 ≤ c 1 at h1
    change _ + v 1 ≤ c 2 at h2
    change _ + v 2 ≤ c 3 at h3
    change _ + v 1 ≤ c 4 at h4
    change _ + v 0 ≤ c 5 at h5
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hvs
    change v 0 + (v 1 + v 2) = m at hvs
    constructor <;> linarith
  · rintro ⟨hplus,hminus⟩
    let q : Fin 3 → R := fun i => ∑ t, μ t * ordinaryMargin t i
    have hq : ∀ i, 0 ≤ q i := by
      intro i
      exact Finset.sum_nonneg (fun t _ => mul_nonneg (hμ t) (ordinaryMargin_nonneg t i))
    have hp0 : m+q 0 ≤ c 0+c 3 := hp 0
    have hp1 : m+q 1 ≤ c 1+c 4 := hp 1
    have hp2 : m+q 2 ≤ c 2+c 5 := hp 2
    obtain ⟨x,y,z,hx,hy,hz,hxc,hyc,hzc,he⟩ :=
      resonant_allocation m (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)
        hm (hc 0) (hc 1) (hc 2) (hc 3) (hc 4) (hc 5)
        (by linarith [hq 0]) (by linarith [hq 1]) (by linarith [hq 2]) hplus hminus
    let v : Fin 3 → R := ![x,y,z]
    let d : Fin 6 → R := fun j => c j-resonantConsumption v j
    have hx0 := le_trans hxc (min_le_left _ _)
    have hx5 := le_trans hxc (min_le_right _ _)
    have hy2 := le_trans hyc (min_le_left _ _)
    have hy4 := le_trans hyc (min_le_right _ _)
    have hz1 := le_trans hzc (min_le_left _ _)
    have hz3 := le_trans hzc (min_le_right _ _)
    have hd : ∀ j, 0 ≤ d j := by
      intro j
      fin_cases j <;> simp only [d,resonantConsumption,v,Matrix.cons_val_zero,Matrix.cons_val_succ]
      all_goals first | exact sub_nonneg.mpr hx0 | exact sub_nonneg.mpr hx5 |
        exact sub_nonneg.mpr hy2 | exact sub_nonneg.mpr hy4 |
        exact sub_nonneg.mpr hz1 | exact sub_nonneg.mpr hz3
    have hrem := resonant_remaining_pairs m (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)
      (q 0) (q 1) (q 2) x y z hx hy hz he hp0 hp1 hp2
    have hdp : ∀ i : Fin 3, (∑ t, μ t * ordinaryMargin t i) ≤
        d (Fin.castAdd 3 i)+d (Fin.natAdd 3 i) := by
      intro i
      fin_cases i
      · exact hrem.1
      · exact hrem.2.1
      · exact hrem.2.2
    obtain ⟨w,hw,hws,hwd⟩ := ordinary_aggregate μ d hμ hd hdp
    refine ⟨w,v,hw,hws,?_,?_,?_⟩
    · intro k; fin_cases k <;> simp [v] <;> assumption
    · simpa [v,Fin.sum_univ_succ, add_assoc] using he
    · intro j
      have := hwd j
      dsimp [d] at this
      linarith

/-- Row order from the paper, with R (row 6, zero-based) removed. -/
def paperOrdinaryMultiplicities (μ : Fin 10 → R) : Fin 9 → R :=
  ![μ 0,μ 1,μ 2,μ 3,μ 4,μ 5,μ 7,μ 8,μ 9]

def paperCapacities (s : Fin 6 → R) : Fin 6 → R :=
  ![s 0,s 3,s 4,s 5,s 1,s 2]

/-- The criterion in the paper's original row and slack coordinate order.
The three hypotheses are precisely the table-weighted pair capacities. -/
theorem aggregate_selection_paper_coordinates (μ : Fin 10 → R) (s : Fin 6 → R)
    (hμ : ∀ t, 0 ≤ μ t) (hs : ∀ j, 0 ≤ s j)
    (h16 : μ 0+2*μ 1+μ 2+μ 3+μ 5+μ 6+μ 7 ≤ s 0+s 5)
    (h24 : μ 0+μ 1+2*μ 2+μ 3+μ 4+μ 6+μ 8 ≤ s 1+s 3)
    (h35 : 2*μ 0+μ 1+μ 2+μ 4+μ 5+μ 6+μ 9 ≤ s 2+s 4) :
    AggregateFeasible (paperOrdinaryMultiplicities μ) (μ 6) (paperCapacities s) ↔
      μ 6 ≤ s 0+s 3+s 4 ∧ μ 6 ≤ s 1+s 2+s 5 := by
  have hm : ∀ t, 0 ≤ paperOrdinaryMultiplicities μ t := by
    intro t
    fin_cases t <;> exact hμ _
  have hc : ∀ j, 0 ≤ paperCapacities s j := by
    intro j
    fin_cases j <;> exact hs _
  have hp : ∀ i : Fin 3, μ 6 + (∑ t, paperOrdinaryMultiplicities μ t * ordinaryMargin t i) ≤
      paperCapacities s (Fin.castAdd 3 i) + paperCapacities s (Fin.natAdd 3 i) := by
    intro i
    fin_cases i
    · convert h16 using 1; norm_num [paperOrdinaryMultiplicities,ordinaryMargin,paperCapacities,Fin.sum_univ_succ]; ring
    · convert h24 using 1 <;> norm_num [paperOrdinaryMultiplicities,ordinaryMargin,paperCapacities,Fin.sum_univ_succ]
      all_goals first | (change s 3+s 1=s 1+s 3; exact add_comm _ _) | ring
    · convert h35 using 1 <;> norm_num [paperOrdinaryMultiplicities,ordinaryMargin,paperCapacities,Fin.sum_univ_succ] <;> ring
  rw [aggregate_selection_criterion _ _ _ hm (hμ 6) hc hp]
  change (μ 6 ≤ s 0+s 3+s 4 ∧ μ 6 ≤ s 5+s 1+s 2) ↔ _
  constructor <;> rintro ⟨h₁,h₂⟩ <;> exact ⟨h₁,by linarith⟩

end Aggregate
end UploadBroadcast.Allocation
