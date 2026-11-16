import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators
/-! # Exact numeric allocation statements

This module proves arithmetic allocation facts. It does not identify these
polyhedra with an operational coding problem or assert existence of a code.
-/
namespace UploadBroadcast.Allocation

/-- Nonnegative rates satisfying the three deficit constraints. -/
def OmniscienceFeasible (a b c x y z : ℝ) : Prop :=
  0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ a ≤ y + z ∧ b ≤ x + z ∧ c ≤ x + y

/-- The exact value of the three-variable numerical LP. -/
noncomputable def omniscienceValue (a b c : ℝ) : ℝ :=
  max (max a b) (max c ((a + b + c) / 2))

theorem omniscience_lower_bound {a b c x y z : ℝ}
    (h : OmniscienceFeasible a b c x y z) :
    omniscienceValue a b c ≤ x + y + z := by
  rcases h with ⟨hx, hy, hz, ha, hb, hc⟩
  unfold omniscienceValue
  repeat rw [max_le_iff]
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

/-- An optimizer exists for all three nonnegative deficits. -/
theorem omniscience_optimum (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ∃ x y z, OmniscienceFeasible a b c x y z ∧
      x + y + z = omniscienceValue a b c := by
  have va : a ≤ omniscienceValue a b c := by
    exact le_trans (le_max_left a b) (le_max_left _ _)
  have vb : b ≤ omniscienceValue a b c := by
    exact le_trans (le_max_right a b) (le_max_left _ _)
  have vc : c ≤ omniscienceValue a b c := by
    exact le_trans (le_max_left c _) (le_max_right _ _)
  have vs : (a+b+c)/2 ≤ omniscienceValue a b c := by
    exact le_trans (le_max_right c _) (le_max_right _ _)
  by_cases habc : a ≤ b + c
  · by_cases hbac : b ≤ a + c
    · by_cases hcab : c ≤ a + b
      · have hf : OmniscienceFeasible a b c ((b+c-a)/2)
            ((a+c-b)/2) ((a+b-c)/2) := by
          exact ⟨by linarith, by linarith, by linarith,
            by linarith, by linarith, by linarith⟩
        refine ⟨_, _, _, hf, le_antisymm ?_ (omniscience_lower_bound hf)⟩
        linarith
      · have hf : OmniscienceFeasible a b c b (c-b) 0 := by
          exact ⟨by linarith, by linarith, by linarith,
            by linarith, by linarith, by linarith⟩
        refine ⟨_, _, _, hf, le_antisymm ?_ (omniscience_lower_bound hf)⟩
        linarith
    · have hf : OmniscienceFeasible a b c c 0 (b-c) := by
        exact ⟨by linarith, by linarith, by linarith,
          by linarith, by linarith, by linarith⟩
      refine ⟨_, _, _, hf, le_antisymm ?_ (omniscience_lower_bound hf)⟩
      linarith
  · have hf : OmniscienceFeasible a b c 0 c (a-c) := by
      exact ⟨by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith⟩
    refine ⟨_, _, _, hf, le_antisymm ?_ (omniscience_lower_bound hf)⟩
    linarith

section OrderedRing
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Fill two bins by taking as much as possible from the first. The proof
works for both real and integer capacities. -/
theorem fill_two (m a b : R) (hm : 0 ≤ m) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (h : m ≤ a+b) :
    ∃ x y, 0 ≤ x ∧ 0 ≤ y ∧ x ≤ a ∧ y ≤ b ∧ x+y=m := by
  refine ⟨min m a, m-min m a, ?_⟩
  have h₁ := min_le_left m a
  have h₂ := min_le_right m a
  refine ⟨le_min hm ha, by linarith, h₂, ?_, by ring⟩
  by_cases hma : m ≤ a
  · rw [min_eq_left hma]; simpa using hb
  · rw [min_eq_right (le_of_not_ge hma)]; linarith

/-- Three-bin bounded allocation, again valid without division. -/
theorem fill_three (m a b c : R) (hm : 0 ≤ m) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (h : m ≤ a+b+c) :
    ∃ x y z, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x ≤ a ∧ y ≤ b ∧ z ≤ c ∧ x+y+z=m := by
  obtain ⟨x, yz, hx, hyz, hxa, hyzbc, he⟩ :=
    fill_two m a (b+c) hm ha (add_nonneg hb hc) (by linarith)
  obtain ⟨y, z, hy, hz, hyb, hzc, he'⟩ := fill_two yz b c hyz hb hc hyzbc
  exact ⟨x,y,z,hx,hy,hz,hxa,hyb,hzc,by linarith⟩

/-- The eight terms obtained by expanding the cyclic minima are all
bounded below by the required resonant multiplicity. -/
theorem cyclic_capacity (m a₁ a₂ a₃ b₁ b₂ b₃ : R)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (hp₁ : m ≤ a₁+b₁) (hp₂ : m ≤ a₂+b₂) (hp₃ : m ≤ a₃+b₃)
    (ha : m ≤ a₁+a₂+a₃) (hb : m ≤ b₁+b₂+b₃) :
    m ≤ min a₁ b₃ + min a₃ b₂ + min a₂ b₁ := by
  simp only [min_def]
  split_ifs <;> linarith

/-- Allocate the three resonant menu choices using the pair and
orientation constraints from the paper. -/
theorem resonant_allocation (m a₁ a₂ a₃ b₁ b₂ b₃ : R) (hm : 0 ≤ m)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (hp₁ : m ≤ a₁+b₁) (hp₂ : m ≤ a₂+b₂) (hp₃ : m ≤ a₃+b₃)
    (ha : m ≤ a₁+a₂+a₃) (hb : m ≤ b₁+b₂+b₃) :
    ∃ x y z, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
      x ≤ min a₁ b₃ ∧ y ≤ min a₃ b₂ ∧ z ≤ min a₂ b₁ ∧ x+y+z=m := by
  apply fill_three m _ _ _ hm (le_min ha₁ hb₃) (le_min ha₃ hb₂) (le_min ha₂ hb₁)
  exact cyclic_capacity m a₁ a₂ a₃ b₁ b₂ b₃ ha₁ ha₂ ha₃ hb₁ hb₂ hb₃ hp₁ hp₂ hp₃ ha hb

/-- The O menu consists of two singleton choices and one double choice.
Two opposite-pair capacity inequalities suffice, over reals or integers. -/
theorem o_menu_allocation (m c₁ c₂ c₄ c₆ : R) (hm : 0 ≤ m)
    (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) (h₄ : 0 ≤ c₄) (h₆ : 0 ≤ c₆)
    (hp : m ≤ c₁+c₆) (hq : m ≤ c₂+c₄) :
    ∃ x y d, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ d ∧
      x ≤ c₁ ∧ y ≤ c₂ ∧ d ≤ c₄ ∧ d ≤ c₆ ∧ x+y+d=m := by
  let d := max 0 (m-c₁-c₂)
  have hd : 0 ≤ d := le_max_left _ _
  have hdm : d ≤ m := by dsimp [d]; rw [max_le_iff]; constructor <;> linarith
  have hd₄ : d ≤ c₄ := by dsimp [d]; rw [max_le_iff]; constructor <;> linarith
  have hd₆ : d ≤ c₆ := by dsimp [d]; rw [max_le_iff]; constructor <;> linarith
  have hrem : m-d ≤ c₁+c₂ := by have := le_max_right 0 (m-c₁-c₂); dsimp [d]; linarith
  obtain ⟨x,y,hx,hy,hxc,hyc,he⟩ := fill_two (m-d) c₁ c₂ (by linarith) h₁ h₂ hrem
  exact ⟨x,y,d,hx,hy,hd,hxc,hyc,hd₄,hd₆,by linarith⟩
end OrderedRing
end UploadBroadcast.Allocation

namespace UploadBroadcast.Allocation

/-- The downward-closed waterfilling polyhedron, with each coordinate
bounded individually and each complementary pair bounded. -/
def WaterFeasible (u₁ u₂ u₃ p₁ p₂ p₃ x y z : ℝ) : Prop :=
  0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x ≤ u₁ ∧ y ≤ u₂ ∧ z ≤ u₃ ∧
    y+z ≤ p₁ ∧ x+z ≤ p₂ ∧ x+y ≤ p₃

def waterLevel (b₁ b₂ b₃ x y z : ℝ) : ℝ :=
  min (b₁+x) (min (b₂+y) (b₃+z))

theorem water_downward {u₁ u₂ u₃ p₁ p₂ p₃ x y z x' y' z' : ℝ}
    (hf : WaterFeasible u₁ u₂ u₃ p₁ p₂ p₃ x y z)
    (hx : 0 ≤ x') (hy : 0 ≤ y') (hz : 0 ≤ z')
    (hxx : x' ≤ x) (hyy : y' ≤ y) (hzz : z' ≤ z) :
    WaterFeasible u₁ u₂ u₃ p₁ p₂ p₃ x' y' z' := by
  rcases hf with ⟨_,_,_,h₁,h₂,h₃,h₄,h₅,h₆⟩
  exact ⟨hx,hy,hz,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith⟩

/-- Rounding an actual maximizing waterfilling point downward produces
an integer feasible point whose water level is precisely the floor of
the real optimum. The maximizing-point hypothesis specifies the source
optimization problem, not the desired integer conclusion. -/
theorem waterfill_integer_rounding
    (b₁ b₂ b₃ : ℤ) (u₁ u₂ u₃ p₁ p₂ p₃ x y z : ℝ)
    (hf : WaterFeasible u₁ u₂ u₃ p₁ p₂ p₃ x y z)
    (hopt : ∀ x' y' z', WaterFeasible u₁ u₂ u₃ p₁ p₂ p₃ x' y' z' →
      waterLevel b₁ b₂ b₃ x' y' z' ≤ waterLevel b₁ b₂ b₃ x y z) :
    ∃ X Y Z : ℤ, 0 ≤ X ∧ 0 ≤ Y ∧ 0 ≤ Z ∧
      WaterFeasible u₁ u₂ u₃ p₁ p₂ p₃ X Y Z ∧
      min (b₁+X) (min (b₂+Y) (b₃+Z)) =
        ⌊waterLevel b₁ b₂ b₃ x y z⌋ := by
  let h : ℤ := ⌊waterLevel b₁ b₂ b₃ x y z⌋
  let X := max 0 (h-b₁)
  let Y := max 0 (h-b₂)
  let Z := max 0 (h-b₃)
  have hh : (h:ℝ) ≤ waterLevel b₁ b₂ b₃ x y z := Int.floor_le _
  have hl₁ : (h:ℝ) ≤ b₁+x := le_trans hh (min_le_left _ _)
  have hl₂ : (h:ℝ) ≤ b₂+y := le_trans hh (le_trans (min_le_right _ _) (min_le_left _ _))
  have hl₃ : (h:ℝ) ≤ b₃+z := le_trans hh (le_trans (min_le_right _ _) (min_le_right _ _))
  have hX : 0 ≤ X := le_max_left _ _
  have hY : 0 ≤ Y := le_max_left _ _
  have hZ : 0 ≤ Z := le_max_left _ _
  have hXx : (X:ℝ) ≤ x := by
    dsimp [X]; push_cast; rw [max_le_iff]; exact ⟨hf.1, by linarith⟩
  have hYy : (Y:ℝ) ≤ y := by
    dsimp [Y]; push_cast; rw [max_le_iff]; exact ⟨hf.2.1, by linarith⟩
  have hZz : (Z:ℝ) ≤ z := by
    dsimp [Z]; push_cast; rw [max_le_iff]; exact ⟨hf.2.2.1, by linarith⟩
  have hF : WaterFeasible u₁ u₂ u₃ p₁ p₂ p₃ X Y Z :=
    water_downward hf (by exact_mod_cast hX) (by exact_mod_cast hY)
      (by exact_mod_cast hZ) hXx hYy hZz
  refine ⟨X,Y,Z,hX,hY,hZ,hF,le_antisymm ?_ ?_⟩
  · have hm := hopt X Y Z hF
    have hc : ((min (b₁+X) (min (b₂+Y) (b₃+Z)) : ℤ):ℝ) ≤
        waterLevel b₁ b₂ b₃ x y z := by
      push_cast
      exact hm
    exact Int.le_floor.mpr hc
  · apply le_min
    · have := le_max_right 0 (h-b₁); dsimp [X]; omega
    · apply le_min
      · have := le_max_right 0 (h-b₂); dsimp [Y]; omega
      · have := le_max_right 0 (h-b₃); dsimp [Z]; omega

/-- Algebraic conversion from integer waterfilling to LCBC allocation.
Here x,y,z represent the complementary pair variables λ₂₃,λ₁₃,λ₁₂.
The aligned allocation is the residual minimum. -/
theorem integer_lcbc_from_waterfill
    (r p₁ p₂ p₃ b₁ b₂ b₃ x y z : ℤ)
    (hp₁ : r+y+z ≤ p₁) (hp₂ : r+x+z ≤ p₂) (hp₃ : r+x+y ≤ p₃)
    (hb₁ : p₁ ≤ b₁) (hb₂ : p₂ ≤ b₂) (hb₃ : p₃ ≤ b₃) :
    ∃ a : ℤ, 0 ≤ a ∧ r+y+z+a ≤ b₁ ∧ r+x+z+a ≤ b₂ ∧
      r+x+y+a ≤ b₃ ∧
      2*r+x+y+z+a = r+min (b₁+x) (min (b₂+y) (b₃+z)) := by
  let a := min (b₁-y-z) (min (b₂-x-z) (b₃-x-y)) - r
  have hmin : r ≤ min (b₁-y-z) (min (b₂-x-z) (b₃-x-y)) := by
    apply le_min
    · omega
    · apply le_min <;> omega
  refine ⟨a, by dsimp [a]; omega, ?_, ?_, ?_, ?_⟩
  · have := min_le_left (b₁-y-z) (min (b₂-x-z) (b₃-x-y)); dsimp [a]; omega
  · have := le_trans (min_le_right (b₁-y-z) (min (b₂-x-z) (b₃-x-y)))
      (min_le_left (b₂-x-z) (b₃-x-y)); dsimp [a]; omega
  · have := le_trans (min_le_right (b₁-y-z) (min (b₂-x-z) (b₃-x-y)))
      (min_le_right (b₂-x-z) (b₃-x-y)); dsimp [a]; omega
  · dsimp [a]
    simp only [min_def]
    split_ifs <;> omega
end UploadBroadcast.Allocation

namespace UploadBroadcast.Allocation

/-- Exact numerical LCBC rounding theorem for the paper's waterfilling
polyhedron. The operational identification of its real optimum with
broadcast cost is deliberately not part of this arithmetic statement. -/
theorem integer_lcbc_allocation
    (r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ m₁ m₂ m₃ : ℤ)
    (hr : 0 ≤ r) (hb₁ : p₁ ≤ b₁) (hb₂ : p₂ ≤ b₂) (hb₃ : p₃ ≤ b₃)
    (hm₁ : b₁ ≤ m₁) (hm₂ : b₂ ≤ m₂) (hm₃ : b₃ ≤ m₃)
    (x y z : ℝ)
    (hf : WaterFeasible (u₁-r) (u₂-r) (u₃-r) (p₁-r) (p₂-r) (p₃-r) x y z)
    (hopt : ∀ x' y' z',
      WaterFeasible (u₁-r) (u₂-r) (u₃-r) (p₁-r) (p₂-r) (p₃-r) x' y' z' →
      waterLevel b₁ b₂ b₃ x' y' z' ≤ waterLevel b₁ b₂ b₃ x y z) :
    ∃ X Y Z a : ℤ, 0 ≤ r ∧ 0 ≤ X ∧ 0 ≤ Y ∧ 0 ≤ Z ∧ 0 ≤ a ∧
      r+X ≤ u₁ ∧ r+Y ≤ u₂ ∧ r+Z ≤ u₃ ∧
      r+Y+Z ≤ p₁ ∧ r+X+Z ≤ p₂ ∧ r+X+Y ≤ p₃ ∧
      r+Y+Z+a ≤ b₁ ∧ r+X+Z+a ≤ b₂ ∧ r+X+Y+a ≤ b₃ ∧
      0 ≤ m₁-r-Y-Z-a ∧ 0 ≤ m₂-r-X-Z-a ∧ 0 ≤ m₃-r-X-Y-a ∧
      m₁+m₂+m₃-2*r-X-Y-Z-a =
        ⌈((m₁+m₂+m₃-r : ℤ):ℝ)-waterLevel b₁ b₂ b₃ x y z⌉ := by
  obtain ⟨X,Y,Z,hX,hY,hZ,hF,hlevel⟩ := waterfill_integer_rounding b₁ b₂ b₃
    (u₁-r) (u₂-r) (u₃-r) (p₁-r) (p₂-r) (p₃-r) x y z hf hopt
  rcases hF with ⟨_,_,_,hU₁,hU₂,hU₃,hP₁,hP₂,hP₃⟩
  have hU₁' : r+X ≤ u₁ := by exact_mod_cast (show (r:ℝ)+X ≤ u₁ by linarith)
  have hU₂' : r+Y ≤ u₂ := by exact_mod_cast (show (r:ℝ)+Y ≤ u₂ by linarith)
  have hU₃' : r+Z ≤ u₃ := by exact_mod_cast (show (r:ℝ)+Z ≤ u₃ by linarith)
  have hP₁' : r+Y+Z ≤ p₁ := by exact_mod_cast (show (r:ℝ)+Y+Z ≤ p₁ by linarith)
  have hP₂' : r+X+Z ≤ p₂ := by exact_mod_cast (show (r:ℝ)+X+Z ≤ p₂ by linarith)
  have hP₃' : r+X+Y ≤ p₃ := by exact_mod_cast (show (r:ℝ)+X+Y ≤ p₃ by linarith)
  obtain ⟨a,ha,hA₁,hA₂,hA₃,he⟩ := integer_lcbc_from_waterfill
    r p₁ p₂ p₃ b₁ b₂ b₃ X Y Z
    hP₁' hP₂' hP₃' hb₁ hb₂ hb₃
  refine ⟨X,Y,Z,a,hr,hX,hY,hZ,ha,hU₁',hU₂',hU₃',hP₁',hP₂',hP₃',
    hA₁,hA₂,hA₃,by omega,by omega,by omega,?_⟩
  rw [hlevel] at he
  have hc : ⌈((m₁+m₂+m₃-r : ℤ):ℝ)-waterLevel b₁ b₂ b₃ x y z⌉ =
      m₁+m₂+m₃-r-⌊waterLevel b₁ b₂ b₃ x y z⌋ := by
    rw [sub_eq_add_neg, add_comm, Int.ceil_add_intCast, Int.ceil_neg]
    omega
  rw [hc]
  omega
end UploadBroadcast.Allocation

namespace UploadBroadcast.Allocation
section
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Under opposite-pair capacities, the two orientation inequalities
are exactly equivalent to feasibility of the resonant menu. -/
theorem resonant_selection_iff (m a₁ a₂ a₃ b₁ b₂ b₃ : R) (hm : 0 ≤ m)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (hp₁ : m ≤ a₁+b₁) (hp₂ : m ≤ a₂+b₂) (hp₃ : m ≤ a₃+b₃) :
    (∃ x y z, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
      x ≤ min a₁ b₃ ∧ y ≤ min a₃ b₂ ∧ z ≤ min a₂ b₁ ∧ x+y+z=m) ↔
      m ≤ a₁+a₂+a₃ ∧ m ≤ b₁+b₂+b₃ := by
  constructor
  · rintro ⟨x,y,z,hx,hy,hz,hxc,hyc,hzc,he⟩
    have hxa := le_trans hxc (min_le_left _ _)
    have hxb := le_trans hxc (min_le_right _ _)
    have hya := le_trans hyc (min_le_left _ _)
    have hyb := le_trans hyc (min_le_right _ _)
    have hza := le_trans hzc (min_le_left _ _)
    have hzb := le_trans hzc (min_le_right _ _)
    constructor <;> linarith
  · rintro ⟨ha,hb⟩
    exact resonant_allocation m a₁ a₂ a₃ b₁ b₂ b₃ hm ha₁ ha₂ ha₃ hb₁ hb₂ hb₃
      hp₁ hp₂ hp₃ ha hb

/-- After resonant allocation, every opposite pair retains its reserved
nonresonant quota. This is the subtraction step in aggregate packing. -/
theorem resonant_remaining_pairs
    (m a₁ a₂ a₃ b₁ b₂ b₃ q₁ q₂ q₃ x y z : R)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (he : x+y+z=m)
    (hp₁ : m+q₁ ≤ a₁+b₁) (hp₂ : m+q₂ ≤ a₂+b₂)
    (hp₃ : m+q₃ ≤ a₃+b₃) :
    q₁ ≤ (a₁-x)+(b₁-z) ∧ q₂ ≤ (a₂-z)+(b₂-y) ∧
      q₃ ≤ (a₃-y)+(b₃-x) := by
  exact ⟨by linarith,by linarith,by linarith⟩
end
end UploadBroadcast.Allocation

namespace UploadBroadcast.Allocation
section
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Simultaneously reserve one opposite pair for finitely many ordinary
menu types. Reservations use only ordered-ring operations, hence apply
unchanged to integer multiplicities and integer slack. -/
theorem pair_reservations {ι : Type*} (s : Finset ι) (q : ι → R) (a b : R)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hcap : ∑ i ∈ s, q i ≤ a+b) :
    ∃ x y : ι → R,
      (∀ i ∈ s, 0 ≤ x i ∧ 0 ≤ y i ∧ x i+y i=q i) ∧
      (∑ i ∈ s, x i) ≤ a ∧ (∑ i ∈ s, y i) ≤ b := by
  classical
  induction s using Finset.induction_on generalizing a b with
  | empty =>
      exact ⟨fun _ => 0, fun _ => 0, by simp, by simpa using ha, by simpa using hb⟩
  | @insert i s hi ih =>
      have hqi := hq i (Finset.mem_insert_self i s)
      have hqs : ∀ j ∈ s, 0 ≤ q j := fun j hj => hq j (Finset.mem_insert_of_mem hj)
      have hsum : 0 ≤ ∑ j ∈ s, q j := Finset.sum_nonneg hqs
      rw [Finset.sum_insert hi] at hcap
      obtain ⟨xi,yi,hxi,hyi,hxia,hyib,he⟩ := fill_two (q i) a b hqi ha hb (by linarith)
      obtain ⟨x,y,hxy,hxa,hyb⟩ := ih (a-xi) (b-yi) (by linarith) (by linarith) hqs (by linarith)
      let X := Function.update x i xi
      let Y := Function.update y i yi
      have hX : ∀ j ∈ s, X j = x j := by
        intro j hj
        have hji : j ≠ i := by intro h; subst j; exact hi hj
        simp [X, Function.update, hji]
      have hY : ∀ j ∈ s, Y j = y j := by
        intro j hj
        have hji : j ≠ i := by intro h; subst j; exact hi hj
        simp [Y, Function.update, hji]
      have hsX : (∑ j ∈ s, X j) = ∑ j ∈ s, x j := Finset.sum_congr rfl hX
      have hsY : (∑ j ∈ s, Y j) = ∑ j ∈ s, y j := Finset.sum_congr rfl hY
      refine ⟨X,Y,?_,?_,?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa [X,Y] using And.intro hxi (And.intro hyi he)
        · rw [hX j hj,hY j hj]
          exact hxy j hj
      · rw [Finset.sum_insert hi, hsX]
        simp only [X, Function.update_self]
        linarith
      · rw [Finset.sum_insert hi, hsY]
        simp only [Y, Function.update_self]
        linarith
end
end UploadBroadcast.Allocation

namespace UploadBroadcast.Allocation

/-- Integer deficits admit an optimal half-integral rate triple. This is
only the numerical two-instance scaling statement, not a coding claim. -/
theorem omniscience_half_integral (a b c : ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ∃ X Y Z : ℤ,
      OmniscienceFeasible a b c ((X:ℝ)/2) ((Y:ℝ)/2) ((Z:ℝ)/2) ∧
      ((X:ℝ)/2)+((Y:ℝ)/2)+((Z:ℝ)/2) = omniscienceValue a b c := by
  have ha' : (0:ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (0:ℝ) ≤ b := by exact_mod_cast hb
  have hc' : (0:ℝ) ≤ c := by exact_mod_cast hc
  have va : (a:ℝ) ≤ omniscienceValue a b c :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have vb : (b:ℝ) ≤ omniscienceValue a b c :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have vc : (c:ℝ) ≤ omniscienceValue a b c :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have vs : ((a:ℝ)+b+c)/2 ≤ omniscienceValue a b c :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  by_cases h₁ : (a:ℝ) ≤ b+c
  · by_cases h₂ : (b:ℝ) ≤ a+c
    · by_cases h₃ : (c:ℝ) ≤ a+b
      · refine ⟨b+c-a,a+c-b,a+b-c,?_,?_⟩
        · unfold OmniscienceFeasible
          push_cast
          exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
        · apply le_antisymm
          · push_cast; linarith
          · apply omniscience_lower_bound
            unfold OmniscienceFeasible
            push_cast
            exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
      · refine ⟨2*b,2*(c-b),0,?_,?_⟩
        · unfold OmniscienceFeasible
          push_cast
          exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
        · apply le_antisymm
          · push_cast; linarith
          · apply omniscience_lower_bound
            unfold OmniscienceFeasible
            push_cast
            exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
    · refine ⟨2*c,0,2*(b-c),?_,?_⟩
      · unfold OmniscienceFeasible
        push_cast
        exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
      · apply le_antisymm
        · push_cast; linarith
        · apply omniscience_lower_bound
          unfold OmniscienceFeasible
          push_cast
          exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
  · refine ⟨0,2*c,2*(a-c),?_,?_⟩
    · unfold OmniscienceFeasible
      push_cast
      exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
    · apply le_antisymm
      · push_cast; linarith
      · apply omniscience_lower_bound
        unfold OmniscienceFeasible
        push_cast
        exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
end UploadBroadcast.Allocation
