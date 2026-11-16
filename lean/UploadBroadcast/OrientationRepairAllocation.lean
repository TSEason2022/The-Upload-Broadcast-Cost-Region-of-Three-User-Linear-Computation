import UploadBroadcast.BinaryAugmentedAllocation

namespace UploadBroadcast.OrientationRepairAllocation
open BinaryMenuAllocation

def plus (c : Fin 6 → ℤ) : ℤ := c 0+c 3+c 4
def minus (c : Fin 6 → ℤ) : ℤ := c 1+c 2+c 5
def positiveCount (m : ℤ) (c : Fin 6 → ℤ) : ℤ := max 0 (m-plus c)
def negativeCount (m : ℤ) (c : Fin 6 → ℤ) : ℤ := max 0 (m-minus c)
def repaired (m : ℤ) (c : Fin 6 → ℤ) : Fin 6 → ℤ :=
  ![c 0,c 1-positiveCount m c,c 2,c 3-negativeCount m c,c 4,c 5]

/-- The total-slack inequality used in the repair proof already follows
from the three strengthened pair reservations. -/
theorem sum_capacity (m : ℤ) (q : Fin 3 → ℤ) (c : Fin 6 → ℤ)
    (hq : ∀ p, 0 ≤ q p)
    (hp : ∀ p, m+q p ≤ c (pairLeft p)+c (pairRight p)) :
    3*m ≤ plus c+minus c := by
  have h₀ : m+q 0 ≤ c 0+c 5 := hp 0
  have h₁ : m+q 1 ≤ c 1+c 3 := hp 1
  have h₂ : m+q 2 ≤ c 2+c 4 := hp 2
  have hq₀ := hq 0
  have hq₁ := hq 1
  have hq₂ := hq 2
  unfold plus minus
  omega

/-- Exact integer bookkeeping of both possible orientation repairs. At most
one orientation is repaired, enough slack exists at its charged coordinate,
and every strengthened pair reservation survives. -/
theorem repaired_capacities (m : ℤ) (q : Fin 3 → ℤ) (c : Fin 6 → ℤ)
    (hm : 0 ≤ m) (hq : ∀ p, 0 ≤ q p) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ p, m+q p ≤ c (pairLeft p)+c (pairRight p))
    (hsum : 3*m ≤ plus c+minus c) :
    0 ≤ positiveCount m c ∧ 0 ≤ negativeCount m c ∧
    positiveCount m c+negativeCount m c ≤ m ∧
    (positiveCount m c=0 ∨ negativeCount m c=0) ∧
    (∀ j, 0 ≤ repaired m c j) ∧
    (∀ p, m-positiveCount m c-negativeCount m c+q p ≤
      repaired m c (pairLeft p)+repaired m c (pairRight p)) ∧
    m-positiveCount m c-negativeCount m c ≤ plus (repaired m c) ∧
    m-positiveCount m c-negativeCount m c ≤ minus (repaired m c) := by
  have hp₀ : m+q 0 ≤ c 0+c 5 := hp 0
  have hp₁ : m+q 1 ≤ c 1+c 3 := hp 1
  have hp₂ : m+q 2 ≤ c 2+c 4 := hp 2
  have hq₀ := hq 0
  have hq₁ := hq 1
  have hq₂ := hq 2
  have hc₀ := hc 0
  have hc₁ := hc 1
  have hc₂ := hc 2
  have hc₃ := hc 3
  have hc₄ := hc 4
  have hc₅ := hc 5
  simp only [plus,minus] at hsum
  have ha : 0 ≤ positiveCount m c := le_max_left _ _
  have hb : 0 ≤ negativeCount m c := le_max_left _ _
  have hab : positiveCount m c+negativeCount m c ≤ m := by
    unfold positiveCount negativeCount plus minus
    omega
  have hone : positiveCount m c=0 ∨ negativeCount m c=0 := by
    unfold positiveCount negativeCount plus minus
    omega
  refine ⟨ha,hb,hab,hone,?_,?_,?_,?_⟩
  · intro j
    fin_cases j <;> simp [repaired,positiveCount,negativeCount,plus,minus] <;> omega
  · intro p
    fin_cases p <;> simp [repaired,pairLeft,pairRight,positiveCount,negativeCount,plus,minus] <;> omega
  · simp [repaired,positiveCount,negativeCount,plus,minus]
    omega
  · simp [repaired,positiveCount,negativeCount,plus,minus]
    omega

/-- The reserved coordinates are literally the two canonical repair
increments, so no hidden profile charge is lost in the bookkeeping. -/
theorem repaired_add_reserved (m : ℤ) (c : Fin 6 → ℤ) (j : Fin 6) :
    repaired m c j + (if j=1 then positiveCount m c else 0) +
      (if j=3 then negativeCount m c else 0) = c j := by
  fin_cases j <;> simp [repaired]

end UploadBroadcast.OrientationRepairAllocation
