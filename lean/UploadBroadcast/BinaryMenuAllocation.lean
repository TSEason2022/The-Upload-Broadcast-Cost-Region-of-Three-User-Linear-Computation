import UploadBroadcast.NonzeroDefectProfile
import UploadBroadcast.AllocationAggregate

/-! Integer charge fitting for every row of `tab:binary-extra-menus`.
The six coordinate order is the paper's (123,132,213,231,312,321).
These are numerical packing theorems, not assumed relay-existence statements. -/
namespace UploadBroadcast.BinaryMenuAllocation
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

inductive Family | R0 | T2 | R1 | T3H | R2
  deriving DecidableEq, Fintype

def pairLeft : Fin 3 → Fin 6 := ![0,1,2]
def pairRight : Fin 3 → Fin 6 := ![5,3,4]

def charge : Family → Fin 3 → ℕ
  | .R0 | .R2 => ![1,1,1]
  | .T2 => ![1,0,0]
  | .R1 => ![0,0,1]
  | .T3H => ![0,1,0]

/-- Repeated generators pad the menus without changing their choices.
The six R₂ generators are precisely the six directed three-vertex paths. -/
def menu : Family → Fin 6 → Fin 6 → ℕ
  | .R0 => ![![0,0,0,1,0,0], ![0,0,0,0,0,1], ![1,0,1,0,0,0],
      ![0,1,0,0,1,0], ![0,0,0,1,0,0], ![0,0,0,0,0,1]]
  | .T2 => ![![1,0,0,0,0,0], ![0,0,0,0,0,1], ![1,0,0,0,0,0],
      ![1,0,0,0,0,0], ![1,0,0,0,0,0], ![1,0,0,0,0,0]]
  | .R1 => ![![0,0,1,0,0,0], ![0,0,0,0,1,0], ![0,0,1,0,0,0],
      ![0,0,1,0,0,0], ![0,0,1,0,0,0], ![0,0,1,0,0,0]]
  | .T3H => ![![0,1,0,0,0,0], ![0,0,0,1,0,0], ![0,1,0,0,0,0],
      ![0,1,0,0,0,0], ![0,1,0,0,0,0], ![0,1,0,0,0,0]]
  | .R2 => ![![0,0,1,0,0,1], ![0,0,0,1,1,0], ![1,0,0,0,1,0],
      ![0,1,0,0,0,1], ![0,1,1,0,0,0], ![1,0,0,1,0,0]]

/-- Every additional binary menu fits an integer reservation with its
stated opposite-pair charges. No fractional menu mixing is used. -/
theorem menu_fits (g : Family) (c : Fin 6 → ℕ)
    (hp : ∀ i : Fin 3, charge g i ≤ c (pairLeft i)+c (pairRight i)) :
    ∃ k : Fin 6, ∀ j, menu g k j ≤ c j := by
  have h₀ := hp 0
  have h₁ := hp 1
  have h₂ := hp 2
  cases g <;>
    simp [charge,pairLeft,pairRight] at h₀ h₁ h₂ <;>
    simp [Fin.exists_fin_succ,Fin.forall_fin_succ,menu] <;> omega

/-- The same scalar selection stated for signed integer slacks. -/
theorem menu_fits_int (g : Family) (c : Fin 6 → ℤ) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ i : Fin 3, (charge g i : ℤ) ≤ c (pairLeft i)+c (pairRight i)) :
    ∃ k : Fin 6, ∀ j, (menu g k j : ℤ) ≤ c j := by
  have hn : ∀ i : Fin 3, charge g i ≤ (c (pairLeft i)).toNat+(c (pairRight i)).toNat := by
    intro i
    have hh := hp i
    have hL := hc (pairLeft i)
    have hR := hc (pairRight i)
    omega
  obtain ⟨k,hk⟩ := menu_fits g (fun j => (c j).toNat) hn
  refine ⟨k,fun j => ?_⟩
  have hh := hk j
  have hj := hc j
  omega

/-- Pair margins computed from the actual classified-family dimension
formulas, in the same charge order as the source table. -/
def margin : Family → ℕ → Fin 3 → ℕ
  | .R0,n => ![n,n,n]
  | .T2,n => ![n,n-1,n]
  | .R1,n => ![n-1,n-1,n]
  | .T3H,n | .R2,n => ![n-1,n-1,n-1]

def minimumParameter : Family → ℕ
  | .R0 | .T2 | .R1 => 1
  | .T3H | .R2 => 2

theorem charge_le_margin (g : Family) (n : ℕ) (hn : minimumParameter g ≤ n)
    (i : Fin 3) : charge g i ≤ margin g n i := by
  cases g <;> fin_cases i <;> simp [charge,margin,minimumParameter] at * <;> omega

/-- The R₂ menu really is the user-permutation orbit of e₄+e₅.
A path is specified by its three distinct vertices (start, middle, end). -/
def pathIncrement (a b c : Three) (r : Fin 6) : ℕ :=
  if ((Profile.firstOrder r).2.1=a ∧ (Profile.firstOrder r).1=b) ∨
     ((Profile.firstOrder r).2.1=b ∧ (Profile.firstOrder r).1=c) then 1 else 0

theorem r2_menu_is_path (k : Fin 6) :
    ∃ a b c : Three, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ menu .R2 k = pathIncrement a b c := by
  fin_cases k
  · exact ⟨0,1,2,by decide,by decide,by decide,by ext r; fin_cases r <;> decide⟩
  · exact ⟨0,2,1,by decide,by decide,by decide,by ext r; fin_cases r <;> decide⟩
  · exact ⟨1,0,2,by decide,by decide,by decide,by ext r; fin_cases r <;> decide⟩
  · exact ⟨1,2,0,by decide,by decide,by decide,by ext r; fin_cases r <;> decide⟩
  · exact ⟨2,0,1,by decide,by decide,by decide,by ext r; fin_cases r <;> decide⟩
  · exact ⟨2,1,0,by decide,by decide,by decide,by ext r; fin_cases r <;> decide⟩

theorem path_is_r2_menu (a b c : Three) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ k, pathIncrement a b c = menu .R2 k := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all
  all_goals decide

/-- The displayed margins are computed from the full first and doubled
second profile arithmetic, rather than introduced as charge assumptions. -/
theorem margins_from_profile (g : Family) (n : ℕ) (hn : minimumParameter g ≤ n)
    (i : Fin 3) :
    let f : NonzeroDefectProfile.Family := match g with
      | .R0 => .R0 | .T2 => .T2 | .R1 => .R1 | .T3H => .T3 | .R2 => .R2
    NonzeroDefectProfile.doubledSecond f n -
      (NonzeroDefectProfile.fullFirst f n (pairLeft i) +
       NonzeroDefectProfile.fullFirst f n (pairRight i)) = margin g n i := by
  cases g <;> fin_cases i <;>
    simp [NonzeroDefectProfile.doubledSecond,NonzeroDefectProfile.fullFirst,
      pairLeft,pairRight,margin,minimumParameter] at * <;> omega

theorem h_margin_from_profile (n : ℕ) (hn : 2 ≤ n) (i : Fin 3) :
    NonzeroDefectProfile.doubledSecond .H n -
      (NonzeroDefectProfile.fullFirst .H n (pairLeft i) +
       NonzeroDefectProfile.fullFirst .H n (pairRight i)) = margin .T3H n i := by
  fin_cases i <;> simp [NonzeroDefectProfile.doubledSecond,
    NonzeroDefectProfile.fullFirst,pairLeft,pairRight,margin] <;> omega

/-- Simultaneous integer reservations and scalar menu selections for an
arbitrary finite collection of additional binary components. -/
theorem aggregate_menu_fits {I : Type*} [Fintype I] (g : I → Family)
    (c : Fin 6 → ℤ) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ p : Fin 3, (∑ t, (charge (g t) p : ℤ)) ≤
      c (pairLeft p)+c (pairRight p)) :
    ∃ k : I → Fin 6, ∀ j, (∑ t, (menu (g t) (k t) j : ℤ)) ≤ c j := by
  classical
  obtain ⟨x₀,y₀,hxy₀,hx₀,hy₀⟩ := Allocation.pair_reservations Finset.univ
    (fun t => (charge (g t) 0 : ℤ)) (c 0) (c 5) (hc 0) (hc 5)
    (fun _ _ => Nat.cast_nonneg _) (hp 0)
  obtain ⟨x₁,y₁,hxy₁,hx₁,hy₁⟩ := Allocation.pair_reservations Finset.univ
    (fun t => (charge (g t) 1 : ℤ)) (c 1) (c 3) (hc 1) (hc 3)
    (fun _ _ => Nat.cast_nonneg _) (hp 1)
  obtain ⟨x₂,y₂,hxy₂,hx₂,hy₂⟩ := Allocation.pair_reservations Finset.univ
    (fun t => (charge (g t) 2 : ℤ)) (c 2) (c 4) (hc 2) (hc 4)
    (fun _ _ => Nat.cast_nonneg _) (hp 2)
  let r : I → Fin 6 → ℤ := fun t => ![x₀ t,x₁ t,x₂ t,y₁ t,y₂ t,y₀ t]
  have hr (t : I) : ∀ j, 0 ≤ r t j := by
    have h₀ := hxy₀ t (Finset.mem_univ t)
    have h₁ := hxy₁ t (Finset.mem_univ t)
    have h₂ := hxy₂ t (Finset.mem_univ t)
    intro j; fin_cases j <;> simp [r]
    all_goals omega
  have hp' (t : I) : ∀ p, (charge (g t) p : ℤ) ≤ r t (pairLeft p)+r t (pairRight p) := by
    have h₀ := hxy₀ t (Finset.mem_univ t)
    have h₁ := hxy₁ t (Finset.mem_univ t)
    have h₂ := hxy₂ t (Finset.mem_univ t)
    intro p; fin_cases p <;>
      simp [r,pairLeft,pairRight]
    all_goals omega
  choose k hk using fun t => menu_fits_int (g t) (r t) (hr t) (hp' t)
  refine ⟨k,fun j => (Finset.sum_le_sum (fun t _ => hk t j)).trans ?_⟩
  fin_cases j <;> simp [r]
  all_goals assumption

end UploadBroadcast.BinaryMenuAllocation
