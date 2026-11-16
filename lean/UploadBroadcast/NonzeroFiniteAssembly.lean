import UploadBroadcast.GlobalMenuAssembly
import UploadBroadcast.NonzeroBinaryMenus
import UploadBroadcast.R2PermutedMenus
import UploadBroadcast.NonzeroSameChart

namespace UploadBroadcast.NonzeroFiniteAssembly
open Module Profile NonzeroDefectProfile NonzeroFamilyRanks GlobalMenuAssembly
open scoped BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- All eight original-field nonzero-defect binary families. -/
inductive Kind | hyperplane (g : NonzeroBinaryMenus.Kind) | R2
  deriving DecidableEq, Fintype

def family : Kind → Family
  | .hyperplane g => NonzeroBinaryMenus.family g
  | .R2 => .R2

def rank (g : Kind) (n : ℕ) : ℕ :=
  match g with
  | .hyperplane g => fullAmbient (NonzeroBinaryMenus.family g) n-1
  | .R2 => 3*n-1

def menu : Kind → Fin 6 → Fin 6 → ℤ
  | .hyperplane g => fun k r => NonzeroBinaryMenus.menu g k r
  | .R2 => fun k r => BinaryMenuAllocation.menu .R2 k r

def charge : Kind → Fin 3 → ℤ
  | .hyperplane .T1 => ![0,0,1]
  | .hyperplane .O => ![1,0,1]
  | .hyperplane g => fun p => BinaryMenuAllocation.charge (NonzeroBinaryMenus.extraFamily g) p
  | .R2 => fun p => BinaryMenuAllocation.charge .R2 p

theorem charge_nonneg (g : Kind) (p : Fin 3) : 0 ≤ charge g p := by
  cases g with
  | R2 => exact Nat.cast_nonneg _
  | hyperplane g => cases g <;> fin_cases p <;> norm_num [charge]

theorem menu_fits (g : Kind) (c : Fin 6 → ℤ) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ p, charge g p ≤ c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p)) :
    ∃ k, ∀ j, menu g k j ≤ c j := by
  cases g with
  | R2 => exact BinaryMenuAllocation.menu_fits_int .R2 c hc hp
  | hyperplane g =>
    cases g with
    | T1 =>
      have hh : (1 : ℤ) ≤ c 2+c 4 := hp 2
      by_cases h : 1 ≤ c 4
      · refine ⟨0,?_⟩
        intro j; fin_cases j <;> simp [menu,NonzeroBinaryMenus.menu] <;> first | assumption | exact hc _
      · refine ⟨1,?_⟩
        intro j; fin_cases j <;> simp [menu,NonzeroBinaryMenus.menu] <;> first | omega | exact hc _
    | O =>
      have h₀ : (1 : ℤ) ≤ c 0+c 5 := hp 0
      have h₂ : (1 : ℤ) ≤ c 2+c 4 := hp 2
      by_cases h₅ : 1 ≤ c 5
      · refine ⟨0,?_⟩
        intro j; fin_cases j <;> simp [menu,NonzeroBinaryMenus.menu] <;> first | assumption | exact hc _
      by_cases h₄ : 1 ≤ c 4
      · refine ⟨1,?_⟩
        intro j; fin_cases j <;> simp [menu,NonzeroBinaryMenus.menu] <;> first | assumption | exact hc _
      · refine ⟨2,?_⟩
        intro j; fin_cases j <;> simp [menu,NonzeroBinaryMenus.menu] <;> first | omega | exact hc _
    | R0 => exact BinaryMenuAllocation.menu_fits_int .R0 c hc hp
    | T2 => exact BinaryMenuAllocation.menu_fits_int .T2 c hc hp
    | R1 => exact BinaryMenuAllocation.menu_fits_int .R1 c hc hp
    | T3 => exact BinaryMenuAllocation.menu_fits_int .T3H c hc hp
    | H => exact BinaryMenuAllocation.menu_fits_int .T3H c hc hp

/-- Genuine indecomposability and seven family dimensions supply the complete
local geometric menu interface. -/
theorem realizes_menu (T : Task K V)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Kind) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T (family g) n) :
    RealizesMenu T (rank g n) (fun k => GlobalMenuAssembly.firstIncrement (menu g k)) := by
  intro k
  cases g with
  | hyperplane g =>
    obtain ⟨P,hg,hf,hd,hfirst,hsecond⟩ := NonzeroBinaryMenus.full_binary_menu T hT g n hn h k
    refine ⟨P,hg,hf,hd,?_⟩
    intro r
    rw [Task.inducedRelay_entry]
    cases r with
    | inl r => simpa only [GlobalMenuAssembly.firstIncrement,menu,Int.cast_natCast] using hfirst r
    | inr r => simpa only [GlobalMenuAssembly.firstIncrement,add_zero] using (hsecond r).le
  | R2 =>
    obtain ⟨P,hg,hf,hd,hfirst,hsecond⟩ := R2PermutedMenus.full_binary_R2_menu T hT n hn h k
    refine ⟨P,hg,hf,hd,?_⟩
    intro r
    rw [Task.inducedRelay_entry]
    cases r with
    | inl r => simpa only [GlobalMenuAssembly.firstIncrement,menu,Int.cast_natCast] using hfirst r
    | inr r => simpa only [GlobalMenuAssembly.firstIncrement,add_zero] using (hsecond r).le

/-- Same-chart original-field realization for q ≥ 3, from the same genuine
family classification data. -/
theorem same_chart_realizes [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : Task K V)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) :
    RealizesMenu T (fullAmbient g n-codimension g)
      (fun (_ : Unit) => GlobalMenuAssembly.firstIncrement (fun r => NonzeroDefectProfile.firstIncrement g r)) := by
  intro k
  obtain ⟨hfull₁,hfull₂,P,hg,hf,hd,_,hfirst,hsecond⟩ :=
    NonzeroSameChart.same_chart_full_and_relay hq T hT g n hn h
  refine ⟨P,hg,hf,hd,?_⟩
  intro r
  rw [Task.inducedRelay_entry]
  cases r with
  | inl r =>
    rw [hfirst,hfull₁]
    simp only [GlobalMenuAssembly.firstIncrement,Int.cast_natCast,le_refl]
  | inr r =>
    obtain ⟨i,l⟩ := r
    have h₁ := hsecond i l
    have h₂ := hfull₂ i l
    simp only [GlobalMenuAssembly.firstIncrement,add_zero]
    linarith only [h₁,h₂]

variable {I : Type} [Fintype I] {F : I → Type}
  [∀ t, AddCommGroup (F t)] [∀ t, Module K (F t)] [∀ t, FiniteDimensional K (F t)]

/-- A concrete finite binary relay theorem from component classification and
integer capacities. No local or global relay is assumed. -/
theorem binary_relay (T : (t : I) → Task K (F t))
    (hT : ∀ t, TaskDecomposition.Indecomposable (EdgeExtraction.configuration (T t)).spaces ⊤)
    (g : I → Kind) (n : I → ℕ) (hn : ∀ t, 1 ≤ n t)
    (hdims : ∀ t, Dimensions (T t) (family (g t)) (n t))
    (c : Fin 6 → ℤ) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ p, (∑ t, charge (g t) p) ≤
      c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p))
    (D : ℝ)
    (hfirst : ∀ j, entry (FiniteRelayAssembly.task T) (.inl j)+(c j : ℝ) ≤ D)
    (hsecond : ∀ r : Three × Three, entry (FiniteRelayAssembly.task T) (.inr r) ≤ D) :
    ∃ P : Submodule K (∀ t, F t), ∃ hg : (FiniteRelayAssembly.task T).LocallyGenerated P,
      (FiniteRelayAssembly.task T).RelayFeasible P ∧ finrank K P = ∑ t, rank (g t) (n t) ∧
      ∀ r, entry ((FiniteRelayAssembly.task T).inducedRelay P hg) r ≤ D :=
  assemble_charged_menus T (fun _ => Fin 6) (fun t => rank (g t) (n t))
    (fun t => menu (g t)) (fun t => charge (g t))
    (fun t p => charge_nonneg (g t) p) (fun t => menu_fits (g t))
    (fun t => realizes_menu (T t) (hT t) (g t) (n t) (hn t) (hdims t)) c hc hp D hfirst hsecond

/-- Actual finite same-chart relays, with the exact local upload-rank sum
and all fifteen bounds under the corresponding numerical first-entry budget. -/
theorem stable_relay [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : (t : I) → Task K (F t))
    (hT : ∀ t, TaskDecomposition.Indecomposable (EdgeExtraction.configuration (T t)).spaces ⊤)
    (g : I → Family) (n : I → ℕ) (hn : ∀ t, 1 ≤ n t)
    (hdims : ∀ t, Dimensions (T t) (g t) (n t)) (D : ℝ)
    (hfirst : ∀ r : Fin 6, entry (FiniteRelayAssembly.task T) (.inl r)+
      (∑ t, (NonzeroDefectProfile.firstIncrement (g t) r : ℝ)) ≤ D)
    (hsecond : ∀ r : Three × Three, entry (FiniteRelayAssembly.task T) (.inr r) ≤ D) :
    ∃ P : Submodule K (∀ t, F t), ∃ hg : (FiniteRelayAssembly.task T).LocallyGenerated P,
      (FiniteRelayAssembly.task T).RelayFeasible P ∧
      finrank K P = ∑ t, (fullAmbient (g t) (n t)-codimension (g t)) ∧
      ∀ r, entry ((FiniteRelayAssembly.task T).inducedRelay P hg) r ≤ D := by
  apply assemble_choices T (fun _ => Unit)
    (fun t => fullAmbient (g t) (n t)-codimension (g t))
    (fun t _ => GlobalMenuAssembly.firstIncrement (fun r => NonzeroDefectProfile.firstIncrement (g t) r))
    (fun t => same_chart_realizes hq (T t) (hT t) (g t) (n t) (hn t) (hdims t))
    (fun _ => ()) (fun _ => D)
  intro r
  cases r with
  | inl r => simpa only [GlobalMenuAssembly.firstIncrement,Int.cast_natCast] using hfirst r
  | inr r => simpa only [GlobalMenuAssembly.firstIncrement,Finset.sum_const_zero,add_zero] using hsecond r

end UploadBroadcast.NonzeroFiniteAssembly
