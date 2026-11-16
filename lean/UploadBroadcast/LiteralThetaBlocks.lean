import UploadBroadcast.NonzeroFamilyRanks
import UploadBroadcast.NonzeroDefectRelays
import UploadBroadcast.RelayProfileTransport
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.LinearCombination

/-!
# Exact θ-dependent primitive configurations

This file checks the literal R₀/1 and D configurations at lines 2631–2667 of
`TIT_LCBC_optimized.tex`. The coefficient field is arbitrary; θ ≠ 0, 1 is
stated precisely where needed. No indecomposability or requested-rank
hypothesis is used.
-/
namespace UploadBroadcast.LiteralThetaBlocks
open Module Profile NonzeroDefectProfile
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
variable {K : Type} [Field K]

/-- A literal finite list of coefficient vectors, interpreted as its span. -/
def vspan {n d : ℕ} (v : Fin n → Fin d → K) : Submodule K (Fin d → K) :=
  Submodule.span K (Set.range v)

lemma mem_vspan {n d : ℕ} (v : Fin n → Fin d → K) (x : Fin d → K) :
    x ∈ vspan v ↔ ∃ c : Fin n → K, Fintype.linearCombination K v c = x := by
  rw [vspan, ← Fintype.range_linearCombination, LinearMap.mem_range]

lemma finrank_vspan {n d : ℕ} (v : Fin n → Fin d → K)
    (h : Function.Injective (Fintype.linearCombination K v)) :
    finrank K (vspan v) = n := by
  rw [vspan, ← Fintype.range_linearCombination,
    LinearMap.finrank_range_of_inj h, Module.finrank_fin_fun]

namespace R0
abbrev V (K : Type*) := Fin 4 → K

def A : Three → Submodule K (V K) :=
  ![vspan ![![1,0,0,0]], vspan ![![0,1,0,0],![0,0,0,1]],
    vspan ![![0,0,1,0],![1,0,0,1]]]

def U (θ : K) : Three → Submodule K (V K) :=
  ![vspan ![![1,0,0,0],![0,1,1,0]],
    vspan ![![0,1,0,0],![1,0,1,0],![0,0,0,1]],
    vspan ![![0,0,1,0],![1,θ,0,0],![1,0,0,1]]]

def P : Submodule K (V K) := vspan ![![1,0,0,0],![0,1,0,0],![0,0,1,0]]

lemma mem_A0 (v : V K) : v ∈ A 0 ↔ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 := by
  change v ∈ vspan _ ↔ _
  rw [mem_vspan]
  constructor
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ]
  · rintro ⟨h1,h2,h3⟩
    refine ⟨![v 0], ?_⟩
    ext j; fin_cases j <;> simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,h1,h2,h3]

lemma mem_A1 (v : V K) : v ∈ A 1 ↔ v 0 = 0 ∧ v 2 = 0 := by
  change v ∈ vspan _ ↔ _
  rw [mem_vspan]
  constructor
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ]
  · rintro ⟨h0,h2⟩
    refine ⟨![v 1,v 3], ?_⟩
    ext j; fin_cases j <;> simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,h0,h2]

lemma mem_A2 (v : V K) : v ∈ A 2 ↔ v 1 = 0 ∧ v 3 = v 0 := by
  change v ∈ vspan _ ↔ _
  rw [mem_vspan]
  constructor
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ]
  · rintro ⟨h1,h3⟩
    refine ⟨![v 2,v 0], ?_⟩
    ext j; fin_cases j <;> simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,h1,h3]

lemma mem_U0 (θ : K) (v : V K) : v ∈ U θ 0 ↔ v 2 = v 1 ∧ v 3 = 0 := by
  change v ∈ vspan _ ↔ _
  rw [mem_vspan]
  constructor
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ]
  · rintro ⟨h2,h3⟩
    refine ⟨![v 0,v 1], ?_⟩
    ext j; fin_cases j <;> simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,h2,h3]

lemma mem_U1 (θ : K) (v : V K) : v ∈ U θ 1 ↔ v 2 = v 0 := by
  change v ∈ vspan _ ↔ _
  rw [mem_vspan]
  constructor
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ]
  · intro h2
    refine ⟨![v 1,v 0,v 3], ?_⟩
    ext j; fin_cases j <;> simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,h2]

lemma mem_U2 (θ : K) (v : V K) : v ∈ U θ 2 ↔ v 1 = θ * (v 0-v 3) := by
  change v ∈ vspan _ ↔ _
  rw [mem_vspan]
  constructor
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ, mul_comm]
  · intro h1
    refine ⟨![v 2,v 0-v 3,v 3], ?_⟩
    ext j; fin_cases j <;> simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,h1,mul_comm]

lemma mem_P (v : V K) : v ∈ (P : Submodule K (V K)) ↔ v 3 = 0 := by
  rw [P, mem_vspan]
  constructor
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ]
  · intro h3
    refine ⟨![v 0,v 1,v 2], ?_⟩
    ext j; fin_cases j <;> simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,h3]


lemma side_dimension (i : Three) : finrank K ↥(A (K := K) i) = (![1,2,2] : Three → ℕ) i := by
  fin_cases i <;> change finrank K (vspan _) = _ <;> apply finrank_vspan
  all_goals
    intro a b h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    ext j; fin_cases j <;>
      simp_all [Fintype.linearCombination_apply, Fin.sum_univ_succ]

lemma signal_dimension (θ : K) (i : Three) :
    finrank K ↥(U θ i) = (![2,3,3] : Three → ℕ) i := by
  fin_cases i <;> change finrank K (vspan _) = _ <;> apply finrank_vspan
  all_goals
    intro a b h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    ext j; fin_cases j <;>
      simp_all [Fintype.linearCombination_apply, Fin.sum_univ_succ]

lemma relay_dimension : finrank K (P : Submodule K (V K)) = 3 := by
  apply finrank_vspan
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  ext j; fin_cases j <;>
    simp_all [Fintype.linearCombination_apply, Fin.sum_univ_succ]

lemma pair01 (θ : K) : U θ 0 ⊓ U θ 1 = vspan ![![1,1,1,0]] := by
  ext v
  rw [Submodule.mem_inf, mem_U0, mem_U1, mem_vspan]
  constructor
  · rintro ⟨⟨h2,h3⟩,h0⟩
    refine ⟨![v 0], ?_⟩
    ext j; fin_cases j <;>
      simp_all [Fintype.linearCombination_apply, Fin.sum_univ_succ]
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ]

lemma pair02 (θ : K) : U θ 0 ⊓ U θ 2 = vspan ![![1,θ,θ,0]] := by
  ext v
  rw [Submodule.mem_inf, mem_U0, mem_U2, mem_vspan]
  constructor
  · rintro ⟨⟨h2,h3⟩,h1⟩
    refine ⟨![v 0], ?_⟩
    ext j; fin_cases j <;>
      simp_all [Fintype.linearCombination_apply, Fin.sum_univ_succ,mul_comm]
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ,mul_comm]

lemma pair12 (θ : K) :
    U θ 1 ⊓ U θ 2 = vspan ![![1,θ,1,0],![0,-θ,0,1]] := by
  ext v
  rw [Submodule.mem_inf, mem_U1, mem_U2, mem_vspan]
  constructor
  · rintro ⟨h2,h1⟩
    refine ⟨![v 0,v 3], ?_⟩
    ext j; fin_cases j <;>
      simp_all [Fintype.linearCombination_apply, Fin.sum_univ_succ,mul_comm,mul_sub,sub_eq_add_neg,mul_add]
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ,mul_comm,mul_sub,sub_eq_add_neg,mul_add]

lemma pair_dimension (θ : K) (i j : Three) (hij : i ≠ j) :
    finrank K ↥(U θ i ⊓ U θ j) + 4 =
      (![2,3,3] : Three → ℕ) i + (![2,3,3] : Three → ℕ) j := by
  have h01 : finrank K ↥(U θ 0 ⊓ U θ 1) = 1 := by
    rw [pair01]; apply finrank_vspan
    intro a b h
    have h0 := congrFun h 0
    ext j; fin_cases j
    simpa [Fintype.linearCombination_apply, Fin.sum_univ_succ] using h0
  have h02 : finrank K ↥(U θ 0 ⊓ U θ 2) = 1 := by
    rw [pair02]; apply finrank_vspan
    intro a b h
    have h0 := congrFun h 0
    ext j; fin_cases j
    simpa [Fintype.linearCombination_apply, Fin.sum_univ_succ] using h0
  have h12 : finrank K ↥(U θ 1 ⊓ U θ 2) = 2 := by
    rw [pair12]; apply finrank_vspan
    intro a b h
    have h0 := congrFun h 0
    have h3 := congrFun h 3
    ext j; fin_cases j <;>
      simp_all [Fintype.linearCombination_apply, Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j <;>
    simp_all [h01,h02,h12]
  all_goals rw [inf_comm]; assumption

lemma triple_zero (θ : K) (hθ : θ ≠ 1) : U θ 0 ⊓ U θ 1 ⊓ U θ 2 = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  rcases (show (v 2 = v 1 ∧ v 3 = 0) ∧ v 2 = v 0 ∧ v 1 = θ*(v 0-v 3) by
    simpa only [Submodule.mem_inf,mem_U0,mem_U1,mem_U2,and_assoc] using hv) with
    ⟨⟨h21,h3⟩,h20,h1⟩
  have hz : (θ-1)*v 0 = 0 := by rw [h3,sub_zero] at h1; linear_combination -h1+h20-h21
  have h0 : v 0 = 0 := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hθ)
  change v = 0
  ext j; fin_cases j <;> simp_all

lemma side_le_signal (θ : K) (i : Three) : A i ≤ U θ i := by
  fin_cases i <;> intro v hv
  · change v ∈ A 0 at hv; change v ∈ U θ 0
    rw [mem_A0] at hv; rw [mem_U0]; rcases hv with ⟨h1,h2,h3⟩; simp_all
  · change v ∈ A 1 at hv; change v ∈ U θ 1
    rw [mem_A1] at hv; rw [mem_U1]; rcases hv with ⟨h0,h2⟩; simp_all
  · change v ∈ A 2 at hv; change v ∈ U θ 2
    rw [mem_A2] at hv; rw [mem_U2]; rcases hv with ⟨h1,h3⟩; simp_all

lemma sides_span : (⨆ i, A (K := K) i) = ⊤ := by
  rw [three_iSup]
  apply top_unique
  intro v _
  refine Submodule.mem_sup.mpr ⟨![v 0,v 1,0,v 3], ?_, ![0,0,v 2,0], ?_, ?_⟩
  · refine Submodule.mem_sup.mpr ⟨![v 0,0,0,0], ?_, ![0,v 1,0,v 3], ?_, ?_⟩
    · simp [mem_A0]
    · simp [mem_A1]
    · ext j; fin_cases j <;> simp
  · simp [mem_A2]
  · ext j; fin_cases j <;> simp

def task (θ : K) : Task K (V K) where
  A := A
  U := U θ
  side_le_signal := side_le_signal θ
  feasible i := by rw [sides_span]; exact le_top

lemma side_signal01 (θ : K) : A 0 ⊓ U θ 1 = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  rw [Submodule.mem_inf,mem_A0,mem_U1] at hv
  rcases hv with ⟨⟨h1,h2,h3⟩,h0⟩
  change v = 0
  ext j; fin_cases j <;> simp_all

lemma side_signal02 (θ : K) (hθ : θ ≠ 0) : A 0 ⊓ U θ 2 = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  rw [Submodule.mem_inf,mem_A0,mem_U2] at hv
  rcases hv with ⟨⟨h1,h2,h3⟩,h⟩
  have h0 : v 0 = 0 := by simpa [h1,h3,hθ] using h.symm
  change v = 0
  ext j; fin_cases j <;> simp_all

lemma side_signal10 (θ : K) : A 1 ⊓ U θ 0 = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  rw [Submodule.mem_inf,mem_A1,mem_U0] at hv
  rcases hv with ⟨⟨h0,h2⟩,h21,h3⟩
  change v = 0
  ext j; fin_cases j <;> simp_all

lemma side_signal12 (θ : K) : A 1 ⊓ U θ 2 = vspan ![![0,-θ,0,1]] := by
  ext v
  rw [Submodule.mem_inf,mem_A1,mem_U2,mem_vspan]
  constructor
  · rintro ⟨⟨h0,h2⟩,h1⟩
    refine ⟨![v 3], ?_⟩
    ext j; fin_cases j <;> simp_all [Fintype.linearCombination_apply,Fin.sum_univ_succ,mul_comm]
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,mul_comm]

lemma side_signal20 (θ : K) : A 2 ⊓ U θ 0 = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  rw [Submodule.mem_inf,mem_A2,mem_U0] at hv
  rcases hv with ⟨⟨h1,h3⟩,h21,h30⟩
  change v = 0
  ext j; fin_cases j <;> simp_all

lemma side_signal21 (θ : K) : A 2 ⊓ U θ 1 = vspan ![![1,0,1,1]] := by
  ext v
  rw [Submodule.mem_inf,mem_A2,mem_U1,mem_vspan]
  constructor
  · rintro ⟨⟨h1,h3⟩,h2⟩
    refine ⟨![v 0], ?_⟩
    ext j; fin_cases j <;> simp_all [Fintype.linearCombination_apply,Fin.sum_univ_succ]
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply,Fin.sum_univ_succ]

lemma side_signal_dimension (θ : K) (hθ : θ ≠ 0) (i j : Three) (hij : i ≠ j) :
    finrank K ↥(A j ⊓ U θ i) + 4 =
      (![1,2,2] : Three → ℕ) j + (![2,3,3] : Three → ℕ) i := by
  have h12 : finrank K ↥(A 1 ⊓ U θ 2) = 1 := by
    rw [side_signal12]; apply finrank_vspan
    intro a b h
    have h3 := congrFun h 3
    ext j; fin_cases j
    simpa [Fintype.linearCombination_apply,Fin.sum_univ_succ] using h3
  have h21 : finrank K ↥(A 2 ⊓ U θ 1) = 1 := by
    rw [side_signal21]; apply finrank_vspan
    intro a b h
    have h0 := congrFun h 0
    ext j; fin_cases j
    simpa [Fintype.linearCombination_apply,Fin.sum_univ_succ] using h0
  fin_cases i <;> fin_cases j <;> simp_all [side_signal01,side_signal02 θ hθ,
    side_signal10,side_signal20,h12,h21]

lemma rank_conditions (θ : K) (h0 : θ ≠ 0) (h1 : θ ≠ 1) :
    RankConditions (task θ) ⊤ ![1,2,2] ![2,3,3] := by
  apply NonzeroFamilyRanks.rankConditions_of_intersection_dimensions
  · exact side_dimension
  · exact signal_dimension θ
  · intro i j hij
    simpa [V] using pair_dimension θ i j hij
  · simp [task,triple_zero θ h1,V]
  · intro i j hij
    simpa [V] using side_signal_dimension θ h0 i j hij
  · intro i; simp [task,triple_zero θ h1]

/-- All fifteen entries of the full literal four-dimensional task. -/
theorem full_profile (θ : K) (h0 : θ ≠ 0) (h1 : θ ≠ 1) :
    (∀ r : Fin 6, entry (task θ) (.inl r) = 1) ∧
    (∀ i ell : Three, 2 * entry (task θ) (.inr (i,ell)) = 3) := by
  have hr : RankConditions (task θ) ⊤ (fullSide .R0 1) (fullSignal .R0 1) := by
    simpa [fullSide,fullSignal] using rank_conditions θ h0 h1
  have hd : finrank K (⊤ : Submodule K (V K)) = fullAmbient .R0 1 := by
    simp [V,fullAmbient]
  constructor
  · intro r
    have h := full_first_entries (task θ) ⊤ .R0 1 (by decide) hd hr r
    fin_cases r <;> simpa [fullFirst] using h
  · intro i ell
    simpa [doubledSecond] using full_second_entries (task θ) ⊤ .R0 1 (by decide) hd hr i ell

def wform : V K →ₗ[K] K := LinearMap.proj 3

lemma P_eq_kernel : (P : Submodule K (V K)) = LinearMap.ker wform := by
  ext v; simp [mem_P,LinearMap.mem_ker,wform]

/-- The source's form and its actual side relation, including signs. -/
theorem relation_certificate :
    (![1,0,0,0] : V K) ∈ A 0 ∧ (![0,0,0,1] : V K) ∈ A 1 ∧
    (![-1,0,0,-1] : V K) ∈ A 2 ∧
    (![1,0,0,0] : V K) + ![0,0,0,1] + ![-1,0,0,-1] = 0 ∧
    wform (![1,0,0,0] : V K) = 0 ∧ wform (![0,0,0,1] : V K) = 1 ∧
    wform (![-1,0,0,-1] : V K) = -1 := by
  refine ⟨by simp [mem_A0],by simp [mem_A1],by simp [mem_A2],?_,rfl,rfl,rfl⟩
  ext j; fin_cases j <;> simp

/-- Actual local generation and feasibility of the displayed hyperplane. -/
theorem relay (θ : K) : (task θ).LocallyGenerated P ∧ (task θ).RelayFeasible P := by
  rw [P_eq_kernel]
  apply NonzeroDefectRelays.hyperplane_relay (task θ) wform
  · exact sides_span
  · intro v hv
    change v ∈ U θ 0 at hv
    have hv3 := (mem_U0 θ v).mp hv
    exact hv3.2
  · exact relation_certificate.1
  · exact relation_certificate.2.1
  · exact relation_certificate.2.2.1
  · exact relation_certificate.2.2.2.1
  · simp [wform]

end R0

namespace D
abbrev V (K : Type*) := Fin 3 → K

def A : Three → Submodule K (V K) :=
  ![vspan ![![1,0,0]], vspan ![![0,1,0]], vspan ![![0,0,1]]]

def U (θ : K) : Three → Submodule K (V K) :=
  ![vspan ![![1,0,0],![0,1,1]], vspan ![![0,1,0],![1,0,1]],
    vspan ![![0,0,1],![1,θ,0]]]

lemma mem_A0 (v : V K) : v ∈ A 0 ↔ v 1 = 0 ∧ v 2 = 0 := by
  change v ∈ vspan _ ↔ _
  rw [mem_vspan]
  constructor
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ]
  · rintro ⟨ha,hb⟩
    refine ⟨![v 0], ?_⟩
    ext j; fin_cases j <;> simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,ha,hb]

lemma mem_A1 (v : V K) : v ∈ A 1 ↔ v 0 = 0 ∧ v 2 = 0 := by
  change v ∈ vspan _ ↔ _
  rw [mem_vspan]
  constructor
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ]
  · rintro ⟨ha,hb⟩
    refine ⟨![v 1], ?_⟩
    ext j; fin_cases j <;> simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,ha,hb]

lemma mem_A2 (v : V K) : v ∈ A 2 ↔ v 0 = 0 ∧ v 1 = 0 := by
  change v ∈ vspan _ ↔ _
  rw [mem_vspan]
  constructor
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ]
  · rintro ⟨ha,hb⟩
    refine ⟨![v 2], ?_⟩
    ext j; fin_cases j <;> simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,ha,hb]

lemma mem_U0 (θ : K) (v : V K) : v ∈ U θ 0 ↔ v 2 = v 1 := by
  change v ∈ vspan _ ↔ _
  rw [mem_vspan]
  constructor
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ,mul_comm]
  · intro h
    refine ⟨![v 0,v 1], ?_⟩
    ext j; fin_cases j <;> simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,h,mul_comm]

lemma mem_U1 (θ : K) (v : V K) : v ∈ U θ 1 ↔ v 2 = v 0 := by
  change v ∈ vspan _ ↔ _
  rw [mem_vspan]
  constructor
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ,mul_comm]
  · intro h
    refine ⟨![v 1,v 0], ?_⟩
    ext j; fin_cases j <;> simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,h,mul_comm]

lemma mem_U2 (θ : K) (v : V K) : v ∈ U θ 2 ↔ v 1 = θ*v 0 := by
  change v ∈ vspan _ ↔ _
  rw [mem_vspan]
  constructor
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply, Fin.sum_univ_succ,mul_comm]
  · intro h
    refine ⟨![v 2,v 0], ?_⟩
    ext j; fin_cases j <;> simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,h,mul_comm]

lemma side_dimension (i : Three) : finrank K ↥(A (K := K) i) = 1 := by
  fin_cases i <;> change finrank K (vspan _) = _ <;> apply finrank_vspan
  all_goals
    intro a b h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    ext j; fin_cases j
    simp_all [Fintype.linearCombination_apply, Fin.sum_univ_succ]

lemma signal_dimension (θ : K) (i : Three) : finrank K ↥(U θ i) = 2 := by
  fin_cases i <;> change finrank K (vspan _) = _ <;> apply finrank_vspan
  all_goals
    intro a b h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    ext j; fin_cases j <;>
      simp_all [Fintype.linearCombination_apply, Fin.sum_univ_succ]

lemma pair01 (θ : K) : U θ 0 ⊓ U θ 1 = vspan ![![1,1,1]] := by
  ext v
  rw [Submodule.mem_inf,mem_U0,mem_U1,mem_vspan]
  constructor
  · rintro ⟨h21,h20⟩
    refine ⟨![v 0], ?_⟩
    ext j; fin_cases j <;> simp_all [Fintype.linearCombination_apply,Fin.sum_univ_succ]
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply,Fin.sum_univ_succ]

lemma pair02 (θ : K) : U θ 0 ⊓ U θ 2 = vspan ![![1,θ,θ]] := by
  ext v
  rw [Submodule.mem_inf,mem_U0,mem_U2,mem_vspan]
  constructor
  · rintro ⟨h21,h1⟩
    refine ⟨![v 0], ?_⟩
    ext j; fin_cases j <;> simp_all [Fintype.linearCombination_apply,Fin.sum_univ_succ,mul_comm]
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,mul_comm]

lemma pair12 (θ : K) : U θ 1 ⊓ U θ 2 = vspan ![![1,θ,1]] := by
  ext v
  rw [Submodule.mem_inf,mem_U1,mem_U2,mem_vspan]
  constructor
  · rintro ⟨h20,h1⟩
    refine ⟨![v 0], ?_⟩
    ext j; fin_cases j <;> simp_all [Fintype.linearCombination_apply,Fin.sum_univ_succ,mul_comm]
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,mul_comm]

lemma pair_dimension (θ : K) (i j : Three) (hij : i ≠ j) :
    finrank K ↥(U θ i ⊓ U θ j) = 1 := by
  have h01 : finrank K ↥(U θ 0 ⊓ U θ 1) = 1 := by
    rw [pair01]; apply finrank_vspan
    intro a b h
    have h0 := congrFun h 0
    ext j; fin_cases j
    simpa [Fintype.linearCombination_apply,Fin.sum_univ_succ] using h0
  have h02 : finrank K ↥(U θ 0 ⊓ U θ 2) = 1 := by
    rw [pair02]; apply finrank_vspan
    intro a b h
    have h0 := congrFun h 0
    ext j; fin_cases j
    simpa [Fintype.linearCombination_apply,Fin.sum_univ_succ] using h0
  have h12 : finrank K ↥(U θ 1 ⊓ U θ 2) = 1 := by
    rw [pair12]; apply finrank_vspan
    intro a b h
    have h0 := congrFun h 0
    ext j; fin_cases j
    simpa [Fintype.linearCombination_apply,Fin.sum_univ_succ] using h0
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals rw [inf_comm]; assumption

lemma triple_zero (θ : K) (hθ : θ ≠ 1) : U θ 0 ⊓ U θ 1 ⊓ U θ 2 = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  rw [Submodule.mem_inf,Submodule.mem_inf,mem_U0,mem_U1,mem_U2] at hv
  rcases hv with ⟨⟨h21,h20⟩,h1⟩
  have hz : (θ-1)*v 0 = 0 := by linear_combination -h1+h20-h21
  have h0 : v 0 = 0 := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hθ)
  change v = 0
  ext j; fin_cases j <;> simp_all

lemma side_le_signal (θ : K) (i : Three) : A i ≤ U θ i := by
  fin_cases i <;> intro v hv
  · change v ∈ A 0 at hv; change v ∈ U θ 0
    rw [mem_A0] at hv; rw [mem_U0]; rcases hv with ⟨h1,h2⟩; simp_all
  · change v ∈ A 1 at hv; change v ∈ U θ 1
    rw [mem_A1] at hv; rw [mem_U1]; rcases hv with ⟨h0,h2⟩; simp_all
  · change v ∈ A 2 at hv; change v ∈ U θ 2
    rw [mem_A2] at hv; rw [mem_U2]; rcases hv with ⟨h0,h1⟩; simp_all

lemma sides_span : (⨆ i, A (K := K) i) = ⊤ := by
  rw [three_iSup]
  apply top_unique
  intro v _
  refine Submodule.mem_sup.mpr ⟨![v 0,v 1,0], ?_, ![0,0,v 2], ?_, ?_⟩
  · refine Submodule.mem_sup.mpr ⟨![v 0,0,0], ?_, ![0,v 1,0], ?_, ?_⟩
    · simp [mem_A0]
    · simp [mem_A1]
    · ext j; fin_cases j <;> simp
  · simp [mem_A2]
  · ext j; fin_cases j <;> simp

def task (θ : K) : Task K (V K) where
  A := A
  U := U θ
  side_le_signal := side_le_signal θ
  feasible i := by rw [sides_span]; exact le_top

lemma side_signal_zero (θ : K) (hθ : θ ≠ 0) (i j : Three) (hij : i ≠ j) :
    A j ⊓ U θ i = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  have hc : v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 := by
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals
      simp only [Submodule.mem_inf] at hv
      rcases hv with ⟨ha,hu⟩
      dsimp only at ha hu
      first
      | replace ha := (mem_A0 v).mp ha
      | replace ha := (mem_A1 v).mp ha
      | replace ha := (mem_A2 v).mp ha
      first
      | replace hu := (mem_U0 θ v).mp hu
      | replace hu := (mem_U1 θ v).mp hu
      | replace hu := (mem_U2 θ v).mp hu
      rcases ha with ⟨ha,hb⟩
      simp_all [hθ]
  change v = 0
  ext j; fin_cases j <;> simp_all

lemma rank_conditions (θ : K) (h0 : θ ≠ 0) (h1 : θ ≠ 1) :
    RankConditions (task θ) ⊤ (fun _ => 1) (fun _ => 2) := by
  apply NonzeroFamilyRanks.rankConditions_of_intersection_dimensions
  · exact side_dimension
  · exact signal_dimension θ
  · intro i j hij; simp [task,pair_dimension θ i j hij,V]
  · simp [task,triple_zero θ h1,V]
  · intro i j hij; simp [task,side_signal_zero θ h0 i j hij,V]
  · intro i; simp [task,triple_zero θ h1]

/-- The literal three-dimensional block contributes one to each first entry
and three to each doubled second entry. -/
theorem profile (θ : K) (h0 : θ ≠ 0) (h1 : θ ≠ 1) :
    (∀ r : Fin 6, entry (task θ) (.inl r) = 1) ∧
    (∀ i ell : Three, 2 * entry (task θ) (.inr (i,ell)) = 3) := by
  have hr := rank_conditions θ h0 h1
  constructor
  · intro r
    change firstEntry (task θ) (firstOrder r).1 (firstOrder r).2.1 (firstOrder r).2.2 = _
    rw [firstEntry_formula (task θ) ⊤ _ _ hr _ _ _
      (by fin_cases r <;> decide) (by fin_cases r <;> decide) (by fin_cases r <;> decide)]
    norm_num [V]
  · intro i ell
    change 2 * secondEntry (task θ) i (i+1) (i+2) ell = _
    rw [secondEntry_formula (task θ) ⊤ _ _ hr _ _ _ _
      (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    norm_num [V]

end D

/-- The fixed literal coordinate inclusion of the D block as the R₀ relay. -/
def embed : D.V K →ₗ[K] R0.V K where
  toFun v := ![v 0,v 1,v 2,0]
  map_add' v w := by ext j; fin_cases j <;> simp
  map_smul' c v := by ext j; fin_cases j <;> simp

lemma embed_injective : Function.Injective (embed (K := K)) := by
  intro v w h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  ext j; fin_cases j <;> simp_all [embed]

lemma mem_map_embed (S : Submodule K (D.V K)) (w : R0.V K) :
    w ∈ S.map embed ↔ w 3 = 0 ∧ ![w 0,w 1,w 2] ∈ S := by
  constructor
  · rintro ⟨v,hv,rfl⟩
    have he : ![v 0,v 1,v 2] = v := by ext j; fin_cases j <;> rfl
    simpa [embed,he] using And.intro (rfl : (0 : K) = 0) hv
  · rintro ⟨h3,hS⟩
    refine ⟨![w 0,w 1,w 2],hS,?_⟩
    ext j; fin_cases j <;> simp [embed,h3]

lemma map_D_side0 : (D.A (K := K) 0).map embed = R0.A 0 ⊓ R0.P := by
  ext w
  rw [mem_map_embed,Submodule.mem_inf,D.mem_A0,R0.mem_A0,R0.mem_P]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  constructor
  · rintro ⟨h3,ha,hb⟩; simp_all
  · rintro ⟨ha,h3⟩; rcases ha with ⟨ha,hb⟩; simp_all

lemma map_D_side1 : (D.A (K := K) 1).map embed = R0.A 1 ⊓ R0.P := by
  ext w
  rw [mem_map_embed,Submodule.mem_inf,D.mem_A1,R0.mem_A1,R0.mem_P]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  constructor
  · rintro ⟨h3,ha,hb⟩; simp_all
  · rintro ⟨ha,h3⟩; rcases ha with ⟨ha,hb⟩; simp_all

lemma map_D_side2 : (D.A (K := K) 2).map embed = R0.A 2 ⊓ R0.P := by
  ext w
  rw [mem_map_embed,Submodule.mem_inf,D.mem_A2,R0.mem_A2,R0.mem_P]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  constructor
  · rintro ⟨h3,ha,hb⟩; simp_all
  · rintro ⟨ha,h3⟩; rcases ha with ⟨ha,hb⟩; simp_all

lemma map_D_signal0 (θ : K) : (D.U θ 0).map embed = R0.U θ 0 ⊓ R0.P := by
  ext w
  rw [mem_map_embed,Submodule.mem_inf,D.mem_U0,R0.mem_U0,R0.mem_P]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  constructor
  · rintro ⟨h3,hU⟩; simp_all
  · rintro ⟨hU,h3⟩; simp_all

lemma map_D_signal1 (θ : K) : (D.U θ 1).map embed = R0.U θ 1 ⊓ R0.P := by
  ext w
  rw [mem_map_embed,Submodule.mem_inf,D.mem_U1,R0.mem_U1,R0.mem_P]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  constructor
  · rintro ⟨h3,hU⟩; simp_all
  · rintro ⟨hU,h3⟩; simp_all

lemma map_D_signal2 (θ : K) : (D.U θ 2).map embed = R0.U θ 2 ⊓ R0.P := by
  ext w
  rw [mem_map_embed,Submodule.mem_inf,D.mem_U2,R0.mem_U2,R0.mem_P]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  constructor
  · rintro ⟨h3,hU⟩; simp_all
  · rintro ⟨hU,h3⟩; simp_all

lemma map_D_side (i : Three) : (D.A (K := K) i).map embed = R0.A i ⊓ R0.P := by
  fin_cases i
  · exact map_D_side0
  · exact map_D_side1
  · exact map_D_side2

lemma map_D_signal (θ : K) (i : Three) : (D.U θ i).map embed = R0.U θ i ⊓ R0.P := by
  fin_cases i
  · exact map_D_signal0 θ
  · exact map_D_signal1 θ
  · exact map_D_signal2 θ

/-- Equality of actual tasks, rather than equality of prescribed rank profiles. -/
theorem induced_eq_image_D (θ : K) :
    NonzeroDefectRelays.inducedTask (R0.task θ) R0.P (R0.relay θ).1 =
      (D.task θ).imageTask embed := by
  have hA : (NonzeroDefectRelays.inducedTask (R0.task θ) R0.P (R0.relay θ).1).A =
      ((D.task θ).imageTask embed).A := by
    funext i; exact (map_D_side i).symm
  have hU : (NonzeroDefectRelays.inducedTask (R0.task θ) R0.P (R0.relay θ).1).U =
      ((D.task θ).imageTask embed).U := by
    funext i; exact (map_D_signal θ i).symm
  cases hs : NonzeroDefectRelays.inducedTask (R0.task θ) R0.P (R0.relay θ).1
  cases ht : (D.task θ).imageTask embed
  simp_all only [Task.mk.injEq]

/-- The literal R₀ relay and the full literal R₀ task have all fifteen entries
claimed by the paper, over every field admitting θ ≠ 0, 1. -/
theorem R0_same_chart_profile (θ : K) (h0 : θ ≠ 0) (h1 : θ ≠ 1) :
    let S := NonzeroDefectRelays.inducedTask (R0.task θ) R0.P (R0.relay θ).1
    (∀ r : Fin 6, entry S (.inl r) = 1) ∧
    (∀ i ell : Three, 2 * entry S (.inr (i,ell)) = 3) ∧
    (∀ r : Index, entry S r = entry (R0.task θ) r) := by
  dsimp only
  rw [induced_eq_image_D]
  simp only [entry_imageTask (D.task θ) embed embed_injective]
  have hD := D.profile θ h0 h1
  have hR := R0.full_profile θ h0 h1
  refine ⟨hD.1,hD.2,?_⟩
  intro r
  rcases r with r | ⟨i,ell⟩
  · rw [hD.1,hR.1]
  · have hd := hD.2 i ell; have hr := hR.2 i ell; linarith


namespace D

lemma pair_conditional_rank (θ : K) (h0 : θ ≠ 0) (h1 : θ ≠ 1)
    (i j : Three) (hij : i ≠ j) : condRank (U θ i ⊓ U θ j) (A j) = 1 := by
  have h := (rank_conditions θ h0 h1).pair_rank i j hij
  simpa [V,task] using h

lemma pairs_span (θ : K) (h0 : θ ≠ 0) (h1 : θ ≠ 1)
    (i j : Three) (hij : i ≠ j) : U θ i ⊔ U θ j = ⊤ :=
  (rank_conditions θ h0 h1).pair_span i j hij

lemma relay (θ : K) : (task θ).LocallyGenerated ⊤ ∧ (task θ).RelayFeasible ⊤ := by
  constructor
  · simpa only [Task.LocallyGenerated,top_inf_eq,task] using sides_span.symm
  · intro i; simp

/-- Appending one actual D block changes the actual fifteen entries by the
source's one-block increment, for any pre-existing task. -/
theorem append_profile {F : Type} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
    (T : Task K F) (θ : K) (h0 : θ ≠ 0) (h1 : θ ≠ 1) :
    (∀ r : Fin 6, entry (directSum T (task θ)) (.inl r) = entry T (.inl r) + 1) ∧
    (∀ i ell : Three, 2 * entry (directSum T (task θ)) (.inr (i,ell)) =
      2 * entry T (.inr (i,ell)) + 3) := by
  have hp := profile θ h0 h1
  constructor
  · intro r; rw [entry_directSum,hp.1]
  · intro i ell; rw [entry_directSum,mul_add,hp.2]

/-- The exact source tuple increment under a direct sum with D. The triple
rank stays fixed; no genericity assumption on the original task is needed. -/
theorem append_dimensions {F : Type} [AddCommGroup F] [Module K F]
    [FiniteDimensional K F] (T : Task K F) (θ : K) (h1 : θ ≠ 1) :
    finrank K (F × V K) = finrank K F + 3 ∧
    (∀ i, finrank K ((directSum T (task θ)).A i) = finrank K (T.A i) + 1) ∧
    (∀ i, finrank K ((directSum T (task θ)).U i) = finrank K (T.U i) + 2) ∧
    (∀ i j, i ≠ j → finrank K ↥((directSum T (task θ)).U i ⊓
      (directSum T (task θ)).U j) = finrank K ↥(T.U i ⊓ T.U j) + 1) ∧
    finrank K ↥((directSum T (task θ)).U 0 ⊓ (directSum T (task θ)).U 1 ⊓
      (directSum T (task θ)).U 2) = finrank K ↥(T.U 0 ⊓ T.U 1 ⊓ T.U 2) ∧
    (∀ i, condRank ((directSum T (task θ)).U i) ((directSum T (task θ)).A i) =
      condRank (T.U i) (T.A i) + 1) := by
  refine ⟨by simp [finrank_prod,V],?_,?_,?_,?_,?_⟩
  · intro i; simp [directSum,task,finrank_submodule_prod,side_dimension]
  · intro i; simp [directSum,task,finrank_submodule_prod,signal_dimension]
  · intro i j hij
    change finrank K ↥((T.U i).prod (U θ i) ⊓ (T.U j).prod (U θ j)) = _
    rw [Submodule.prod_inf_prod (T.U i) (T.U j) (U θ i) (U θ j),
      finrank_submodule_prod,pair_dimension θ i j hij]
  · change finrank K ↥((T.U 0).prod (U θ 0) ⊓ (T.U 1).prod (U θ 1) ⊓
      (T.U 2).prod (U θ 2)) = _
    rw [Submodule.prod_inf_prod (T.U 0) (T.U 1) (U θ 0) (U θ 1),
      Submodule.prod_inf_prod (T.U 0 ⊓ T.U 1) (T.U 2) (U θ 0 ⊓ U θ 1) (U θ 2),
      finrank_submodule_prod,triple_zero θ h1]
    simp
  · intro i
    rw [show (directSum T (task θ)).U i = (T.U i).prod (U θ i) from rfl,
      show (directSum T (task θ)).A i = (T.A i).prod (A i) from rfl,condRank_prod]
    have hd : condRank (U θ i) (A i) = 1 := by
      rw [condRank,sup_eq_right.mpr (side_le_signal θ i),signal_dimension,side_dimension]
    rw [hd]

/-- Pair and triple conditional ranks have exactly the source's increments. -/
theorem append_conditional_ranks {F : Type} [AddCommGroup F] [Module K F]
    [FiniteDimensional K F] (T : Task K F) (θ : K) (h0 : θ ≠ 0) (h1 : θ ≠ 1) :
    (∀ i j, i ≠ j → condRank ((directSum T (task θ)).U i ⊓
      (directSum T (task θ)).U j) ((directSum T (task θ)).A j) =
        condRank (T.U i ⊓ T.U j) (T.A j) + 1) ∧
    (∀ ell, condRank ((directSum T (task θ)).U 0 ⊓ (directSum T (task θ)).U 1 ⊓
      (directSum T (task θ)).U 2) ((directSum T (task θ)).A ell) =
        condRank (T.U 0 ⊓ T.U 1 ⊓ T.U 2) (T.A ell)) := by
  constructor
  · intro i j hij
    simp [directSum,task,Submodule.prod_inf_prod,condRank_prod,pair_conditional_rank θ h0 h1 i j hij]
  · intro ell
    change condRank ((T.U 0).prod (U θ 0) ⊓ (T.U 1).prod (U θ 1) ⊓
      (T.U 2).prod (U θ 2)) ((T.A ell).prod (A ell)) = _
    rw [Submodule.prod_inf_prod (T.U 0) (T.U 1) (U θ 0) (U θ 1),
      Submodule.prod_inf_prod (T.U 0 ⊓ T.U 1) (T.U 2) (U θ 0 ⊓ U θ 1) (U θ 2),
      condRank_prod,triple_zero θ h1]
    have hz : condRank (⊥ : Submodule K (V K)) (A ell) = 0 := by
      rw [condRank,sup_bot_eq,Nat.sub_self]
    rw [hz,add_zero]

end D

namespace R0

lemma pair_conditional_rank (θ : K) (h0 : θ ≠ 0) (h1 : θ ≠ 1)
    (i j : Three) (hij : i ≠ j) : condRank (U θ i ⊓ U θ j) (A j) = 1 := by
  have h := (rank_conditions θ h0 h1).pair_rank i j hij
  fin_cases i <;> fin_cases j <;> simp_all [V,task]

lemma pairs_span (θ : K) (h0 : θ ≠ 0) (h1 : θ ≠ 1)
    (i j : Three) (hij : i ≠ j) : U θ i ⊔ U θ j = ⊤ :=
  (rank_conditions θ h0 h1).pair_span i j hij

lemma relay_side_dimension (i : Three) : finrank K ↥(P ⊓ A (K := K) i) = 1 := by
  rw [inf_comm,← map_D_side,finrank_map_injective (embed (K := K)) embed_injective,D.side_dimension]

lemma relay_signal_dimension (θ : K) (i : Three) : finrank K ↥(P ⊓ U θ i) = 2 := by
  rw [inf_comm,← map_D_signal,finrank_map_injective (embed (K := K)) embed_injective,D.signal_dimension]

lemma relay_local_upload_dimension :
    (∑ i : Three, finrank K ↥(P ⊓ A (K := K) i)) = finrank K (P : Submodule K (V K)) := by
  simp [relay_side_dimension,relay_dimension,Fintype.card_fin]

lemma relay_pair_dimension (θ : K) (i j : Three) (hij : i ≠ j) :
    finrank K ↥((U θ i ⊓ P) ⊓ (U θ j ⊓ P)) = 1 := by
  rw [← map_D_signal,← map_D_signal,← Submodule.map_inf embed embed_injective,
    finrank_map_injective (embed (K := K)) embed_injective,D.pair_dimension θ i j hij]

lemma relay_pair_conditional_rank (θ : K) (h0 : θ ≠ 0) (h1 : θ ≠ 1)
    (i j : Three) (hij : i ≠ j) :
    condRank ((U θ i ⊓ P) ⊓ (U θ j ⊓ P)) (A j ⊓ P) = 1 := by
  rw [← map_D_signal,← map_D_signal,← map_D_side,
    ← Submodule.map_inf embed embed_injective,condRank_map_injective (embed (K := K)) embed_injective]
  exact D.pair_conditional_rank θ h0 h1 i j hij

lemma relay_triple_zero (θ : K) (h1 : θ ≠ 1) :
    (U θ 0 ⊓ P) ⊓ (U θ 1 ⊓ P) ⊓ (U θ 2 ⊓ P) = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  have h : v ∈ U θ 0 ⊓ U θ 1 ⊓ U θ 2 := ⟨⟨hv.1.1.1,hv.1.2.1⟩,hv.2.1⟩
  simpa only [triple_zero θ h1] using h

lemma relay_pair01 (θ : K) :
    (U θ 0 ⊓ P) ⊓ (U θ 1 ⊓ P) = vspan ![![1,1,1,0]] := by
  rw [inf_inf_inf_comm,inf_idem,pair01]
  apply inf_eq_left.mpr
  intro v hv
  rw [mem_vspan] at hv
  obtain ⟨c,rfl⟩ := hv
  simp [mem_P,Fintype.linearCombination_apply,Fin.sum_univ_succ]

lemma relay_pair02 (θ : K) :
    (U θ 0 ⊓ P) ⊓ (U θ 2 ⊓ P) = vspan ![![1,θ,θ,0]] := by
  rw [inf_inf_inf_comm,inf_idem,pair02]
  apply inf_eq_left.mpr
  intro v hv
  rw [mem_vspan] at hv
  obtain ⟨c,rfl⟩ := hv
  simp [mem_P,Fintype.linearCombination_apply,Fin.sum_univ_succ]

lemma relay_pair12 (θ : K) :
    (U θ 1 ⊓ P) ⊓ (U θ 2 ⊓ P) = vspan ![![1,θ,1,0]] := by
  ext v
  rw [Submodule.mem_inf,Submodule.mem_inf,Submodule.mem_inf,
    mem_U1,mem_U2,mem_P,mem_vspan]
  constructor
  · rintro ⟨⟨h2,h3⟩,h1,_⟩
    refine ⟨![v 0],?_⟩
    ext j; fin_cases j <;> simp_all [Fintype.linearCombination_apply,Fin.sum_univ_succ,mul_comm]
  · rintro ⟨c,rfl⟩
    simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,mul_comm]

end R0
end UploadBroadcast.LiteralThetaBlocks
