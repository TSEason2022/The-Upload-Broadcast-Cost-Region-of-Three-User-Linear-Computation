import UploadBroadcast.FiniteMonoidPower
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# A nilpotent operator with an indecomposable marked kernel line

A finite-field argument constructs a commuting finite-rank map from a maximal
nilpotent chain. A positive idempotent power extracts its cyclic summand. This
proves the marked indecomposable case without assuming Jordan classification.
-/
namespace UploadBroadcast.MarkedNilpotent
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The finite convolution associated with a chain and a linear functional. -/
def chainMap (N : Module.End K V) (n : ℕ) (v : V) (φ : V →ₗ[K] K) :
    Module.End K V where
  toFun y := ∑ i ∈ Finset.range (n+1), φ ((N^i) y) • (N^(n-i)) v
  map_add' y z := by simp [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' a y := by simp [map_smul, smul_smul, Finset.smul_sum, mul_comm]

@[simp] lemma chainMap_apply (N : Module.End K V) (n : ℕ) (v : V)
    (φ : V →ₗ[K] K) (y : V) :
    chainMap N n v φ y = ∑ i ∈ Finset.range (n+1), φ ((N^i) y) • (N^(n-i)) v := rfl

lemma pow_apply_eq_zero_of_apply_eq_zero (N : Module.End K V) {y : V}
    (hy : N y = 0) {i : ℕ} (hi : 0 < i) : (N^i) y = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  simp [pow_succ, Module.End.mul_apply, hy]

/-- On the kernel, the convolution has rank at most one. -/
theorem chainMap_on_kernel (N : Module.End K V) (n : ℕ) (v : V)
    (φ : V →ₗ[K] K) {y : V} (hy : N y = 0) :
    chainMap N n v φ y = φ y • (N^n) v := by
  rw [chainMap_apply, Finset.sum_range_succ']
  have hz : ∑ i ∈ Finset.range n,
      φ ((N^(i+1)) y) • (N^(n-(i+1))) v = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [pow_apply_eq_zero_of_apply_eq_zero N hy (by omega), map_zero, zero_smul]
  simp only [hz, zero_add, pow_zero, Module.End.one_apply, Nat.sub_zero]

/-- The two boundary terms vanish at the global nilpotence bound. -/
theorem chainMap_commutes (N : Module.End K V) (n : ℕ) (v : V)
    (φ : V →ₗ[K] K) (hN : N^(n+1) = 0) :
    Commute (chainMap N n v φ) N := by
  apply LinearMap.ext
  intro y
  change chainMap N n v φ (N y) = N (chainMap N n v φ y)
  change (∑ i ∈ Finset.range (n+1), φ ((N^i) (N y)) • (N^(n-i)) v) = _
  simp only [chainMap_apply, map_sum, map_smul]
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have hl : φ ((N^n) (N y)) • (N^(n-n)) v = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ, hN]
    simp
  have hr : φ ((N^0) y) • N ((N^(n-0)) v) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_zero, hN]
    simp
  rw [hl, hr, add_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  rw [← Module.End.mul_apply, ← pow_succ,
    ← Module.End.mul_apply, ← pow_succ']
  congr 3
  omega

/-- Every value of the convolution is in the chain span. -/
theorem chainMap_mem_span (N : Module.End K V) (n : ℕ) (v : V)
    (φ : V →ₗ[K] K) (y : V) :
    chainMap N n v φ y ∈
      Submodule.span K (Set.range (fun i : Fin (n+1) => (N^i.val) v)) := by
  rw [chainMap_apply]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨n-i, by omega⟩, rfl⟩

/-- Preservation of a generating vector is preservation of its line. -/
lemma map_mem_line (P : Module.End K V) (l : V)
    (hP : P l ∈ Submodule.span K {l}) {x : V}
    (hx : x ∈ Submodule.span K {l}) : P x ∈ Submodule.span K {l} := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul]
  exact Submodule.smul_mem _ a hP

lemma pow_mem_line (P : Module.End K V) (l : V)
    (hP : P l ∈ Submodule.span K {l}) (r : ℕ) {x : V}
    (hx : x ∈ Submodule.span K {l}) : (P^r) x ∈ Submodule.span K {l} := by
  induction r with
  | zero => simpa using hx
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact map_mem_line P l hP ih

/-- Choose a functional detecting a vector while either its image vector lies
on the marked line or the functional kills that line. -/
lemma exists_marked_functional (b l : V) (hb : b ≠ 0) :
    ∃ φ : V →ₗ[K] K, φ b = 1 ∧ (b ∈ Submodule.span K {l} ∨ φ l = 0) := by
  classical
  by_cases hbl : b ∈ Submodule.span K {l}
  · obtain ⟨φ, hφ, _⟩ :=
      (Submodule.exists_dual_map_eq_bot_of_nmem (p := (⊥ : Submodule K V))
        (by simpa using hb) inferInstance)
    refine ⟨(φ b)⁻¹ • φ, ?_, Or.inl hbl⟩
    simp [LinearMap.smul_apply, smul_eq_mul, hφ]
  · obtain ⟨φ, hφ, hz⟩ :=
      Submodule.exists_dual_map_eq_bot_of_nmem hbl inferInstance
    have hφl : φ l = 0 := by
      have hh : φ l ∈ (Submodule.span K {l}).map φ :=
        Submodule.mem_map.mpr ⟨l, Submodule.mem_span_singleton_self l, rfl⟩
      simpa [hz] using hh
    refine ⟨(φ b)⁻¹ • φ, ?_, Or.inr ?_⟩
    · simp [LinearMap.smul_apply, smul_eq_mul, hφ]
    · simp [LinearMap.smul_apply, hφl]

/-- A maximal chain exists for every nonzero space with a nilpotent operator. -/
lemma exists_maximal_chain (N : Module.End K V) (hN : IsNilpotent N)
    (l : V) (hl : l ≠ 0) :
    ∃ (n : ℕ) (v : V), N^(n+1) = 0 ∧ (N^n) v ≠ 0 := by
  classical
  have hpos : 0 < Nat.find hN := by
    by_contra hh
    have hz : Nat.find hN = 0 := by omega
    have h := Nat.find_spec hN
    rw [hz, pow_zero] at h
    exact hl (by simpa using congrArg (fun f : Module.End K V => f l) h)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hlast : N^(n+1) = 0 := by simpa [hn] using Nat.find_spec hN
  have hprev : N^n ≠ 0 := Nat.find_min hN (by omega)
  obtain ⟨v, hv⟩ : ∃ v : V, (N^n) v ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hprev (LinearMap.ext hh)
  exact ⟨n, v, hlast, hv⟩

/-- The single chain's convolution has an identity power under the marked
indecomposability criterion. -/
theorem exists_chainMap_pow_eq_one [Finite K] [FiniteDimensional K V]
    (N : Module.End K V) (hN : IsNilpotent N) (l : V) (hl : l ≠ 0)
    (hNl : N l = 0)
    (hind : ∀ P : Module.End K V, Commute P N →
      P l ∈ Submodule.span K {l} → (∀ x, P (P x) = P x) → P = 0 ∨ P = 1) :
    ∃ (n : ℕ) (v : V) (φ : V →ₗ[K] K) (r : ℕ),
      N^(n+1) = 0 ∧ (N^n) v ≠ 0 ∧ 0 < r ∧
      (chainMap N n v φ)^r = 1 ∧ (N^n) v ∈ Submodule.span K {l} := by
  classical
  letI : Finite V := Module.finite_of_finite K
  letI : Finite (Module.End K V) := Finite.of_injective
    (fun f : Module.End K V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨n, v, hn, hv⟩ := exists_maximal_chain N hN l hl
  obtain ⟨φ, hφ, hmark⟩ := exists_marked_functional (K := K) ((N^n) v) l hv
  let P := chainMap N n v φ
  have hNb : N ((N^n) v) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ', hn]
    rfl
  have hPb : P ((N^n) v) = (N^n) v := by
    rw [chainMap_on_kernel N n v φ hNb, hφ, one_smul]
  have hpowb (r : ℕ) : (P^r) ((N^n) v) = (N^n) v := by
    induction r with
    | zero => rfl
    | succ r ih => rw [pow_succ', Module.End.mul_apply, ih, hPb]
  have hPl : P l ∈ Submodule.span K {l} := by
    change chainMap N n v φ l ∈ _
    rw [chainMap_on_kernel N n v φ hNl]
    rcases hmark with hmark | hmark
    · exact Submodule.smul_mem _ _ hmark
    · simp [hmark]
  obtain ⟨r, hr, hid⟩ := FiniteMonoidPower.exists_pos_pow_add_eq P
  have hid' : ∀ x, (P^r) ((P^r) x) = (P^r) x := by
    intro x
    simpa only [pow_add, Module.End.mul_apply] using
      congrArg (fun f : Module.End K V => f x) hid
  obtain hz | ho := hind (P^r) ((chainMap_commutes N n v φ hn).pow_left r)
    (pow_mem_line P l hPl r (Submodule.mem_span_singleton_self l)) hid'
  · have hh := hpowb r
    rw [hz] at hh
    exact False.elim (hv hh.symm)
  · refine ⟨n, v, φ, r, hn, hv, hr, ho, ?_⟩
    rcases hmark with hmark | hmark
    · exact hmark
    · exfalso
      have hzero : P l = 0 := by
        rw [chainMap_on_kernel N n v φ hNl, hmark, zero_smul]
      have hzero' := pow_apply_eq_zero_of_apply_eq_zero P hzero hr
      rw [ho] at hzero'
      exact hl hzero'

/-- A marked indecomposable nilpotent operator is generated by one maximal
chain, and its entire kernel is precisely the marked line. -/
theorem single_chain_and_kernel [Finite K] [FiniteDimensional K V]
    (N : Module.End K V) (hN : IsNilpotent N) (l : V) (hl : l ≠ 0)
    (hNl : N l = 0)
    (hind : ∀ P : Module.End K V, Commute P N →
      P l ∈ Submodule.span K {l} → (∀ x, P (P x) = P x) → P = 0 ∨ P = 1) :
    (∃ (n : ℕ) (v : V), N^(n+1) = 0 ∧ (N^n) v ≠ 0 ∧
      Submodule.span K (Set.range (fun i : Fin (n+1) => (N^i.val) v)) = ⊤) ∧
    LinearMap.ker N = Submodule.span K {l} := by
  obtain ⟨n, v, φ, r, hn, hv, hr, hpow, hb⟩ :=
    exists_chainMap_pow_eq_one N hN l hl hNl hind
  let P := chainMap N n v φ
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hPl : P l ∈ Submodule.span K {l} := by
    rw [chainMap_on_kernel N n v φ hNl]
    exact Submodule.smul_mem _ _ hb
  constructor
  · refine ⟨n, v, hn, hv, eq_top_iff.mpr ?_⟩
    intro x _
    have hx : P ((P^s) x) = x := by
      have := congrArg (fun f : Module.End K V => f x) hpow
      simpa only [pow_succ', Module.End.mul_apply, Module.End.one_apply] using this
    rw [← hx]
    exact chainMap_mem_span N n v φ _
  · apply le_antisymm
    · intro x hx
      have hPx : P x ∈ Submodule.span K {l} := by
        rw [chainMap_on_kernel N n v φ hx]
        exact Submodule.smul_mem _ _ hb
      have he : (P^s) (P x) = x := by
        have := congrArg (fun f : Module.End K V => f x) hpow
        simpa only [pow_succ, Module.End.mul_apply, Module.End.one_apply] using this
      rw [← he]
      exact pow_mem_line P l hPl s hPx
    · exact Submodule.span_le.mpr (by simpa [LinearMap.mem_ker] using hNl)

/-- A globally nilpotent operator vanishes at the dimension of its space. -/
lemma nilpotent_pow_finrank [FiniteDimensional K V]
    (N : Module.End K V) (hN : IsNilpotent N) :
    N ^ Module.finrank K V = 0 := by
  obtain ⟨m, hm⟩ := hN
  apply LinearMap.ext
  intro x
  exact Module.End.ker_pow_le_ker_pow_finrank N m (by simp [hm])

/-- A spanning maximal chain has exactly the dimension of the space. -/
lemma maximal_chain_finrank [FiniteDimensional K V]
    (N : Module.End K V) (n : ℕ) (v : V)
    (hn : N^(n+1) = 0) (hv : (N^n) v ≠ 0)
    (hspan : Submodule.span K
      (Set.range (fun i : Fin (n+1) => (N^i.val) v)) = ⊤) :
    Module.finrank K V = n+1 := by
  classical
  have hupper : Module.finrank K V ≤ n+1 := by
    simpa using finrank_le_of_span_eq_top hspan
  have hlower : n < Module.finrank K V := by
    by_contra h
    have hd : Module.finrank K V ≤ n := by omega
    have hnil := nilpotent_pow_finrank N ⟨n+1, hn⟩
    apply hv
    rw [← Nat.sub_add_cancel hd, pow_add, Module.End.mul_apply, hnil, LinearMap.zero_apply,
      map_zero]
  omega

/-- The chain obtained above is genuinely a basis; this is the one-block Jordan
basis conclusion, rather than only a bound on the kernel dimension. -/
theorem exists_jordan_chain_basis [Finite K] [FiniteDimensional K V]
    (N : Module.End K V) (hN : IsNilpotent N) (l : V) (hl : l ≠ 0)
    (hNl : N l = 0)
    (hind : ∀ P : Module.End K V, Commute P N →
      P l ∈ Submodule.span K {l} → (∀ x, P (P x) = P x) → P = 0 ∨ P = 1) :
    ∃ (n : ℕ) (v : V) (b : Basis (Fin (n+1)) K V),
      (∀ i, b i = (N^i.val) v) ∧
      (∀ i : Fin n, N (b i.castSucc) = b i.succ) ∧
      N (b (Fin.last n)) = 0 ∧
      LinearMap.ker N = Submodule.span K {l} := by
  obtain ⟨⟨n, v, hn, hv, hs⟩, hk⟩ := single_chain_and_kernel N hN l hl hNl hind
  have hd : Fintype.card (Fin (n+1)) = Module.finrank K V := by
    simpa using (maximal_chain_finrank N n v hn hv hs).symm
  let b : Basis (Fin (n+1)) K V :=
    basisOfTopLeSpanOfCardEqFinrank (fun i : Fin (n+1) => (N^i.val) v) hs.ge hd
  have hb (i : Fin (n+1)) : b i = (N^i.val) v :=
    congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ hs.ge hd) i
  refine ⟨n, v, b, hb, ?_, ?_, hk⟩
  · intro i
    rw [hb, hb]
    change N ((N^i.val) v) = (N^(i.val+1)) v
    rw [pow_succ', Module.End.mul_apply]
  · rw [hb]
    simp only [Fin.val_last, ← Module.End.mul_apply, ← pow_succ', hn,
      LinearMap.zero_apply]

#print axioms single_chain_and_kernel
#print axioms exists_jordan_chain_basis

end UploadBroadcast.MarkedNilpotent
