import UploadBroadcast.ResidualUpload
import UploadBroadcast.CommonFunction
import UploadBroadcast.Shannon
import UploadBroadcast.EntropyCoding
import UploadBroadcast.FiniteAlphabetEncoding

/-! Actual finite-alphabet Shannon packaging for the residual upload converse. -/
namespace UploadBroadcast.ResidualConverse
open MeasureTheory ProbabilityTheory
variable {Ω ι : Type*} [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  [Fintype ι] [DecidableEq ι]

omit [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] [Fintype ι] in
/-- Equality of padded observations is precisely equality of their selected coordinates. -/
theorem observe_eq_iff (X : Ω → ι → ℕ) (A : Finset ι) (x y : Ω) :
    Shannon.observe X A x = Shannon.observe X A y ↔ ∀ i ∈ A, X x i = X y i := by
  constructor
  · intro h i hi
    simpa [Shannon.observe,hi] using congrFun h i
  · intro h
    funext i
    by_cases hi : i ∈ A
    · simp [Shannon.observe,hi,h i hi]
    · simp [Shannon.observe,hi]

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Fiber-equivalent finite observations have equal genuine Shannon entropy. -/
theorem entropy_eq_of_fibers {S T : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [MeasurableSpace T] [DiscreteMeasurableSpace T] [Countable S] [Countable T]
    [Nonempty S] [Nonempty T] (f : Ω → S) (g : Ω → T)
    (h : ∀ x y, f x = f y ↔ g x = g y) : entropy f μ = entropy g μ := by
  have hf : Function.FactorsThrough f g := fun x y he => (h x y).mpr he
  have hg : Function.FactorsThrough g f := fun x y he => (h x y).mp he
  obtain ⟨a,ha⟩ := (Function.factorsThrough_iff f).mp hf
  obtain ⟨b,hb⟩ := (Function.factorsThrough_iff g).mp hg
  apply le_antisymm
  · rw [ha]
    exact entropy_comp_le μ Measurable.of_discrete a
  · rw [hb]
    exact entropy_comp_le μ Measurable.of_discrete b

/-- Source-level functional dependencies imply the precise entropy-function
hypotheses used by the common-function theorem. -/
theorem determines_of_coordinates (X : Ω → ι → ℕ) (A B : Finset ι)
    (h : ∀ x y, (∀ i ∈ A, X x i = X y i) → ∀ i ∈ B, X x i = X y i) :
    (Shannon.entropyFunction μ X).Determines A B := by
  apply (Shannon.determines_iff μ X A B).mpr
  have hf : Function.FactorsThrough (Shannon.observe X B) (Shannon.observe X A) := by
    intro x y hxy
    exact (observe_eq_iff X B x y).mpr (h x y ((observe_eq_iff X A x y).mp hxy))
  obtain ⟨f,hf⟩ := (Function.factorsThrough_iff (Shannon.observe X B)).mp hf
  exact condEntropy_zero_of_factor μ _ _ Measurable.of_discrete f hf

/-- The unconditioned common-function lower bound for actual finite source
observations. All hypotheses are pointwise code/recovery statements, except
pairwise independence of the three actual side observations. -/
theorem common_lower_bound
    (W₁ W₂ W₃ M₁ M₂ M₃ T₁ T₂ T₃ Θ : Ω → ℕ)
    (enc₁ : ∀ x y, W₁ x = W₁ y → M₁ x = M₁ y ∧ T₁ x = T₁ y)
    (enc₂ : ∀ x y, W₂ x = W₂ y → M₂ x = M₂ y ∧ T₂ x = T₂ y)
    (enc₃ : ∀ x y, W₃ x = W₃ y → M₃ x = M₃ y ∧ T₃ x = T₃ y)
    (dec₁ : ∀ x y, M₁ x = M₁ y → T₁ x = T₁ y → W₁ x = W₁ y)
    (dec₂ : ∀ x y, M₂ x = M₂ y → T₂ x = T₂ y → W₂ x = W₂ y)
    (dec₃ : ∀ x y, M₃ x = M₃ y → T₃ x = T₃ y → W₃ x = W₃ y)
    (ind₁₂ : IndepFun W₁ W₂ μ) (ind₁₃ : IndepFun W₁ W₃ μ) (ind₂₃ : IndepFun W₂ W₃ μ)
    (tri₃ : ∀ x y, T₁ x = T₁ y → T₂ x = T₂ y → T₃ x = T₃ y)
    (tri₂ : ∀ x y, T₁ x = T₁ y → T₃ x = T₃ y → T₂ x = T₂ y)
    (common₁ : ∀ x y, M₁ x = M₁ y → M₂ x = M₂ y → M₃ x = M₃ y →
      T₁ x = T₁ y → Θ x = Θ y)
    (common₂ : ∀ x y, M₁ x = M₁ y → M₂ x = M₂ y → M₃ x = M₃ y →
      T₂ x = T₂ y → Θ x = Θ y)
    (bridge : ∀ x y, M₁ x = M₁ y → M₂ x = M₂ y → M₃ x = M₃ y →
      Θ x = Θ y → T₃ x = T₃ y → T₁ x = T₁ y) :
    2 * entropy (fun x => (W₁ x,W₂ x,W₃ x)) μ -
      (entropy W₁ μ + entropy W₂ μ + entropy W₃ μ) ≤
      entropy M₁ μ + entropy M₂ μ + entropy M₃ μ := by
  let X : Ω → Fin 10 → ℕ := fun x => ![W₁ x,W₂ x,W₃ x,M₁ x,M₂ x,M₃ x,T₁ x,T₂ x,T₃ x,Θ x]
  let h := Shannon.entropyFunction μ X
  have det (A B : Finset (Fin 10))
      (hh : ∀ x y, (∀ i ∈ A, X x i = X y i) → ∀ i ∈ B, X x i = X y i) :
      h.Determines A B := determines_of_coordinates μ X A B hh
  have e₁ : h.Determines {0} ({3} ∪ {6}) := by
    apply det
    intro x y hh i hi
    have he := enc₁ x y (by simpa [X] using hh 0 (by simp))
    simp only [Finset.mem_union,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simpa [X] using he.1
    · simpa [X] using he.2
  have e₂ : h.Determines {1} ({4} ∪ {7}) := by
    apply det
    intro x y hh i hi
    have he := enc₂ x y (by simpa [X] using hh 1 (by simp))
    simp only [Finset.mem_union,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simpa [X] using he.1
    · simpa [X] using he.2
  have e₃ : h.Determines {2} ({5} ∪ {8}) := by
    apply det
    intro x y hh i hi
    have he := enc₃ x y (by simpa [X] using hh 2 (by simp))
    simp only [Finset.mem_union,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simpa [X] using he.1
    · simpa [X] using he.2
  have d₁ : h.Determines ({3} ∪ {6}) {0} := by
    apply det
    intro x y hh i hi
    have he := dec₁ x y (by simpa [X] using hh 3 (by simp)) (by simpa [X] using hh 6 (by simp))
    have hi' : i = 0 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have d₂ : h.Determines ({4} ∪ {7}) {1} := by
    apply det
    intro x y hh i hi
    have he := dec₂ x y (by simpa [X] using hh 4 (by simp)) (by simpa [X] using hh 7 (by simp))
    have hi' : i = 1 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have d₃ : h.Determines ({5} ∪ {8}) {2} := by
    apply det
    intro x y hh i hi
    have he := dec₃ x y (by simpa [X] using hh 5 (by simp)) (by simpa [X] using hh 8 (by simp))
    have hi' : i = 2 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have t₃ : h.Determines ({6} ∪ {7}) {8} := by
    apply det
    intro x y hh i hi
    have he := tri₃ x y (by simpa [X] using hh 6 (by simp)) (by simpa [X] using hh 7 (by simp))
    have hi' : i = 8 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have t₂ : h.Determines ({6} ∪ {8}) {7} := by
    apply det
    intro x y hh i hi
    have he := tri₂ x y (by simpa [X] using hh 6 (by simp)) (by simpa [X] using hh 8 (by simp))
    have hi' : i = 7 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have c₁ : h.Determines (({3} ∪ {4} ∪ {5}) ∪ {6}) {9} := by
    apply det
    intro x y hh i hi
    have he := common₁ x y (by simpa [X] using hh 3 (by simp))
      (by simpa [X] using hh 4 (by simp)) (by simpa [X] using hh 5 (by simp))
      (by simpa [X] using hh 6 (by simp))
    have hi' : i = 9 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have c₂ : h.Determines (({3} ∪ {4} ∪ {5}) ∪ {7}) {9} := by
    apply det
    intro x y hh i hi
    have he := common₂ x y (by simpa [X] using hh 3 (by simp))
      (by simpa [X] using hh 4 (by simp)) (by simpa [X] using hh 5 (by simp))
      (by simpa [X] using hh 7 (by simp))
    have hi' : i = 9 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have br : h.Determines ((({3} ∪ {4} ∪ {5}) ∪ {9}) ∪ {8}) {6} := by
    apply det
    intro x y hh i hi
    have he := bridge x y (by simpa [X] using hh 3 (by simp))
      (by simpa [X] using hh 4 (by simp)) (by simpa [X] using hh 5 (by simp))
      (by simpa [X] using hh 9 (by simp)) (by simpa [X] using hh 8 (by simp))
    have hi' : i = 6 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have single (i : Fin 10) : h {i} = entropy (fun x => X x i) μ := by
    apply entropy_eq_of_fibers μ
    intro x y
    simp [observe_eq_iff]
  have pair (i j : Fin 10) : h ({i} ∪ {j}) = entropy (fun x => (X x i,X x j)) μ := by
    apply entropy_eq_of_fibers μ
    intro x y
    simp [observe_eq_iff,or_imp,forall_and,and_assoc]
  have triple : h ({0} ∪ {1} ∪ {2}) = entropy (fun x => (W₁ x,W₂ x,W₃ x)) μ := by
    apply entropy_eq_of_fibers μ
    intro x y
    simp [observe_eq_iff,X,or_imp,forall_and,and_assoc]
  have ind (i j : Fin 10) (hi : IndepFun (fun x => X x i) (fun x => X x j) μ) :
      h ({i} ∪ {j}) = h {i} + h {j} := by
    rw [pair,single,single]
    exact hi.entropy_pair_eq_add Measurable.of_discrete Measurable.of_discrete
  have ii₁₂ := ind 0 1 (by simpa [X] using ind₁₂)
  have ii₁₃ := ind 0 2 (by simpa [X] using ind₁₃)
  have ii₂₃ := ind 1 2 (by simpa [X] using ind₂₃)
  have result := h.commonFunction {0} {1} {2} {3} {4} {5} {6} {7} {8} {9}
    e₁ e₂ e₃ d₁ d₂ d₃ ii₁₂ ii₁₃ ii₂₃ t₃ t₂ c₁ c₂ br
  have nn₁ := h.condMutual_nonneg {4} {5} ({3} ∪ {6})
  have nn₂ := h.condMutual_nonneg {3} {5} ({4} ∪ {7})
  have bound : 2 * h ({0} ∪ {1} ∪ {2}) - (h {0} + h {1} + h {2}) ≤ h {3} + h {4} + h {5} := by
    linarith
  simpa only [triple,single,X,Matrix.cons_val_zero,Matrix.cons_val_succ] using bound

/-- Retained-information version of the actual common-function bound. The
conditioning observations are the original sides W₁/W₂, by proved local
mutual determination, exactly as required for the omniscience lift. -/
theorem common_retained_bound
    (W₁ W₂ W₃ M₁ M₂ M₃ T₁ T₂ T₃ Θ : Ω → ℕ)
    (enc₁ : ∀ x y, W₁ x = W₁ y → M₁ x = M₁ y ∧ T₁ x = T₁ y)
    (enc₂ : ∀ x y, W₂ x = W₂ y → M₂ x = M₂ y ∧ T₂ x = T₂ y)
    (enc₃ : ∀ x y, W₃ x = W₃ y → M₃ x = M₃ y ∧ T₃ x = T₃ y)
    (dec₁ : ∀ x y, M₁ x = M₁ y → T₁ x = T₁ y → W₁ x = W₁ y)
    (dec₂ : ∀ x y, M₂ x = M₂ y → T₂ x = T₂ y → W₂ x = W₂ y)
    (dec₃ : ∀ x y, M₃ x = M₃ y → T₃ x = T₃ y → W₃ x = W₃ y)
    (ind₁₂ : IndepFun W₁ W₂ μ) (ind₁₃ : IndepFun W₁ W₃ μ) (ind₂₃ : IndepFun W₂ W₃ μ)
    (tri₃ : ∀ x y, T₁ x = T₁ y → T₂ x = T₂ y → T₃ x = T₃ y)
    (tri₂ : ∀ x y, T₁ x = T₁ y → T₃ x = T₃ y → T₂ x = T₂ y)
    (common₁ : ∀ x y, M₁ x = M₁ y → M₂ x = M₂ y → M₃ x = M₃ y →
      T₁ x = T₁ y → Θ x = Θ y)
    (common₂ : ∀ x y, M₁ x = M₁ y → M₂ x = M₂ y → M₃ x = M₃ y →
      T₂ x = T₂ y → Θ x = Θ y)
    (bridge : ∀ x y, M₁ x = M₁ y → M₂ x = M₂ y → M₃ x = M₃ y →
      Θ x = Θ y → T₃ x = T₃ y → T₁ x = T₁ y) :
    2 * entropy (fun x => (W₁ x,W₂ x,W₃ x)) μ -
      (entropy W₁ μ + entropy W₂ μ + entropy W₃ μ) +
      condMutualInfo M₂ M₃ W₁ μ + condMutualInfo M₁ M₃ W₂ μ ≤
      entropy M₁ μ + entropy M₂ μ + entropy M₃ μ := by
  let X : Ω → Fin 10 → ℕ := fun x => ![W₁ x,W₂ x,W₃ x,M₁ x,M₂ x,M₃ x,T₁ x,T₂ x,T₃ x,Θ x]
  let h := Shannon.entropyFunction μ X
  have det (A B : Finset (Fin 10))
      (hh : ∀ x y, (∀ i ∈ A, X x i = X y i) → ∀ i ∈ B, X x i = X y i) :
      h.Determines A B := determines_of_coordinates μ X A B hh
  have e₁ : h.Determines {0} ({3} ∪ {6}) := by
    apply det
    intro x y hh i hi
    have he := enc₁ x y (by simpa [X] using hh 0 (by simp))
    simp only [Finset.mem_union,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simpa [X] using he.1
    · simpa [X] using he.2
  have e₂ : h.Determines {1} ({4} ∪ {7}) := by
    apply det
    intro x y hh i hi
    have he := enc₂ x y (by simpa [X] using hh 1 (by simp))
    simp only [Finset.mem_union,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simpa [X] using he.1
    · simpa [X] using he.2
  have e₃ : h.Determines {2} ({5} ∪ {8}) := by
    apply det
    intro x y hh i hi
    have he := enc₃ x y (by simpa [X] using hh 2 (by simp))
    simp only [Finset.mem_union,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simpa [X] using he.1
    · simpa [X] using he.2
  have d₁ : h.Determines ({3} ∪ {6}) {0} := by
    apply det
    intro x y hh i hi
    have he := dec₁ x y (by simpa [X] using hh 3 (by simp)) (by simpa [X] using hh 6 (by simp))
    have hi' : i = 0 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have d₂ : h.Determines ({4} ∪ {7}) {1} := by
    apply det
    intro x y hh i hi
    have he := dec₂ x y (by simpa [X] using hh 4 (by simp)) (by simpa [X] using hh 7 (by simp))
    have hi' : i = 1 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have d₃ : h.Determines ({5} ∪ {8}) {2} := by
    apply det
    intro x y hh i hi
    have he := dec₃ x y (by simpa [X] using hh 5 (by simp)) (by simpa [X] using hh 8 (by simp))
    have hi' : i = 2 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have t₃ : h.Determines ({6} ∪ {7}) {8} := by
    apply det
    intro x y hh i hi
    have he := tri₃ x y (by simpa [X] using hh 6 (by simp)) (by simpa [X] using hh 7 (by simp))
    have hi' : i = 8 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have t₂ : h.Determines ({6} ∪ {8}) {7} := by
    apply det
    intro x y hh i hi
    have he := tri₂ x y (by simpa [X] using hh 6 (by simp)) (by simpa [X] using hh 8 (by simp))
    have hi' : i = 7 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have c₁ : h.Determines (({3} ∪ {4} ∪ {5}) ∪ {6}) {9} := by
    apply det
    intro x y hh i hi
    have he := common₁ x y (by simpa [X] using hh 3 (by simp))
      (by simpa [X] using hh 4 (by simp)) (by simpa [X] using hh 5 (by simp))
      (by simpa [X] using hh 6 (by simp))
    have hi' : i = 9 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have c₂ : h.Determines (({3} ∪ {4} ∪ {5}) ∪ {7}) {9} := by
    apply det
    intro x y hh i hi
    have he := common₂ x y (by simpa [X] using hh 3 (by simp))
      (by simpa [X] using hh 4 (by simp)) (by simpa [X] using hh 5 (by simp))
      (by simpa [X] using hh 7 (by simp))
    have hi' : i = 9 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have br : h.Determines ((({3} ∪ {4} ∪ {5}) ∪ {9}) ∪ {8}) {6} := by
    apply det
    intro x y hh i hi
    have he := bridge x y (by simpa [X] using hh 3 (by simp))
      (by simpa [X] using hh 4 (by simp)) (by simpa [X] using hh 5 (by simp))
      (by simpa [X] using hh 9 (by simp)) (by simpa [X] using hh 8 (by simp))
    have hi' : i = 6 := Finset.mem_singleton.mp hi
    subst i
    simpa [X] using he
  have single (i : Fin 10) : h {i} = entropy (fun x => X x i) μ := by
    apply entropy_eq_of_fibers μ
    intro x y
    simp [observe_eq_iff]
  have pair (i j : Fin 10) : h ({i} ∪ {j}) = entropy (fun x => (X x i,X x j)) μ := by
    apply entropy_eq_of_fibers μ
    intro x y
    simp [observe_eq_iff,or_imp,forall_and,and_assoc]
  have triple : h ({0} ∪ {1} ∪ {2}) = entropy (fun x => (W₁ x,W₂ x,W₃ x)) μ := by
    apply entropy_eq_of_fibers μ
    intro x y
    simp [observe_eq_iff,X,or_imp,forall_and,and_assoc]
  have ind (i j : Fin 10) (hi : IndepFun (fun x => X x i) (fun x => X x j) μ) :
      h ({i} ∪ {j}) = h {i} + h {j} := by
    rw [pair,single,single]
    exact hi.entropy_pair_eq_add Measurable.of_discrete Measurable.of_discrete
  have ii₁₂ := ind 0 1 (by simpa [X] using ind₁₂)
  have ii₁₃ := ind 0 2 (by simpa [X] using ind₁₃)
  have ii₂₃ := ind 1 2 (by simpa [X] using ind₂₃)
  have result := h.commonFunction {0} {1} {2} {3} {4} {5} {6} {7} {8} {9}
    e₁ e₂ e₃ d₁ d₂ d₃ ii₁₂ ii₁₃ ii₂₃ t₃ t₂ c₁ c₂ br
  have tri (i j k : Fin 10) : h ({i} ∪ {j} ∪ {k}) =
      entropy (fun x => ((X x i,X x j),X x k)) μ := by
    apply entropy_eq_of_fibers μ
    intro x y
    simp [observe_eq_iff,or_imp,forall_and,and_assoc]
  have cm (i j k : Fin 10) : h.CondMutual {i} {j} {k} =
      condMutualInfo (fun x => X x i) (fun x => X x j) (fun x => X x k) μ := by
    rw [EntropyFunction.CondMutual,pair,pair,single,tri]
    rw [condMutualInfo_eq Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete μ,
      chain_rule'' μ Measurable.of_discrete Measurable.of_discrete,
      chain_rule'' μ Measurable.of_discrete Measurable.of_discrete,
      chain_rule'' μ Measurable.of_discrete Measurable.of_discrete]
    ring
  rw [h.condMutual_congr_condition d₁ e₁, h.condMutual_congr_condition d₂ e₂] at result
  simpa only [triple,single,cm,X,Matrix.cons_val_zero,Matrix.cons_val_succ] using result


@[simp] theorem encode_eq_iff {S : Type*} [Fintype S] (a b : S) :
    FiniteAlphabet.encode a = FiniteAlphabet.encode b ↔ a = b :=
  FiniteAlphabet.encode_injective.eq_iff

omit [Fintype Ω] [IsProbabilityMeasure μ] in
@[simp] theorem entropy_encode {S : Type*} [Fintype S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (f : Ω → S) :
    entropy (FiniteAlphabet.encode ∘ f) μ = entropy f μ :=
  entropy_comp_of_injective μ Measurable.of_discrete _ FiniteAlphabet.encode_injective

omit [Fintype Ω] in
/-- The retained conditional mutual information survives lossless alphabet encoding. -/
@[simp] theorem condMutualInfo_encode {S T U : Type*}
    [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [Fintype T] [MeasurableSpace T] [DiscreteMeasurableSpace T]
    [Fintype U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (f : Ω → S) (g : Ω → T) (h : Ω → U) :
    condMutualInfo (FiniteAlphabet.encode ∘ f) (FiniteAlphabet.encode ∘ g)
      (FiniteAlphabet.encode ∘ h) μ = condMutualInfo f g h μ := by
  calc
    _ = condMutualInfo (FiniteAlphabet.encode ∘ f) (FiniteAlphabet.encode ∘ g) h μ :=
      condMutualInfo_of_inj Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
        μ FiniteAlphabet.encode_injective
    _ = condMutualInfo f (FiniteAlphabet.encode ∘ g) h μ :=
      condMutualInfo_of_inj_map Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
        (fun _ x => FiniteAlphabet.encode x) (fun _ => FiniteAlphabet.encode_injective)
    _ = condMutualInfo (FiniteAlphabet.encode ∘ g) f h μ :=
      condMutualInfo_comm Measurable.of_discrete Measurable.of_discrete h μ
    _ = condMutualInfo g f h μ :=
      condMutualInfo_of_inj_map Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
        (fun _ x => FiniteAlphabet.encode x) (fun _ => FiniteAlphabet.encode_injective)
    _ = condMutualInfo f g h μ :=
      condMutualInfo_comm Measurable.of_discrete Measurable.of_discrete h μ

section Heterogeneous
variable {A₁ A₂ A₃ B₁ B₂ B₃ C₁ C₂ C₃ D₀ : Type*}
  [Fintype A₁] [MeasurableSpace A₁] [DiscreteMeasurableSpace A₁]
  [Fintype A₂] [MeasurableSpace A₂] [DiscreteMeasurableSpace A₂]
  [Fintype A₃] [MeasurableSpace A₃] [DiscreteMeasurableSpace A₃]
  [Fintype B₁] [MeasurableSpace B₁] [DiscreteMeasurableSpace B₁]
  [Fintype B₂] [MeasurableSpace B₂] [DiscreteMeasurableSpace B₂]
  [Fintype B₃] [MeasurableSpace B₃] [DiscreteMeasurableSpace B₃]
  [Fintype C₁] [MeasurableSpace C₁] [DiscreteMeasurableSpace C₁]
  [Fintype C₂] [MeasurableSpace C₂] [DiscreteMeasurableSpace C₂]
  [Fintype C₃] [MeasurableSpace C₃] [DiscreteMeasurableSpace C₃]
  [Fintype D₀] [MeasurableSpace D₀] [DiscreteMeasurableSpace D₀]
  [Nonempty A₁] [Nonempty A₂] [Nonempty A₃]

omit [MeasurableSpace C₁] [DiscreteMeasurableSpace C₁] [MeasurableSpace C₂] [DiscreteMeasurableSpace C₂]
  [MeasurableSpace C₃] [DiscreteMeasurableSpace C₃] [MeasurableSpace D₀] [DiscreteMeasurableSpace D₀] in
/-- Lossless alphabet encoding transfers the concrete common-function bound
to arbitrary heterogeneous finite alphabets. -/
theorem common_lower_bound_finite
    (W₁ : Ω → A₁) (W₂ : Ω → A₂) (W₃ : Ω → A₃)
    (M₁ : Ω → B₁) (M₂ : Ω → B₂) (M₃ : Ω → B₃)
    (T₁ : Ω → C₁) (T₂ : Ω → C₂) (T₃ : Ω → C₃) (Θ : Ω → D₀)
    (enc₁ : ∀ x y, W₁ x = W₁ y → M₁ x = M₁ y ∧ T₁ x = T₁ y)
    (enc₂ : ∀ x y, W₂ x = W₂ y → M₂ x = M₂ y ∧ T₂ x = T₂ y)
    (enc₃ : ∀ x y, W₃ x = W₃ y → M₃ x = M₃ y ∧ T₃ x = T₃ y)
    (dec₁ : ∀ x y, M₁ x = M₁ y → T₁ x = T₁ y → W₁ x = W₁ y)
    (dec₂ : ∀ x y, M₂ x = M₂ y → T₂ x = T₂ y → W₂ x = W₂ y)
    (dec₃ : ∀ x y, M₃ x = M₃ y → T₃ x = T₃ y → W₃ x = W₃ y)
    (ind₁₂ : IndepFun W₁ W₂ μ) (ind₁₃ : IndepFun W₁ W₃ μ) (ind₂₃ : IndepFun W₂ W₃ μ)
    (tri₃ : ∀ x y, T₁ x = T₁ y → T₂ x = T₂ y → T₃ x = T₃ y)
    (tri₂ : ∀ x y, T₁ x = T₁ y → T₃ x = T₃ y → T₂ x = T₂ y)
    (common₁ : ∀ x y, M₁ x = M₁ y → M₂ x = M₂ y → M₃ x = M₃ y →
      T₁ x = T₁ y → Θ x = Θ y)
    (common₂ : ∀ x y, M₁ x = M₁ y → M₂ x = M₂ y → M₃ x = M₃ y →
      T₂ x = T₂ y → Θ x = Θ y)
    (bridge : ∀ x y, M₁ x = M₁ y → M₂ x = M₂ y → M₃ x = M₃ y →
      Θ x = Θ y → T₃ x = T₃ y → T₁ x = T₁ y) :
    2 * entropy (fun x => (W₁ x,W₂ x,W₃ x)) μ -
      (entropy W₁ μ + entropy W₂ μ + entropy W₃ μ) ≤
      entropy M₁ μ + entropy M₂ μ + entropy M₃ μ := by
  have h := common_lower_bound μ
    (FiniteAlphabet.encode ∘ W₁) (FiniteAlphabet.encode ∘ W₂) (FiniteAlphabet.encode ∘ W₃)
    (FiniteAlphabet.encode ∘ M₁) (FiniteAlphabet.encode ∘ M₂) (FiniteAlphabet.encode ∘ M₃)
    (FiniteAlphabet.encode ∘ T₁) (FiniteAlphabet.encode ∘ T₂) (FiniteAlphabet.encode ∘ T₃)
    (FiniteAlphabet.encode ∘ Θ)
    (by simpa only [Function.comp_apply,encode_eq_iff] using enc₁)
    (by simpa only [Function.comp_apply,encode_eq_iff] using enc₂)
    (by simpa only [Function.comp_apply,encode_eq_iff] using enc₃)
    (by simpa only [Function.comp_apply,encode_eq_iff] using dec₁)
    (by simpa only [Function.comp_apply,encode_eq_iff] using dec₂)
    (by simpa only [Function.comp_apply,encode_eq_iff] using dec₃)
    (ind₁₂.comp Measurable.of_discrete Measurable.of_discrete)
    (ind₁₃.comp Measurable.of_discrete Measurable.of_discrete)
    (ind₂₃.comp Measurable.of_discrete Measurable.of_discrete)
    (by simpa only [Function.comp_apply,encode_eq_iff] using tri₃)
    (by simpa only [Function.comp_apply,encode_eq_iff] using tri₂)
    (by simpa only [Function.comp_apply,encode_eq_iff] using common₁)
    (by simpa only [Function.comp_apply,encode_eq_iff] using common₂)
    (by simpa only [Function.comp_apply,encode_eq_iff] using bridge)
  have ht : entropy (fun x => (FiniteAlphabet.encode (W₁ x),FiniteAlphabet.encode (W₂ x),
      FiniteAlphabet.encode (W₃ x))) μ = entropy (fun x => (W₁ x,W₂ x,W₃ x)) μ := by
    apply entropy_eq_of_fibers μ
    intro x y
    simp
  simpa only [entropy_encode,Function.comp_apply,ht] using h
omit [MeasurableSpace C₁] [DiscreteMeasurableSpace C₁] [MeasurableSpace C₂] [DiscreteMeasurableSpace C₂]
  [MeasurableSpace C₃] [DiscreteMeasurableSpace C₃] [MeasurableSpace D₀] [DiscreteMeasurableSpace D₀] in
/-- Actual retained-information common-function bound for heterogeneous finite alphabets. -/
theorem common_retained_bound_finite
    (W₁ : Ω → A₁) (W₂ : Ω → A₂) (W₃ : Ω → A₃)
    (M₁ : Ω → B₁) (M₂ : Ω → B₂) (M₃ : Ω → B₃)
    (T₁ : Ω → C₁) (T₂ : Ω → C₂) (T₃ : Ω → C₃) (Θ : Ω → D₀)
    (enc₁ : ∀ x y, W₁ x = W₁ y → M₁ x = M₁ y ∧ T₁ x = T₁ y)
    (enc₂ : ∀ x y, W₂ x = W₂ y → M₂ x = M₂ y ∧ T₂ x = T₂ y)
    (enc₃ : ∀ x y, W₃ x = W₃ y → M₃ x = M₃ y ∧ T₃ x = T₃ y)
    (dec₁ : ∀ x y, M₁ x = M₁ y → T₁ x = T₁ y → W₁ x = W₁ y)
    (dec₂ : ∀ x y, M₂ x = M₂ y → T₂ x = T₂ y → W₂ x = W₂ y)
    (dec₃ : ∀ x y, M₃ x = M₃ y → T₃ x = T₃ y → W₃ x = W₃ y)
    (ind₁₂ : IndepFun W₁ W₂ μ) (ind₁₃ : IndepFun W₁ W₃ μ) (ind₂₃ : IndepFun W₂ W₃ μ)
    (tri₃ : ∀ x y, T₁ x = T₁ y → T₂ x = T₂ y → T₃ x = T₃ y)
    (tri₂ : ∀ x y, T₁ x = T₁ y → T₃ x = T₃ y → T₂ x = T₂ y)
    (common₁ : ∀ x y, M₁ x = M₁ y → M₂ x = M₂ y → M₃ x = M₃ y →
      T₁ x = T₁ y → Θ x = Θ y)
    (common₂ : ∀ x y, M₁ x = M₁ y → M₂ x = M₂ y → M₃ x = M₃ y →
      T₂ x = T₂ y → Θ x = Θ y)
    (bridge : ∀ x y, M₁ x = M₁ y → M₂ x = M₂ y → M₃ x = M₃ y →
      Θ x = Θ y → T₃ x = T₃ y → T₁ x = T₁ y) :
    2 * entropy (fun x => (W₁ x,W₂ x,W₃ x)) μ -
      (entropy W₁ μ + entropy W₂ μ + entropy W₃ μ) +
      condMutualInfo M₂ M₃ W₁ μ + condMutualInfo M₁ M₃ W₂ μ ≤
      entropy M₁ μ + entropy M₂ μ + entropy M₃ μ := by
  have h := common_retained_bound μ
    (FiniteAlphabet.encode ∘ W₁) (FiniteAlphabet.encode ∘ W₂) (FiniteAlphabet.encode ∘ W₃)
    (FiniteAlphabet.encode ∘ M₁) (FiniteAlphabet.encode ∘ M₂) (FiniteAlphabet.encode ∘ M₃)
    (FiniteAlphabet.encode ∘ T₁) (FiniteAlphabet.encode ∘ T₂) (FiniteAlphabet.encode ∘ T₃)
    (FiniteAlphabet.encode ∘ Θ)
    (by simpa only [Function.comp_apply,encode_eq_iff] using enc₁)
    (by simpa only [Function.comp_apply,encode_eq_iff] using enc₂)
    (by simpa only [Function.comp_apply,encode_eq_iff] using enc₃)
    (by simpa only [Function.comp_apply,encode_eq_iff] using dec₁)
    (by simpa only [Function.comp_apply,encode_eq_iff] using dec₂)
    (by simpa only [Function.comp_apply,encode_eq_iff] using dec₃)
    (ind₁₂.comp Measurable.of_discrete Measurable.of_discrete)
    (ind₁₃.comp Measurable.of_discrete Measurable.of_discrete)
    (ind₂₃.comp Measurable.of_discrete Measurable.of_discrete)
    (by simpa only [Function.comp_apply,encode_eq_iff] using tri₃)
    (by simpa only [Function.comp_apply,encode_eq_iff] using tri₂)
    (by simpa only [Function.comp_apply,encode_eq_iff] using common₁)
    (by simpa only [Function.comp_apply,encode_eq_iff] using common₂)
    (by simpa only [Function.comp_apply,encode_eq_iff] using bridge)
  have ht : entropy (fun x => (FiniteAlphabet.encode (W₁ x),FiniteAlphabet.encode (W₂ x),
      FiniteAlphabet.encode (W₃ x))) μ = entropy (fun x => (W₁ x,W₂ x,W₃ x)) μ := by
    apply entropy_eq_of_fibers μ
    intro x y
    simp
  simpa only [entropy_encode,condMutualInfo_encode,Function.comp_apply,ht] using h
end Heterogeneous

section CodeGeometry
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Concrete projection data isolating one retained private coefficient block. -/
structure PrivateSplit (task : Task K F) (i : Three) (T₀ : Submodule K F) where
  P : Submodule K F
  projection : F →ₗ[K] P
  on_private : ∀ p : P, projection p = p
  on_tripod : ∀ t ∈ T₀, projection t = 0
  side_eq : task.A i = P ⊔ T₀
  on_others : ∀ j, j ≠ i → ∀ a ∈ task.A j, projection a = 0
  remote_span : (⨆ j : {j : Three // j ≠ i}, (task.U j.val).map projection) = ⊤

/-- Build the subtype-valued private-slice certificate from the ordinary
private embedding/projection of a canonical coordinate chart. Full use of
private coordinates is exactly the remote projected-signal spanning input. -/
def PrivateSplit.of_raw_projection {P : Type*} [AddCommGroup P] [Module K P]
    (task : Task K F) (i : Three) (T₀ : Submodule K F)
    (embed : P →ₗ[K] F) (proj : F →ₗ[K] P)
    (left : ∀ p, proj (embed p) = p)
    (tripod : ∀ t ∈ T₀, proj t = 0)
    (side : task.A i = LinearMap.range embed ⊔ T₀)
    (others : ∀ j, j ≠ i → ∀ a ∈ task.A j, proj a = 0)
    (fullUse : (⨆ j : {j : Three // j ≠ i}, (task.U j.val).map proj) = ⊤) :
    PrivateSplit task i T₀ := by
  let e : P →ₗ[K] LinearMap.range embed := embed.codRestrict _ (fun p => ⟨p,rfl⟩)
  let π := e.comp proj
  refine ⟨LinearMap.range embed,π,?_,?_,side,?_,?_⟩
  · rintro ⟨z,⟨p,rfl⟩⟩
    apply Subtype.ext
    change embed (proj (embed p)) = embed p
    rw [left]
  · intro t ht
    change e (proj t) = 0
    rw [tripod t ht,map_zero]
  · intro j hj a ha
    change e (proj a) = 0
    rw [others j hj a ha,map_zero]
  · apply top_unique
    rintro ⟨z,⟨p,rfl⟩⟩ _
    let Q : Submodule K (LinearMap.range embed) :=
      ⨆ j : {j : Three // j ≠ i}, (task.U j.val).map π
    have hh : (⊤ : Submodule K P) ≤ Q.comap e := by
      rw [← fullUse]
      apply iSup_le
      intro j x hx
      obtain ⟨u,hu,rfl⟩ := hx
      exact (le_iSup (fun j : {j : Three // j ≠ i} => (task.U j.val).map π) j) ⟨u,hu,rfl⟩
    exact hh (Submodule.mem_top : p ∈ (⊤ : Submodule K P))

variable {n : ℕ}

/-- Restriction of equal observations to a smaller coefficient subspace. -/
theorem observation_eq_of_le {A B : Submodule K F} (hAB : A ≤ B)
    (x y : Source K F n) (h : UploadBroadcast.observe K F B x = UploadBroadcast.observe K F B y) :
    UploadBroadcast.observe K F A x = UploadBroadcast.observe K F A y := by
  apply LinearMap.ext
  intro a
  exact LinearMap.congr_fun h ⟨a,hAB a.property⟩

/-- Equality of the two component observations implies equality on their sum. -/
theorem observation_eq_sup (A B : Submodule K F) (x y : Source K F n)
    (ha : UploadBroadcast.observe K F A x = UploadBroadcast.observe K F A y)
    (hb : UploadBroadcast.observe K F B x = UploadBroadcast.observe K F B y) :
    UploadBroadcast.observe K F (A ⊔ B) x = UploadBroadcast.observe K F (A ⊔ B) y := by
  apply LinearMap.ext
  intro z
  obtain ⟨a,ha',b,hb',he⟩ := Submodule.mem_sup.mp z.property
  have ea := LinearMap.congr_fun ha ⟨a,ha'⟩
  have eb := LinearMap.congr_fun hb ⟨b,hb'⟩
  change x (z:F) = y (z:F)
  rw [← he,map_add,map_add]
  exact congrArg₂ (· + ·) ea eb

local instance sourceMeasurable (E : Type*) [AddCommGroup E] [Module K E] (m : ℕ) :
    MeasurableSpace (Source K E m) := ⊤
local instance sourceDiscrete (E : Type*) [AddCommGroup E] [Module K E] (m : ℕ) :
    DiscreteMeasurableSpace (Source K E m) := ⟨fun _ => trivial⟩

variable [Finite K] [FiniteDimensional K F]

/-- Disjoint coefficient observations of the actual uniform source are independent. -/
theorem observations_independent (A B : Submodule K F) (hAB : Disjoint A B) (n : ℕ) :
    IndepFun (UploadBroadcast.observe K F A (L := n)) (UploadBroadcast.observe K F B (L := n))
      (uniformOn (Set.univ : Set (Source K F n))) := by
  letI : Finite (Source K F n) := Module.finite_of_finite K
  have hq : (1 : ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
  have hr := LinearObservation.model_mutualInfo_rank A B n
  rw [disjoint_iff.mp hAB,finrank_bot,Nat.cast_zero,mul_zero] at hr
  apply (mutualInfo_eq_zero Measurable.of_discrete Measurable.of_discrete).mp
  exact (div_eq_zero_iff.mp hr).resolve_right (ne_of_gt (Real.log_pos hq))

/-- The joint side observation has the full source entropy when the actual
coefficient subspaces span, at every blocklength. -/
theorem joint_observation_entropy_rank (A B C : Submodule K F)
    (hspan : A ⊔ B ⊔ C = ⊤) (n : ℕ) :
    entropy (fun x : Source K F n => (UploadBroadcast.observe K F A x,
      UploadBroadcast.observe K F B x,UploadBroadcast.observe K F C x))
      (uniformOn (Set.univ : Set (Source K F n))) / Real.log (Nat.card K) =
      (n:ℝ) * Module.finrank K F := by
  letI : Finite (Source K F n) := Module.finite_of_finite K
  letI : Fintype (Source K F n) := Fintype.ofFinite _
  letI (A : Submodule K F) : Finite (Source K A n) := Module.finite_of_finite K
  have he : entropy (fun x : Source K F n => (UploadBroadcast.observe K F A x,
      UploadBroadcast.observe K F B x,UploadBroadcast.observe K F C x))
      (uniformOn (Set.univ : Set (Source K F n))) =
      entropy (UploadBroadcast.observe K F ⊤ (L := n))
      (uniformOn (Set.univ : Set (Source K F n))) := by
    apply entropy_eq_of_fibers
    intro x y
    constructor
    · intro h
      have hh := observation_eq_sup (A ⊔ B) C x y
        (observation_eq_sup A B x y (congrArg Prod.fst h) (congrArg (fun z => z.2.1) h))
        (congrArg (fun z => z.2.2) h)
      exact observation_eq_of_le (by rw [hspan]) x y hh
    · intro h
      exact Prod.ext (observation_eq_of_le le_top x y h)
        (Prod.ext (observation_eq_of_le le_top x y h) (observation_eq_of_le le_top x y h))
  rw [he,LinearObservation.model_entropy_rank,finrank_top]

/-- Actual nonlinear zero-error code implies the residual common-function
entropy lower bound. The input geometry is coefficient/projection data;
no entropy inequality or functional recovery is assumed. -/
theorem code_entropy_bound {M : Three → Type*} {S : Type*}
    [∀ i, Fintype (M i)] [∀ i, MeasurableSpace (M i)] [∀ i, DiscreteMeasurableSpace (M i)]
    (task : Task K F) (code : task.Code n M S) (T₀ : Three → Submodule K F)
    (split : ∀ i, PrivateSplit task i (T₀ i))
    (hdis₀₁ : Disjoint (task.A 0) (task.A 1))
    (hdis₀₂ : Disjoint (task.A 0) (task.A 2))
    (hdis₁₂ : Disjoint (task.A 1) (task.A 2))
    (htri₂ : T₀ 2 ≤ T₀ 0 ⊔ T₀ 1) (htri₁ : T₀ 1 ≤ T₀ 0 ⊔ T₀ 2)
    (hbridge : T₀ 0 ≤ task.U 2 ⊔ (task.U 0 ⊓ task.U 1)) :
    let μ := uniformOn (Set.univ : Set (Source K F n))
    let W := fun i => UploadBroadcast.observe K F (task.A i) (L := n)
    let upload := fun i x => code.encode i (W i x)
    2 * entropy (fun x => (W 0 x,W 1 x,W 2 x)) μ -
      (entropy (W 0) μ + entropy (W 1) μ + entropy (W 2) μ) ≤
      entropy (upload 0) μ + entropy (upload 1) μ + entropy (upload 2) μ := by
  classical
  letI : Finite (Source K F n) := Module.finite_of_finite K
  letI : Fintype (Source K F n) := Fintype.ofFinite _
  letI (A : Submodule K F) : Finite (Source K A n) := Module.finite_of_finite K
  letI (A : Submodule K F) : Fintype (Source K A n) := Fintype.ofFinite _
  let μ := uniformOn (Set.univ : Set (Source K F n))
  let W := fun i => UploadBroadcast.observe K F (task.A i) (L := n)
  let T := fun i => UploadBroadcast.observe K F (T₀ i) (L := n)
  let upload := fun i x => code.encode i (W i x)
  let θ := UploadBroadcast.observe K F (task.U 0 ⊓ task.U 1) (L := n)
  have ht (i : Three) : T₀ i ≤ task.A i := by rw [(split i).side_eq]; exact le_sup_right
  have dec (i : Three) (x y : Source K F n) (hm : upload i x = upload i y) (htt : T i x = T i y) :
      W i x = W i y := by
    obtain ⟨slice,hslice⟩ := SignalBridge.private_slice_inverse task code i (split i).P (T₀ i)
      (split i).projection (split i).on_private (split i).on_tripod (split i).side_eq
      (split i).on_others (split i).remote_span
    change UploadBroadcast.observe K F (task.A i) x = UploadBroadcast.observe K F (task.A i) y
    rw [← hslice x,← hslice y]
    exact congrArg₂ slice hm htt
  have enc (i : Three) (x y : Source K F n) (hw : W i x = W i y) :
      upload i x = upload i y ∧ T i x = T i y :=
    ⟨congrArg (code.encode i) hw,observation_eq_of_le (ht i) x y hw⟩
  have sig (i : Three) (x y : Source K F n)
      (h₀ : upload 0 x = upload 0 y) (h₁ : upload 1 x = upload 1 y)
      (h₂ : upload 2 x = upload 2 y) (htt : T i x = T i y) :
      UploadBroadcast.observe K F (task.U i) x = UploadBroadcast.observe K F (task.U i) y := by
    have hm : (fun j => upload j x) = (fun j => upload j y) := by
      funext j
      fin_cases j <;> assumption
    have hmi : upload i x = upload i y := congrFun hm i
    have hw := dec i x y hmi htt
    rw [← code.zero_error x i,← code.zero_error y i]
    change code.decode i (code.broadcast (fun j => upload j x)) (W i x) =
      code.decode i (code.broadcast (fun j => upload j y)) (W i y)
    rw [hm,hw]
  apply common_lower_bound_finite μ (W 0) (W 1) (W 2) (upload 0) (upload 1) (upload 2)
    (T 0) (T 1) (T 2) θ (enc 0) (enc 1) (enc 2) (dec 0) (dec 1) (dec 2)
    (observations_independent _ _ hdis₀₁ n) (observations_independent _ _ hdis₀₂ n)
    (observations_independent _ _ hdis₁₂ n)
  · intro x y h₀ h₁
    exact observation_eq_of_le htri₂ x y (observation_eq_sup _ _ x y h₀ h₁)
  · intro x y h₀ h₂
    exact observation_eq_of_le htri₁ x y (observation_eq_sup _ _ x y h₀ h₂)
  · intro x y h₀ h₁ h₂ htt
    exact observation_eq_of_le inf_le_left x y (sig 0 x y h₀ h₁ h₂ htt)
  · intro x y h₀ h₁ h₂ htt
    exact observation_eq_of_le inf_le_right x y (sig 1 x y h₀ h₁ h₂ htt)
  · intro x y h₀ h₁ h₂ hθ htt
    exact observation_eq_of_le hbridge x y (observation_eq_sup _ _ x y (sig 2 x y h₀ h₁ h₂ htt) hθ)

/-- The retained-information residual bound derived from an actual arbitrary
nonlinear code. The retained terms condition on the actual original sides. -/
theorem code_retained_entropy_bound {M : Three → Type*} {S : Type*}
    [∀ i, Fintype (M i)] [∀ i, MeasurableSpace (M i)] [∀ i, DiscreteMeasurableSpace (M i)]
    (task : Task K F) (code : task.Code n M S) (T₀ : Three → Submodule K F)
    (split : ∀ i, PrivateSplit task i (T₀ i))
    (hdis₀₁ : Disjoint (task.A 0) (task.A 1))
    (hdis₀₂ : Disjoint (task.A 0) (task.A 2))
    (hdis₁₂ : Disjoint (task.A 1) (task.A 2))
    (htri₂ : T₀ 2 ≤ T₀ 0 ⊔ T₀ 1) (htri₁ : T₀ 1 ≤ T₀ 0 ⊔ T₀ 2)
    (hbridge : T₀ 0 ≤ task.U 2 ⊔ (task.U 0 ⊓ task.U 1)) :
    let μ := uniformOn (Set.univ : Set (Source K F n))
    let W := fun i => UploadBroadcast.observe K F (task.A i) (L := n)
    let upload := fun i x => code.encode i (W i x)
    2 * entropy (fun x => (W 0 x,W 1 x,W 2 x)) μ -
      (entropy (W 0) μ + entropy (W 1) μ + entropy (W 2) μ) +
      condMutualInfo (upload 1) (upload 2) (W 0) μ +
      condMutualInfo (upload 0) (upload 2) (W 1) μ ≤
      entropy (upload 0) μ + entropy (upload 1) μ + entropy (upload 2) μ := by
  classical
  letI : Finite (Source K F n) := Module.finite_of_finite K
  letI : Fintype (Source K F n) := Fintype.ofFinite _
  letI (A : Submodule K F) : Finite (Source K A n) := Module.finite_of_finite K
  letI (A : Submodule K F) : Fintype (Source K A n) := Fintype.ofFinite _
  let μ := uniformOn (Set.univ : Set (Source K F n))
  let W := fun i => UploadBroadcast.observe K F (task.A i) (L := n)
  let T := fun i => UploadBroadcast.observe K F (T₀ i) (L := n)
  let upload := fun i x => code.encode i (W i x)
  let θ := UploadBroadcast.observe K F (task.U 0 ⊓ task.U 1) (L := n)
  have ht (i : Three) : T₀ i ≤ task.A i := by rw [(split i).side_eq]; exact le_sup_right
  have dec (i : Three) (x y : Source K F n) (hm : upload i x = upload i y) (htt : T i x = T i y) :
      W i x = W i y := by
    obtain ⟨slice,hslice⟩ := SignalBridge.private_slice_inverse task code i (split i).P (T₀ i)
      (split i).projection (split i).on_private (split i).on_tripod (split i).side_eq
      (split i).on_others (split i).remote_span
    change UploadBroadcast.observe K F (task.A i) x = UploadBroadcast.observe K F (task.A i) y
    rw [← hslice x,← hslice y]
    exact congrArg₂ slice hm htt
  have enc (i : Three) (x y : Source K F n) (hw : W i x = W i y) :
      upload i x = upload i y ∧ T i x = T i y :=
    ⟨congrArg (code.encode i) hw,observation_eq_of_le (ht i) x y hw⟩
  have sig (i : Three) (x y : Source K F n)
      (h₀ : upload 0 x = upload 0 y) (h₁ : upload 1 x = upload 1 y)
      (h₂ : upload 2 x = upload 2 y) (htt : T i x = T i y) :
      UploadBroadcast.observe K F (task.U i) x = UploadBroadcast.observe K F (task.U i) y := by
    have hm : (fun j => upload j x) = (fun j => upload j y) := by
      funext j
      fin_cases j <;> assumption
    have hmi : upload i x = upload i y := congrFun hm i
    have hw := dec i x y hmi htt
    rw [← code.zero_error x i,← code.zero_error y i]
    change code.decode i (code.broadcast (fun j => upload j x)) (W i x) =
      code.decode i (code.broadcast (fun j => upload j y)) (W i y)
    rw [hm,hw]
  apply common_retained_bound_finite μ (W 0) (W 1) (W 2) (upload 0) (upload 1) (upload 2)
    (T 0) (T 1) (T 2) θ (enc 0) (enc 1) (enc 2) (dec 0) (dec 1) (dec 2)
    (observations_independent _ _ hdis₀₁ n) (observations_independent _ _ hdis₀₂ n)
    (observations_independent _ _ hdis₁₂ n)
  · intro x y h₀ h₁
    exact observation_eq_of_le htri₂ x y (observation_eq_sup _ _ x y h₀ h₁)
  · intro x y h₀ h₂
    exact observation_eq_of_le htri₁ x y (observation_eq_sup _ _ x y h₀ h₂)
  · intro x y h₀ h₁ h₂ htt
    exact observation_eq_of_le inf_le_left x y (sig 0 x y h₀ h₁ h₂ htt)
  · intro x y h₀ h₁ h₂ htt
    exact observation_eq_of_le inf_le_right x y (sig 1 x y h₀ h₁ h₂ htt)
  · intro x y h₀ h₁ h₂ hθ htt
    exact observation_eq_of_le hbridge x y (observation_eq_sup _ _ x y (sig 2 x y h₀ h₁ h₂ htt) hθ)

/-- The same actual-code bound under any user permutation; this supplies all
three cyclic retained inequalities without relabeling the code's alphabets. -/
theorem code_retained_entropy_bound_ordered {M : Three → Type*} {S : Type*}
    [∀ i, Fintype (M i)] [∀ i, MeasurableSpace (M i)] [∀ i, DiscreteMeasurableSpace (M i)]
    (p : Equiv.Perm Three) (task : Task K F) (code : task.Code n M S) (T₀ : Three → Submodule K F)
    (split : ∀ i, PrivateSplit task i (T₀ i))
    (hdis₀₁ : Disjoint (task.A (p 0)) (task.A (p 1)))
    (hdis₀₂ : Disjoint (task.A (p 0)) (task.A (p 2)))
    (hdis₁₂ : Disjoint (task.A (p 1)) (task.A (p 2)))
    (htri₂ : T₀ (p 2) ≤ T₀ (p 0) ⊔ T₀ (p 1)) (htri₁ : T₀ (p 1) ≤ T₀ (p 0) ⊔ T₀ (p 2))
    (hbridge : T₀ (p 0) ≤ task.U (p 2) ⊔ (task.U (p 0) ⊓ task.U (p 1))) :
    let μ := uniformOn (Set.univ : Set (Source K F n))
    let W := fun i => UploadBroadcast.observe K F (task.A i) (L := n)
    let upload := fun i x => code.encode i (W i x)
    2 * entropy (fun x => (W (p 0) x,W (p 1) x,W (p 2) x)) μ -
      (entropy (W (p 0)) μ + entropy (W (p 1)) μ + entropy (W (p 2)) μ) +
      condMutualInfo (upload (p 1)) (upload (p 2)) (W (p 0)) μ +
      condMutualInfo (upload (p 0)) (upload (p 2)) (W (p 1)) μ ≤
      entropy (upload (p 0)) μ + entropy (upload (p 1)) μ + entropy (upload (p 2)) μ := by
  classical
  letI : Finite (Source K F n) := Module.finite_of_finite K
  letI : Fintype (Source K F n) := Fintype.ofFinite _
  letI (A : Submodule K F) : Finite (Source K A n) := Module.finite_of_finite K
  letI (A : Submodule K F) : Fintype (Source K A n) := Fintype.ofFinite _
  let μ := uniformOn (Set.univ : Set (Source K F n))
  let W := fun i => UploadBroadcast.observe K F (task.A i) (L := n)
  let T := fun i => UploadBroadcast.observe K F (T₀ i) (L := n)
  let upload := fun i x => code.encode i (W i x)
  let θ := UploadBroadcast.observe K F (task.U (p 0) ⊓ task.U (p 1)) (L := n)
  have ht (i : Three) : T₀ i ≤ task.A i := by rw [(split i).side_eq]; exact le_sup_right
  have dec (i : Three) (x y : Source K F n) (hm : upload i x = upload i y) (htt : T i x = T i y) :
      W i x = W i y := by
    obtain ⟨slice,hslice⟩ := SignalBridge.private_slice_inverse task code i (split i).P (T₀ i)
      (split i).projection (split i).on_private (split i).on_tripod (split i).side_eq
      (split i).on_others (split i).remote_span
    change UploadBroadcast.observe K F (task.A i) x = UploadBroadcast.observe K F (task.A i) y
    rw [← hslice x,← hslice y]
    exact congrArg₂ slice hm htt
  have enc (i : Three) (x y : Source K F n) (hw : W i x = W i y) :
      upload i x = upload i y ∧ T i x = T i y :=
    ⟨congrArg (code.encode i) hw,observation_eq_of_le (ht i) x y hw⟩
  have sig (i : Three) (x y : Source K F n)
      (h₀ : upload (p 0) x = upload (p 0) y) (h₁ : upload (p 1) x = upload (p 1) y)
      (h₂ : upload (p 2) x = upload (p 2) y) (htt : T i x = T i y) :
      UploadBroadcast.observe K F (task.U i) x = UploadBroadcast.observe K F (task.U i) y := by
    have hm : (fun j => upload j x) = (fun j => upload j y) := by
      funext j
      obtain ⟨k,rfl⟩ := p.surjective j
      fin_cases k <;> assumption
    have hmi : upload i x = upload i y := congrFun hm i
    have hw := dec i x y hmi htt
    rw [← code.zero_error x i,← code.zero_error y i]
    change code.decode i (code.broadcast (fun j => upload j x)) (W i x) =
      code.decode i (code.broadcast (fun j => upload j y)) (W i y)
    rw [hm,hw]
  apply common_retained_bound_finite μ (W (p 0)) (W (p 1)) (W (p 2)) (upload (p 0)) (upload (p 1)) (upload (p 2))
    (T (p 0)) (T (p 1)) (T (p 2)) θ (enc (p 0)) (enc (p 1)) (enc (p 2)) (dec (p 0)) (dec (p 1)) (dec (p 2))
    (observations_independent _ _ hdis₀₁ n) (observations_independent _ _ hdis₀₂ n)
    (observations_independent _ _ hdis₁₂ n)
  · intro x y h₀ h₁
    exact observation_eq_of_le htri₂ x y (observation_eq_sup _ _ x y h₀ h₁)
  · intro x y h₀ h₂
    exact observation_eq_of_le htri₁ x y (observation_eq_sup _ _ x y h₀ h₂)
  · intro x y h₀ h₁ h₂ htt
    exact observation_eq_of_le inf_le_left x y (sig (p 0) x y h₀ h₁ h₂ htt)
  · intro x y h₀ h₁ h₂ htt
    exact observation_eq_of_le inf_le_right x y (sig (p 1) x y h₀ h₁ h₂ htt)
  · intro x y h₀ h₁ h₂ hθ htt
    exact observation_eq_of_le hbridge x y (observation_eq_sup _ _ x y (sig (p 2) x y h₀ h₁ h₂ htt) hθ)

/-- Actual fixed-length upload cost lower bound, obtained from the genuine
Shannon inequality, the uniform-source rank dictionary, and attained
alphabet cardinalities. The code may be nonlinear at every blocklength. -/
theorem code_rank_lower_bound {M : Three → Type*} {S : Type*}
    [∀ i, Fintype (M i)] [∀ i, MeasurableSpace (M i)] [∀ i, DiscreteMeasurableSpace (M i)]
    (task : Task K F) (code : task.Code n M S) (T₀ : Three → Submodule K F)
    (split : ∀ i, PrivateSplit task i (T₀ i))
    (hdis₀₁ : Disjoint (task.A 0) (task.A 1))
    (hdis₀₂ : Disjoint (task.A 0) (task.A 2))
    (hdis₁₂ : Disjoint (task.A 1) (task.A 2))
    (htri₂ : T₀ 2 ≤ T₀ 0 ⊔ T₀ 1) (htri₁ : T₀ 1 ≤ T₀ 0 ⊔ T₀ 2)
    (hbridge : T₀ 0 ≤ task.U 2 ⊔ (task.U 0 ⊓ task.U 1))
    (hspan : task.A 0 ⊔ task.A 1 ⊔ task.A 2 = ⊤) (hn : 0 < n) :
    2 * (Module.finrank K F : ℝ) - (Module.finrank K (task.A 0) +
      Module.finrank K (task.A 1) + Module.finrank K (task.A 2)) ≤ code.uploadCost := by
  classical
  letI : Finite (Source K F n) := Module.finite_of_finite K
  letI : Fintype (Source K F n) := Fintype.ofFinite _
  letI (A : Submodule K F) : Finite (Source K A n) := Module.finite_of_finite K
  letI (A : Submodule K F) : Fintype (Source K A n) := Fintype.ofFinite _
  let μ := uniformOn (Set.univ : Set (Source K F n))
  let W := fun i => UploadBroadcast.observe K F (task.A i) (L := n)
  let upload := fun i x => code.encode i (W i x)
  have hjoint : entropy (fun x => (W 0 x,W 1 x,W 2 x)) μ =
      entropy (UploadBroadcast.observe K F ⊤ (L := n)) μ := by
    apply entropy_eq_of_fibers μ
    intro x y
    constructor
    · intro he
      have h₀ := congrArg Prod.fst he
      have h₁ := congrArg (fun z => z.2.1) he
      have h₂ := congrArg (fun z => z.2.2) he
      have hs := observation_eq_sup (task.A 0 ⊔ task.A 1) (task.A 2) x y
        (observation_eq_sup _ _ x y h₀ h₁) h₂
      exact observation_eq_of_le (by rw [hspan]) x y hs
    · intro he
      exact Prod.ext (observation_eq_of_le le_top x y he)
        (Prod.ext (observation_eq_of_le le_top x y he) (observation_eq_of_le le_top x y he))
  have hq : (1 : ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
  have hlog : 0 < Real.log (Nat.card K) := Real.log_pos hq
  have hb := code_entropy_bound task code T₀ split hdis₀₁ hdis₀₂ hdis₁₂ htri₂ htri₁ hbridge
  change 2 * entropy (fun x => (W 0 x,W 1 x,W 2 x)) μ -
      (entropy (W 0) μ + entropy (W 1) μ + entropy (W 2) μ) ≤
      entropy (upload 0) μ + entropy (upload 1) μ + entropy (upload 2) μ at hb
  have hbq := (div_le_div_iff_of_pos_right hlog).mpr hb
  rw [hjoint] at hbq
  simp only [sub_div,add_div,mul_div_assoc] at hbq
  have hr (A : Submodule K F) := LinearObservation.model_entropy_rank A n
  change ∀ A : Submodule K F, entropy (UploadBroadcast.observe K F A (L := n)) μ /
    Real.log (Nat.card K) = (n:ℝ) * Module.finrank K A at hr
  rw [hr ⊤,hr (task.A 0),hr (task.A 1),hr (task.A 2),finrank_top] at hbq
  have cap (i : Three) : entropy (upload i) μ / Real.log (Nat.card K) ≤
      Real.logb (Nat.card K) (Nat.card (Set.range (code.encode i))) := by
    have he : Set.range (upload i) = Set.range (code.encode i) := by
      ext a
      constructor
      · rintro ⟨x,rfl⟩
        exact ⟨W i x,rfl⟩
      · rintro ⟨w,rfl⟩
        obtain ⟨x,hx⟩ := w.exists_extend
        exact ⟨x,congrArg (code.encode i) hx⟩
    have hc := entropy_div_log_le_logb_attainable μ (upload i) Measurable.of_discrete
      (Nat.card K) hq
    simpa only [he] using hc
  have cap₀ := cap 0
  have cap₁ := cap 1
  have cap₂ := cap 2
  change _ ≤ (∑ i, Real.logb (Nat.card K) (Nat.card (Set.range (code.encode i)))) / (n:ℝ)
  apply (le_div_iff₀ (by exact_mod_cast hn : (0:ℝ) < n)).mpr
  rw [Fin.sum_univ_three]
  nlinarith


/-- The manuscript's retained residual rank bound, in actual q-ary Shannon
units and conditioned on the original side observations. -/
theorem code_retained_rank_bound {M : Three → Type*} {S : Type*}
    [∀ i, Fintype (M i)] [∀ i, MeasurableSpace (M i)] [∀ i, DiscreteMeasurableSpace (M i)]
    (task : Task K F) (code : task.Code n M S) (T₀ : Three → Submodule K F)
    (split : ∀ i, PrivateSplit task i (T₀ i))
    (hdis₀₁ : Disjoint (task.A 0) (task.A 1))
    (hdis₀₂ : Disjoint (task.A 0) (task.A 2))
    (hdis₁₂ : Disjoint (task.A 1) (task.A 2))
    (htri₂ : T₀ 2 ≤ T₀ 0 ⊔ T₀ 1) (htri₁ : T₀ 1 ≤ T₀ 0 ⊔ T₀ 2)
    (hbridge : T₀ 0 ≤ task.U 2 ⊔ (task.U 0 ⊓ task.U 1))
    (hspan : task.A 0 ⊔ task.A 1 ⊔ task.A 2 = ⊤) :
    let μ := uniformOn (Set.univ : Set (Source K F n))
    let W := fun i => UploadBroadcast.observe K F (task.A i) (L := n)
    let upload := fun i x => code.encode i (W i x)
    (n:ℝ) * (2 * (Module.finrank K F : ℝ) - (Module.finrank K (task.A 0) +
      Module.finrank K (task.A 1) + Module.finrank K (task.A 2))) +
      condMutualInfo (upload 1) (upload 2) (W 0) μ / Real.log (Nat.card K) +
      condMutualInfo (upload 0) (upload 2) (W 1) μ / Real.log (Nat.card K) ≤
      entropy (upload 0) μ / Real.log (Nat.card K) + entropy (upload 1) μ / Real.log (Nat.card K) +
      entropy (upload 2) μ / Real.log (Nat.card K) := by
  have hq : (1 : ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
  have hlog := Real.log_pos hq
  have hb := code_retained_entropy_bound task code T₀ split hdis₀₁ hdis₀₂ hdis₁₂ htri₂ htri₁ hbridge
  dsimp only at hb ⊢
  have hbq := (div_le_div_iff_of_pos_right hlog).mpr hb
  simp only [sub_div,add_div,mul_div_assoc] at hbq
  rw [joint_observation_entropy_rank _ _ _ hspan n,
    LinearObservation.model_entropy_rank,LinearObservation.model_entropy_rank,
    LinearObservation.model_entropy_rank] at hbq
  convert hbq using 1; ring


/-- User-permutation version of the retained q-ary rank bound. -/
theorem code_retained_rank_bound_ordered {M : Three → Type*} {S : Type*}
    [∀ i, Fintype (M i)] [∀ i, MeasurableSpace (M i)] [∀ i, DiscreteMeasurableSpace (M i)]
    (p : Equiv.Perm Three) (task : Task K F) (code : task.Code n M S) (T₀ : Three → Submodule K F)
    (split : ∀ i, PrivateSplit task i (T₀ i))
    (hdis₀₁ : Disjoint (task.A (p 0)) (task.A (p 1)))
    (hdis₀₂ : Disjoint (task.A (p 0)) (task.A (p 2)))
    (hdis₁₂ : Disjoint (task.A (p 1)) (task.A (p 2)))
    (htri₂ : T₀ (p 2) ≤ T₀ (p 0) ⊔ T₀ (p 1)) (htri₁ : T₀ (p 1) ≤ T₀ (p 0) ⊔ T₀ (p 2))
    (hbridge : T₀ (p 0) ≤ task.U (p 2) ⊔ (task.U (p 0) ⊓ task.U (p 1)))
    (hspan : task.A (p 0) ⊔ task.A (p 1) ⊔ task.A (p 2) = ⊤) :
    let μ := uniformOn (Set.univ : Set (Source K F n))
    let W := fun i => UploadBroadcast.observe K F (task.A i) (L := n)
    let upload := fun i x => code.encode i (W i x)
    (n:ℝ) * (2 * (Module.finrank K F : ℝ) - (Module.finrank K (task.A (p 0)) +
      Module.finrank K (task.A (p 1)) + Module.finrank K (task.A (p 2)))) +
      condMutualInfo (upload (p 1)) (upload (p 2)) (W (p 0)) μ / Real.log (Nat.card K) +
      condMutualInfo (upload (p 0)) (upload (p 2)) (W (p 1)) μ / Real.log (Nat.card K) ≤
      entropy (upload (p 0)) μ / Real.log (Nat.card K) + entropy (upload (p 1)) μ / Real.log (Nat.card K) +
      entropy (upload (p 2)) μ / Real.log (Nat.card K) := by
  have hq : (1 : ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
  have hlog := Real.log_pos hq
  have hb := code_retained_entropy_bound_ordered p task code T₀ split hdis₀₁ hdis₀₂ hdis₁₂ htri₂ htri₁ hbridge
  dsimp only at hb ⊢
  have hbq := (div_le_div_iff_of_pos_right hlog).mpr hb
  simp only [sub_div,add_div,mul_div_assoc] at hbq
  rw [joint_observation_entropy_rank _ _ _ hspan n,
    LinearObservation.model_entropy_rank,LinearObservation.model_entropy_rank,
    LinearObservation.model_entropy_rank] at hbq
  convert hbq using 1; ring


end CodeGeometry

section ExplicitResidual
attribute [local instance] sourceMeasurable sourceDiscrete
variable {K P₁ P₂ P₃ T L : Type*} [Field K] [Finite K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup T] [Module K T]
  [AddCommGroup L] [Module K L]
  [FiniteDimensional K P₁] [FiniteDimensional K P₂] [FiniteDimensional K P₃]
  [FiniteDimensional K T]
local notation "F₀" => ResidualUpload.Ambient P₁ P₂ P₃ T

/-- Operational residual minimum-upload converse in the explicit normal-form
coefficient model, for every nonlinear finite zero-error code and every
positive blocklength. Signal intersections, independence, Γ ranks, and local
slice recoveries are proved, rather than assumed as entropy hypotheses. -/
theorem explicit_residual_upload_lower_bound {n : ℕ} {M : Three → Type*} {S : Type*}
    (R : SignalBridge.Data (K := K) (F := F₀) (T := T)
      (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (L := L))
    (task : Task K F₀) (code : task.FiniteCode n M S)
    (hA₀ : task.A 0 = ResidualUpload.A₁ K P₁ P₂ P₃ T)
    (hA₁ : task.A 1 = ResidualUpload.A₂ K P₁ P₂ P₃ T)
    (hA₂ : task.A 2 = ResidualUpload.A₃ K P₁ P₂ P₃ T)
    (hU₀ : task.U 0 = R.U₁) (hU₁ : task.U 1 = R.U₂) (hU₂ : task.U 2 = R.U₃)
    (split : ∀ i : Three, PrivateSplit task i
      (![LinearMap.range R.v,LinearMap.range R.r,LinearMap.range (R.r-R.v)] i)) :
    (Module.finrank K P₁ : ℝ) + Module.finrank K P₂ + Module.finrank K P₃ +
      Module.finrank K T ≤ code.toCode.uploadCost := by
  classical
  letI (i : Three) : Finite (M i) := code.finite_upload i
  letI (i : Three) : Fintype (M i) := Fintype.ofFinite _
  letI (i : Three) : MeasurableSpace (M i) := ⊤
  letI (i : Three) : DiscreteMeasurableSpace (M i) := ⟨fun _ => trivial⟩
  let T₀ : Three → Submodule K F₀ :=
    ![LinearMap.range R.v,LinearMap.range R.r,LinearMap.range (R.r-R.v)]
  have hd₀₁ : Disjoint (task.A 0) (task.A 1) := by
    rw [hA₀,hA₁]
    exact ResidualUpload.sides_disjoint₁₂
  have hd₀₂ : Disjoint (task.A 0) (task.A 2) := by
    rw [hA₀,hA₂]
    exact ResidualUpload.sides_disjoint₁₃
  have hd₁₂ : Disjoint (task.A 1) (task.A 2) := by
    rw [hA₁,hA₂]
    exact ResidualUpload.sides_disjoint₂₃
  have ht₂ : T₀ 2 ≤ T₀ 0 ⊔ T₀ 1 := by
    rintro _ ⟨d,rfl⟩
    exact Submodule.sub_mem _ (Submodule.mem_sup_right ⟨d,rfl⟩) (Submodule.mem_sup_left ⟨d,rfl⟩)
  have ht₁ : T₀ 1 ≤ T₀ 0 ⊔ T₀ 2 := by
    rintro _ ⟨d,rfl⟩
    have hh := Submodule.add_mem_sup
      (show R.v d ∈ LinearMap.range R.v from ⟨d,rfl⟩)
      (show (R.r-R.v) d ∈ LinearMap.range (R.r-R.v) from ⟨d,rfl⟩)
    have he : R.v d + (R.r d - R.v d) = R.r d := by abel
    simpa only [LinearMap.sub_apply,he] using hh
  have hb : T₀ 0 ≤ task.U 2 ⊔ (task.U 0 ⊓ task.U 1) := by
    rw [hU₀,hU₁,hU₂]
    exact le_sup_left.trans (SignalBridge.tripod_le_signal_sup_inter R)
  have hs : task.A 0 ⊔ task.A 1 ⊔ task.A 2 = ⊤ := by
    rw [hA₀,hA₁,hA₂]
    exact ResidualUpload.sides_span
  have bound := code_rank_lower_bound task code.toCode T₀ split hd₀₁ hd₀₂ hd₁₂ ht₂ ht₁ hb hs
    code.positive_blocklength
  rw [hA₀,hA₁,hA₂] at bound
  have hg : 2 * (Module.finrank K F₀ : ℝ) -
      (Module.finrank K (ResidualUpload.A₁ K P₁ P₂ P₃ T) +
       Module.finrank K (ResidualUpload.A₂ K P₁ P₂ P₃ T) +
       Module.finrank K (ResidualUpload.A₃ K P₁ P₂ P₃ T)) =
      Module.finrank K P₁ + Module.finrank K P₂ + Module.finrank K P₃ + Module.finrank K T := by
    exact_mod_cast (ResidualUpload.gamma_rank (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := T))
  rw [hg] at bound
  exact bound
/-- The residual-three inequality with its two genuine conditional mutual
information terms retained, on the actual uniform residual block source. -/
theorem explicit_residual_retained_bound {n : ℕ} {M : Three → Type*} {S : Type*}
    [∀ i, MeasurableSpace (M i)] [∀ i, DiscreteMeasurableSpace (M i)]
    (R : SignalBridge.Data (K := K) (F := F₀) (T := T)
      (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (L := L))
    (task : Task K F₀) (code : task.FiniteCode n M S)
    (hA₀ : task.A 0 = ResidualUpload.A₁ K P₁ P₂ P₃ T)
    (hA₁ : task.A 1 = ResidualUpload.A₂ K P₁ P₂ P₃ T)
    (hA₂ : task.A 2 = ResidualUpload.A₃ K P₁ P₂ P₃ T)
    (hU₀ : task.U 0 = R.U₁) (hU₁ : task.U 1 = R.U₂) (hU₂ : task.U 2 = R.U₃)
    (split : ∀ i : Three, PrivateSplit task i
      (![LinearMap.range R.v,LinearMap.range R.r,LinearMap.range (R.r-R.v)] i)) :
    let μ := uniformOn (Set.univ : Set (Source K F₀ n))
    let W := fun i => UploadBroadcast.observe K F₀ (task.A i) (L := n)
    let upload := fun i x => code.encode i (W i x)
    (n:ℝ) * ((Module.finrank K P₁ : ℝ) + Module.finrank K P₂ + Module.finrank K P₃ + Module.finrank K T) +
      condMutualInfo (upload 1) (upload 2) (W 0) μ / Real.log (Nat.card K) +
      condMutualInfo (upload 0) (upload 2) (W 1) μ / Real.log (Nat.card K) ≤
      entropy (upload 0) μ / Real.log (Nat.card K) + entropy (upload 1) μ / Real.log (Nat.card K) +
      entropy (upload 2) μ / Real.log (Nat.card K) := by
  classical
  letI (i : Three) : Finite (M i) := code.finite_upload i
  letI (i : Three) : Fintype (M i) := Fintype.ofFinite _
  let T₀ : Three → Submodule K F₀ :=
    ![LinearMap.range R.v,LinearMap.range R.r,LinearMap.range (R.r-R.v)]
  have hd₀₁ : Disjoint (task.A 0) (task.A 1) := by
    rw [hA₀,hA₁]
    exact ResidualUpload.sides_disjoint₁₂
  have hd₀₂ : Disjoint (task.A 0) (task.A 2) := by
    rw [hA₀,hA₂]
    exact ResidualUpload.sides_disjoint₁₃
  have hd₁₂ : Disjoint (task.A 1) (task.A 2) := by
    rw [hA₁,hA₂]
    exact ResidualUpload.sides_disjoint₂₃
  have ht₂ : T₀ 2 ≤ T₀ 0 ⊔ T₀ 1 := by
    rintro _ ⟨d,rfl⟩
    exact Submodule.sub_mem _ (Submodule.mem_sup_right ⟨d,rfl⟩) (Submodule.mem_sup_left ⟨d,rfl⟩)
  have ht₁ : T₀ 1 ≤ T₀ 0 ⊔ T₀ 2 := by
    rintro _ ⟨d,rfl⟩
    have hh := Submodule.add_mem_sup
      (show R.v d ∈ LinearMap.range R.v from ⟨d,rfl⟩)
      (show (R.r-R.v) d ∈ LinearMap.range (R.r-R.v) from ⟨d,rfl⟩)
    have he : R.v d + (R.r d - R.v d) = R.r d := by abel
    simpa only [LinearMap.sub_apply,he] using hh
  have hb : T₀ 0 ≤ task.U 2 ⊔ (task.U 0 ⊓ task.U 1) := by
    rw [hU₀,hU₁,hU₂]
    exact le_sup_left.trans (SignalBridge.tripod_le_signal_sup_inter R)
  have hs : task.A 0 ⊔ task.A 1 ⊔ task.A 2 = ⊤ := by
    rw [hA₀,hA₁,hA₂]
    exact ResidualUpload.sides_span
  have bound := code_retained_rank_bound task code.toCode T₀ split hd₀₁ hd₀₂ hd₁₂ ht₂ ht₁ hb hs
  have hg : 2 * (Module.finrank K F₀ : ℝ) -
      (Module.finrank K (task.A 0) + Module.finrank K (task.A 1) + Module.finrank K (task.A 2)) =
      Module.finrank K P₁ + Module.finrank K P₂ + Module.finrank K P₃ + Module.finrank K T := by
    rw [hA₀,hA₁,hA₂]
    exact_mod_cast (ResidualUpload.gamma_rank (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := T))
  dsimp only at bound ⊢
  rw [hg] at bound
  exact bound

end ExplicitResidual

end UploadBroadcast.ResidualConverse
