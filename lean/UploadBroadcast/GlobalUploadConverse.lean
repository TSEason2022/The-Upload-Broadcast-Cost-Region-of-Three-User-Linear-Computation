import UploadBroadcast.ResidualConverse
import UploadBroadcast.OmniscienceEntropy

/-! Direct-sum omniscience lift with residual common-function hypotheses
constructed from actual source observations and zero-error codes. -/
namespace UploadBroadcast.GlobalUploadConverse
open MeasureTheory ProbabilityTheory

section EntropyAssembly
variable {ι : Type*} [DecidableEq ι] (h : EntropyFunction ι)

theorem condition_cmi (O A B C : Finset ι) :
    (h.condition O).CondMutual A B C = h.CondMutual A B (C ∪ O) := by
  simp only [EntropyFunction.CondMutual,EntropyFunction.condition,Finset.union_assoc]
  ring

theorem cmi_comm (A B C : Finset ι) : h.CondMutual A B C = h.CondMutual B A C := by
  unfold EntropyFunction.CondMutual
  rw [Finset.union_comm A B]
  ring

/-- The three residual inequalities retain precisely the mutual information
conditioned on the original residual observations together with Ω. This
extraction precedes the omniscience lift and does not assume its conclusion. -/
theorem conditioned_retained_from_common (O : Finset ι) (R M T Θ : Three → Finset ι)
    (joint : h (O ∪ (R 0 ∪ R 1 ∪ R 2)) = h O + h (R 0 ∪ R 1 ∪ R 2))
    (pair : ∀ i j, i ≠ j → h (R i ∪ R j) = h (R i) + h (R j))
    (localEnc : ∀ i, (h.condition O).Determines (R i) (M i ∪ T i))
    (localDec : ∀ i, (h.condition O).Determines (M i ∪ T i) (R i))
    (tri : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (h.condition O).Determines (T i ∪ T j) (T k))
    (common : ∀ i k, i ≠ k → (h.condition O).Determines
      ((M 0 ∪ M 1 ∪ M 2) ∪ T i) (Θ k))
    (bridge : ∀ i k, i ≠ k → (h.condition O).Determines
      (((M 0 ∪ M 1 ∪ M 2) ∪ Θ k) ∪ T k) (T i)) :
    let Γ := 2 * h (R 0 ∪ R 1 ∪ R 2) - (h (R 0) + h (R 1) + h (R 2))
    let J : Three → ℝ := ![h.CondMutual (M 1) (M 2) (R 0 ∪ O),
      h.CondMutual (M 0) (M 2) (R 1 ∪ O), h.CondMutual (M 0) (M 1) (R 2 ∪ O)]
    ∀ i j, i ≠ j → Γ + J i + J j ≤
      (h.condition O) (M 0) + (h.condition O) (M 1) + (h.condition O) (M 2) := by
  let c := h.condition O
  have cond (A : Finset ι) (hA : A ⊆ R 0 ∪ R 1 ∪ R 2) : c A = h A := by
    have hi := h.independent_functions joint (h.determines_self O) (h.determines_of_subset hA)
    change h (A ∪ O)-h O = h A
    rw [Finset.union_comm A O,hi]
    ring
  have cr (i : Three) : c (R i) = h (R i) := by
    apply cond
    fin_cases i <;> intro a ha <;> simp only [Finset.mem_union] <;> tauto
  have cp (i j : Three) (hij : i ≠ j) : c (R i ∪ R j) = c (R i)+c (R j) := by
    rw [cond,cr,cr,pair i j hij]
    intro a ha
    rcases Finset.mem_union.mp ha with hi | hj
    · fin_cases i <;> simp only [Finset.mem_union] <;> tauto
    · fin_cases j <;> simp only [Finset.mem_union] <;> tauto
  have ct : c (R 0 ∪ R 1 ∪ R 2) = h (R 0 ∪ R 1 ∪ R 2) := cond _ (Finset.Subset.refl _)
  have common' (i j k : Three) (he : M i ∪ M j ∪ M k = M 0 ∪ M 1 ∪ M 2) :
      (i ≠ k → c.Determines ((M i ∪ M j ∪ M k) ∪ T i) (Θ k)) ∧
      (j ≠ k → c.Determines ((M i ∪ M j ∪ M k) ∪ T j) (Θ k)) ∧
      (i ≠ k → c.Determines (((M i ∪ M j ∪ M k) ∪ Θ k) ∪ T k) (T i)) := by
    rw [he]
    exact ⟨common i k,common j k,bridge i k⟩
  have b₀₁ := c.commonFunction (R 0) (R 1) (R 2) (M 0) (M 1) (M 2)
    (T 0) (T 1) (T 2) (Θ 2) (localEnc 0) (localEnc 1) (localEnc 2)
    (localDec 0) (localDec 1) (localDec 2) (cp 0 1 (by decide))
    (cp 0 2 (by decide)) (cp 1 2 (by decide)) (tri 0 1 2 (by decide) (by decide) (by decide))
    (tri 0 2 1 (by decide) (by decide) (by decide)) (common 0 2 (by decide))
    (common 1 2 (by decide)) (bridge 0 2 (by decide))
  have eq₀₂ : M 0 ∪ M 2 ∪ M 1 = M 0 ∪ M 1 ∪ M 2 := by
    ext a; simp only [Finset.mem_union]; tauto
  obtain ⟨co₀₂,co₂₀,br₀₂⟩ := common' 0 2 1 eq₀₂
  have b₀₂ := c.commonFunction (R 0) (R 2) (R 1) (M 0) (M 2) (M 1)
    (T 0) (T 2) (T 1) (Θ 1) (localEnc 0) (localEnc 2) (localEnc 1)
    (localDec 0) (localDec 2) (localDec 1) (cp 0 2 (by decide))
    (cp 0 1 (by decide)) (cp 2 1 (by decide)) (tri 0 2 1 (by decide) (by decide) (by decide))
    (tri 0 1 2 (by decide) (by decide) (by decide)) (co₀₂ (by decide))
    (co₂₀ (by decide)) (br₀₂ (by decide))
  have eq₁₂ : M 1 ∪ M 2 ∪ M 0 = M 0 ∪ M 1 ∪ M 2 := by
    ext a; simp only [Finset.mem_union]; tauto
  obtain ⟨co₁₂,co₂₁,br₁₂⟩ := common' 1 2 0 eq₁₂
  have b₁₂ := c.commonFunction (R 1) (R 2) (R 0) (M 1) (M 2) (M 0)
    (T 1) (T 2) (T 0) (Θ 0) (localEnc 1) (localEnc 2) (localEnc 0)
    (localDec 1) (localDec 2) (localDec 0) (cp 1 2 (by decide))
    (cp 1 0 (by decide)) (cp 2 0 (by decide)) (tri 1 2 0 (by decide) (by decide) (by decide))
    (tri 1 0 2 (by decide) (by decide) (by decide)) (co₁₂ (by decide))
    (co₂₁ (by decide)) (br₁₂ (by decide))
  have cm (i j k : Three) : c.CondMutual (M j) (M k) (M i ∪ T i) =
      h.CondMutual (M j) (M k) (R i ∪ O) := by
    rw [c.condMutual_congr_condition (localDec i) (localEnc i)]
    exact condition_cmi h O _ _ _
  simp only [cm] at b₀₁ b₀₂ b₁₂
  have er₀₂ : R 0 ∪ R 2 ∪ R 1 = R 0 ∪ R 1 ∪ R 2 := by
    ext a; simp only [Finset.mem_union]; tauto
  have er₁₂ : R 1 ∪ R 2 ∪ R 0 = R 0 ∪ R 1 ∪ R 2 := by
    ext a; simp only [Finset.mem_union]; tauto
  rw [er₀₂] at b₀₂
  rw [er₁₂] at b₁₂
  simp only [ct,cr] at b₀₁ b₀₂ b₁₂
  rw [cmi_comm h (M 2) (M 1)] at b₀₂
  rw [cmi_comm h (M 2) (M 0),cmi_comm h (M 1) (M 0)] at b₁₂
  simp only [Finset.union_assoc] at b₀₁ b₀₂ b₁₂
  dsimp only
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij ⊢ <;> linarith only [b₀₁, b₀₂, b₁₂]

/-- The full omniscience lift, deriving all three residual inequalities from
common functions. No residual entropy bound is an input. -/
theorem lift_from_common (O : Finset ι) (S R M T Θ : Three → Finset ι)
    (joint : h (O ∪ (R 0 ∪ R 1 ∪ R 2)) = h O + h (R 0 ∪ R 1 ∪ R 2))
    (pair : ∀ i j, i ≠ j → h (R i ∪ R j) = h (R i) + h (R j))
    (side : ∀ i, h.Determines O (S i))
    (encode : ∀ i, h.Determines (S i ∪ R i) (M i))
    (recover₀ : h.Determines (R 0 ∪ S 0 ∪ M 1 ∪ M 2) O)
    (recover₁ : h.Determines (R 1 ∪ S 1 ∪ M 0 ∪ M 2) O)
    (recover₂ : h.Determines (R 2 ∪ S 2 ∪ M 0 ∪ M 1) O)
    (localEnc : ∀ i, (h.condition O).Determines (R i) (M i ∪ T i))
    (localDec : ∀ i, (h.condition O).Determines (M i ∪ T i) (R i))
    (tri : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (h.condition O).Determines (T i ∪ T j) (T k))
    (common : ∀ i k, i ≠ k → (h.condition O).Determines
      ((M 0 ∪ M 1 ∪ M 2) ∪ T i) (Θ k))
    (bridge : ∀ i k, i ≠ k → (h.condition O).Determines
      (((M 0 ∪ M 1 ∪ M 2) ∪ Θ k) ∪ T k) (T i)) :
    (2 * h (R 0 ∪ R 1 ∪ R 2) - (h (R 0) + h (R 1) + h (R 2))) +
      max (max (h O-h (S 0)) (max (h O-h (S 1)) (h O-h (S 2))))
        (((h O-h (S 0))+(h O-h (S 1))+(h O-h (S 2)))/2) ≤
      h (M 0)+h (M 1)+h (M 2) := by
  have bounds := conditioned_retained_from_common h O R M T Θ joint pair
    localEnc localDec tri common bridge
  have b₀₁ := bounds 0 1 (by decide)
  have b₀₂ := bounds 0 2 (by decide)
  have b₁₂ := bounds 1 2 (by decide)
  apply h.omniscience_lift O (S 0) (S 1) (S 2) (R 0) (R 1) (R 2)
    (M 0) (M 1) (M 2) _ joint (pair 0 1 (by decide)) (pair 0 2 (by decide))
    (pair 1 2 (by decide)) (side 0) (side 1) (side 2) (encode 0) (encode 1) (encode 2)
    recover₀ recover₁ recover₂ b₀₁
  · simpa only [Matrix.cons_val_zero, Matrix.cons_val_succ] using b₀₂
  · simpa only [Matrix.cons_val_zero, Matrix.cons_val_succ] using b₁₂
end EntropyAssembly

section FiberTransport
variable {Ω ι A B C : Type*} [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  [Fintype ι] [DecidableEq ι]
  [MeasurableSpace A] [DiscreteMeasurableSpace A] [Countable A] [Nonempty A]
  [MeasurableSpace B] [DiscreteMeasurableSpace B] [Countable B] [Nonempty B]
  [MeasurableSpace C] [DiscreteMeasurableSpace C] [Countable C] [Nonempty C]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ι → ℕ)

omit [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] [Fintype ι]
  [MeasurableSpace A] [DiscreteMeasurableSpace A] [Countable A] [Nonempty A]
  [MeasurableSpace B] [DiscreteMeasurableSpace B] [Countable B] [Nonempty B] in
/-- Lossless coordinate encodings commute with pairing, at the level of fibers. -/
theorem union_fibers (S T : Finset ι) (f : Ω → A) (g : Ω → B)
    (hf : ∀ x y, (∀ i ∈ S, X x i = X y i) ↔ f x = f y)
    (hg : ∀ x y, (∀ i ∈ T, X x i = X y i) ↔ g x = g y) :
    ∀ x y, (∀ i ∈ S ∪ T, X x i = X y i) ↔ (f x,g x) = (f y,g y) := by
  intro x y
  simp only [Finset.mem_union, or_imp, forall_and, hf, hg, Prod.mk.injEq]

/-- Concrete Shannon entropy transport along a lossless coordinate encoding. -/
theorem value_of_fibers (S : Finset ι) (f : Ω → A)
    (hf : ∀ x y, (∀ i ∈ S, X x i = X y i) ↔ f x = f y) :
    (Shannon.entropyFunction μ X) S = entropy f μ := by
  apply ResidualConverse.entropy_eq_of_fibers
  intro x y
  exact (ResidualConverse.observe_eq_iff X S x y).trans (hf x y)

/-- Conditional entropy transport keeps the actual common observation. -/
theorem condition_of_fibers (S T : Finset ι) (f : Ω → A) (g : Ω → B)
    (hf : ∀ x y, (∀ i ∈ S, X x i = X y i) ↔ f x = f y)
    (hg : ∀ x y, (∀ i ∈ T, X x i = X y i) ↔ g x = g y) :
    ((Shannon.entropyFunction μ X).condition T) S = condEntropy f g μ := by
  change (Shannon.entropyFunction μ X) (S ∪ T) - (Shannon.entropyFunction μ X) T = _
  rw [value_of_fibers μ X _ _ (union_fibers X S T f g hf hg), value_of_fibers μ X T g hg]
  exact (chain_rule'' μ Measurable.of_discrete Measurable.of_discrete).symm

/-- Retained CMI transport keeps all three actual observations and their fibers. -/
theorem cmi_of_fibers (S T U : Finset ι) (f : Ω → A) (g : Ω → B) (k : Ω → C)
    (hf : ∀ x y, (∀ i ∈ S, X x i = X y i) ↔ f x = f y)
    (hg : ∀ x y, (∀ i ∈ T, X x i = X y i) ↔ g x = g y)
    (hk : ∀ x y, (∀ i ∈ U, X x i = X y i) ↔ k x = k y) :
    (Shannon.entropyFunction μ X).CondMutual S T U = condMutualInfo f g k μ := by
  unfold EntropyFunction.CondMutual
  rw [value_of_fibers μ X _ _ (union_fibers X S U f k hf hk),
    value_of_fibers μ X _ _ (union_fibers X T U g k hg hk), value_of_fibers μ X U k hk,
    value_of_fibers μ X _ _ (union_fibers X (S ∪ T) U (fun x => (f x,g x)) k
      (union_fibers X S T f g hf hg) hk)]
  rw [condMutualInfo_eq Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete μ,
    chain_rule'' μ Measurable.of_discrete Measurable.of_discrete,
    chain_rule'' μ Measurable.of_discrete Measurable.of_discrete,
    chain_rule'' μ Measurable.of_discrete Measurable.of_discrete]
  ring
end FiberTransport

section CodeGeometry
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Direct-sum coefficient geometry for the omniscience/residual split.
The common-function spaces are actual coefficient subspaces. -/
structure Geometry (task : Task K F) where
  O : Submodule K F
  S : Three → Submodule K F
  R : Three → Submodule K F
  T : Three → Submodule K F
  Θ : Three → Submodule K F
  side_eq : ∀ i, task.A i = S i ⊔ R i
  side_om : ∀ i, S i ≤ O
  demand_om : ∀ i, O ≤ task.U i
  tripod_le : ∀ i, T i ≤ R i
  om_disjoint : Disjoint O (R 0 ⊔ R 1 ⊔ R 2)
  residual_disjoint : ∀ i j, i ≠ j → Disjoint (R i) (R j)
  private_split : ∀ i, ResidualConverse.PrivateSplit task i (S i ⊔ T i)
  tripod_recovery : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → T k ≤ T i ⊔ T j
  common_le : ∀ i k, i ≠ k → Θ k ≤ task.U i
  common_bridge : ∀ i k, i ≠ k → T i ≤ task.U k ⊔ Θ k

abbrev Coord := Option (Three × Fin 5)
def oset : Finset Coord := {none}
def sset (i : Three) : Finset Coord := {some (i,0)}
def rset (i : Three) : Finset Coord := {some (i,1)}
def mset (i : Three) : Finset Coord := {some (i,2)}
def tset (i : Three) : Finset Coord := {some (i,3)}
def cset (i : Three) : Finset Coord := {some (i,4)}

local instance sourceMeasurable (E : Type*) [AddCommGroup E] [Module K E] (n : ℕ) :
    MeasurableSpace (Source K E n) := ⊤
local instance sourceDiscrete (E : Type*) [AddCommGroup E] [Module K E] (n : ℕ) :
    DiscreteMeasurableSpace (Source K E n) := ⟨fun _ => trivial⟩

variable [Finite K] [FiniteDimensional K F]
local instance sourceFinite (E : Type*) [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (n : ℕ) : Finite (Source K E n) := Module.finite_of_finite K
noncomputable def sourceFintype (E : Type*) [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (n : ℕ) : Fintype (Source K E n) := Fintype.ofFinite _
attribute [local instance] sourceFintype

/-- A source-level coefficient observation and an entropy-set observation with
the same fibers have the same actual Shannon entropy. -/
theorem value_of_linear_fibers {n : ℕ} (X : Source K F n → Coord → ℕ)
    (A : Finset Coord) (B : Submodule K F)
    (hf : ∀ x y, (∀ i ∈ A, X x i = X y i) ↔
      UploadBroadcast.observe K F B x = UploadBroadcast.observe K F B y) :
    Shannon.value (uniformOn (Set.univ : Set (Source K F n))) X A =
      entropy (UploadBroadcast.observe K F B (L := n))
        (uniformOn (Set.univ : Set (Source K F n))) := by
  letI : Finite (Source K F n) := Module.finite_of_finite K
  letI : Fintype (Source K F n) := Fintype.ofFinite _
  letI : Finite (Source K B n) := Module.finite_of_finite K
  apply ResidualConverse.entropy_eq_of_fibers
  intro x y
  exact (ResidualConverse.observe_eq_iff X A x y).trans (hf x y)

/-- Disjoint actual coefficient observations induce additive entropy on
any lossless set encoding of those observations. -/
theorem independent_of_linear_fibers {n : ℕ} (X : Source K F n → Coord → ℕ)
    (A C : Finset Coord) (B D : Submodule K F) (hBD : Disjoint B D)
    (hf : ∀ x y, (∀ i ∈ A, X x i = X y i) ↔
      UploadBroadcast.observe K F B x = UploadBroadcast.observe K F B y)
    (hg : ∀ x y, (∀ i ∈ C, X x i = X y i) ↔
      UploadBroadcast.observe K F D x = UploadBroadcast.observe K F D y) :
    let h := Shannon.entropyFunction (uniformOn (Set.univ : Set (Source K F n))) X
    h (A ∪ C) = h A + h C := by
  letI : Finite (Source K F n) := Module.finite_of_finite K
  letI : Fintype (Source K F n) := Fintype.ofFinite _
  letI : Finite (Source K B n) := Module.finite_of_finite K
  letI : Finite (Source K D n) := Module.finite_of_finite K
  have fa : Function.FactorsThrough (Shannon.observe X A) (UploadBroadcast.observe K F B (L := n)) := by
    intro x y he
    exact (ResidualConverse.observe_eq_iff X A x y).mpr ((hf x y).mpr he)
  have fc : Function.FactorsThrough (Shannon.observe X C) (UploadBroadcast.observe K F D (L := n)) := by
    intro x y he
    exact (ResidualConverse.observe_eq_iff X C x y).mpr ((hg x y).mpr he)
  obtain ⟨a,ha⟩ := (Function.factorsThrough_iff (Shannon.observe X A)).mp fa
  obtain ⟨c,hc⟩ := (Function.factorsThrough_iff (Shannon.observe X C)).mp fc
  have hi := (ResidualConverse.observations_independent B D hBD n).comp
    (Measurable.of_discrete (f := a)) (Measurable.of_discrete (f := c))
  rw [← ha,← hc] at hi
  change Shannon.value _ X (A ∪ C) = Shannon.value _ X A + Shannon.value _ X C
  rw [Shannon.value_union]
  exact hi.entropy_pair_eq_add Measurable.of_discrete Measurable.of_discrete

/-- The omniscience-plus-residual entropy bound for an actual arbitrary
nonlinear zero-error code. All conditional common functions and all three
residual bounds are derived internally from coefficient geometry. -/
theorem code_entropy_bounds {n : ℕ} {M : Three → Type*} {B : Type*}
    [∀ i, Fintype (M i)] [∀ i, MeasurableSpace (M i)] [∀ i, DiscreteMeasurableSpace (M i)]
    (task : Task K F) (g : Geometry task) (code : task.Code n M B) :
    let μ := uniformOn (Set.univ : Set (Source K F n))
    let obs := fun A : Submodule K F => UploadBroadcast.observe K F A (L := n)
    let msg := fun i x => code.encode i (obs (task.A i) x)
    ((2 * entropy (obs (g.R 0 ⊔ g.R 1 ⊔ g.R 2)) μ -
      (entropy (obs (g.R 0)) μ + entropy (obs (g.R 1)) μ + entropy (obs (g.R 2)) μ)) +
      max (max (entropy (obs g.O) μ-entropy (obs (g.S 0)) μ)
        (max (entropy (obs g.O) μ-entropy (obs (g.S 1)) μ)
          (entropy (obs g.O) μ-entropy (obs (g.S 2)) μ)))
        (((entropy (obs g.O) μ-entropy (obs (g.S 0)) μ)+
          (entropy (obs g.O) μ-entropy (obs (g.S 1)) μ)+
          (entropy (obs g.O) μ-entropy (obs (g.S 2)) μ))/2) ≤
      entropy (msg 0) μ + entropy (msg 1) μ + entropy (msg 2) μ) ∧
    (let Γ := 2 * entropy (obs (g.R 0 ⊔ g.R 1 ⊔ g.R 2)) μ -
      (entropy (obs (g.R 0)) μ + entropy (obs (g.R 1)) μ + entropy (obs (g.R 2)) μ)
     let J : Three → ℝ := ![
       condMutualInfo (msg 1) (msg 2) (fun x => (obs (g.R 0) x, obs g.O x)) μ,
       condMutualInfo (msg 0) (msg 2) (fun x => (obs (g.R 1) x, obs g.O x)) μ,
       condMutualInfo (msg 0) (msg 1) (fun x => (obs (g.R 2) x, obs g.O x)) μ]
     ∀ i j, i ≠ j → Γ + J i + J j ≤
       condEntropy (msg 0) (obs g.O) μ + condEntropy (msg 1) (obs g.O) μ +
         condEntropy (msg 2) (obs g.O) μ) := by
  classical
  letI (i : Three) : Nonempty (M i) := ⟨code.encode i 0⟩
  let μ := uniformOn (Set.univ : Set (Source K F n))
  let obs := fun A : Submodule K F => UploadBroadcast.observe K F A (L := n)
  let msg := fun i x => code.encode i (obs (task.A i) x)
  let X : Source K F n → Coord → ℕ := fun x c => match c with
    | none => FiniteAlphabet.encode (obs g.O x)
    | some (i,j) => ![FiniteAlphabet.encode (obs (g.S i) x),
        FiniteAlphabet.encode (obs (g.R i) x),FiniteAlphabet.encode (msg i x),
        FiniteAlphabet.encode (obs (g.T i) x),FiniteAlphabet.encode (obs (g.Θ i) x)] j
  let h := Shannon.entropyFunction μ X
  let c := h.condition oset
  have eo (x y : Source K F n) : X x none = X y none ↔ obs g.O x = obs g.O y := by
    simp [X,ResidualConverse.encode_eq_iff]
  have es (i : Three) (x y : Source K F n) : X x (some (i,0)) = X y (some (i,0)) ↔
      obs (g.S i) x = obs (g.S i) y := by simp [X,ResidualConverse.encode_eq_iff]
  have er (i : Three) (x y : Source K F n) : X x (some (i,1)) = X y (some (i,1)) ↔
      obs (g.R i) x = obs (g.R i) y := by simp [X,ResidualConverse.encode_eq_iff]
  have em (i : Three) (x y : Source K F n) : X x (some (i,2)) = X y (some (i,2)) ↔
      msg i x = msg i y := by simp [X,ResidualConverse.encode_eq_iff]
  have et (i : Three) (x y : Source K F n) : X x (some (i,3)) = X y (some (i,3)) ↔
      obs (g.T i) x = obs (g.T i) y := by simp [X,ResidualConverse.encode_eq_iff]
  have ec (i : Three) (x y : Source K F n) : X x (some (i,4)) = X y (some (i,4)) ↔
      obs (g.Θ i) x = obs (g.Θ i) y := by simp [X,ResidualConverse.encode_eq_iff]
  have det (A : Finset Coord) (j : Coord)
      (hf : ∀ x y, (∀ i ∈ A, X x i = X y i) → X x j = X y j) : h.Determines A {j} := by
    apply ResidualConverse.determines_of_coordinates μ X
    intro x y hh i hi
    have hi' : i = j := Finset.mem_singleton.mp hi
    subst i
    exact hf x y hh
  have cd (A : Finset Coord) (j : Coord)
      (hf : ∀ x y, (∀ i ∈ A ∪ oset, X x i = X y i) → X x j = X y j) : c.Determines A {j} := by
    apply (Shannon.condition_determines_iff μ X oset A {j}).mpr
    exact (Shannon.determines_iff μ X (A ∪ oset) {j}).mp (det _ _ hf)
  have fullSide (i : Three) (x y : Source K F n)
      (hs : obs (g.S i) x = obs (g.S i) y) (hr : obs (g.R i) x = obs (g.R i) y) :
      obs (task.A i) x = obs (task.A i) y :=
    ResidualConverse.observation_eq_of_le (by rw [g.side_eq i]) x y
      (ResidualConverse.observation_eq_sup _ _ x y hs hr)
  have localSide (i : Three) (x y : Source K F n) (hm : msg i x = msg i y)
      (ht : obs (g.T i) x = obs (g.T i) y) (ho : obs g.O x = obs g.O y) :
      obs (task.A i) x = obs (task.A i) y := by
    let p := g.private_split i
    obtain ⟨slice,hslice⟩ := SignalBridge.private_slice_inverse task code i p.P (g.S i ⊔ g.T i)
      p.projection p.on_private p.on_tripod p.side_eq p.on_others p.remote_span
    have hn := ResidualConverse.observation_eq_sup _ _ x y
      (ResidualConverse.observation_eq_of_le (g.side_om i) x y ho) ht
    change UploadBroadcast.observe K F (task.A i) x = UploadBroadcast.observe K F (task.A i) y
    rw [← hslice x,← hslice y]
    exact congrArg₂ slice hm hn
  have sig (i : Three) (x y : Source K F n) (hm : (fun j => msg j x) = (fun j => msg j y))
      (ht : obs (g.T i) x = obs (g.T i) y) (ho : obs g.O x = obs g.O y) :
      obs (task.U i) x = obs (task.U i) y := by
    have hs := localSide i x y (congrFun hm i) ht ho
    change UploadBroadcast.observe K F (task.U i) x = UploadBroadcast.observe K F (task.U i) y
    rw [← code.zero_error x i,← code.zero_error y i]
    change code.decode i (code.broadcast (fun j => msg j x)) (obs (task.A i) x) =
      code.decode i (code.broadcast (fun j => msg j y)) (obs (task.A i) y)
    rw [hm,hs]
  have hside (i : Three) : h.Determines oset (sset i) := by
    apply det
    intro x y hh
    exact (es i x y).mpr (ResidualConverse.observation_eq_of_le (g.side_om i) x y
      ((eo x y).mp (hh none (by simp [oset]))))
  have henc (i : Three) : h.Determines (sset i ∪ rset i) (mset i) := by
    apply det
    intro x y hh
    apply (em i x y).mpr
    apply congrArg (code.encode i)
    exact fullSide i x y ((es i x y).mp (hh (some (i,0)) (by simp [sset])))
      ((er i x y).mp (hh (some (i,1)) (by simp [rset])))
  have lenc (i : Three) : c.Determines (rset i) (mset i ∪ tset i) := by
    apply c.determines_union
    · apply cd
      intro x y hh
      apply (em i x y).mpr
      apply congrArg (code.encode i)
      exact fullSide i x y
        (ResidualConverse.observation_eq_of_le (g.side_om i) x y ((eo x y).mp (hh none (by simp [oset]))))
        ((er i x y).mp (hh (some (i,1)) (by simp [rset])))
    · apply cd
      intro x y hh
      exact (et i x y).mpr (ResidualConverse.observation_eq_of_le (g.tripod_le i) x y
        ((er i x y).mp (hh (some (i,1)) (by simp [rset]))))
  have ldec (i : Three) : c.Determines (mset i ∪ tset i) (rset i) := by
    apply cd
    intro x y hh
    apply (er i x y).mpr
    apply ResidualConverse.observation_eq_of_le (show g.R i ≤ task.A i by rw [g.side_eq i]; exact le_sup_right)
    exact localSide i x y ((em i x y).mp (hh (some (i,2)) (by simp [mset])))
      ((et i x y).mp (hh (some (i,3)) (by simp [tset]))) ((eo x y).mp (hh none (by simp [oset])))
  have htri (i j k : Three) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      c.Determines (tset i ∪ tset j) (tset k) := by
    apply cd
    intro x y hh
    exact (et k x y).mpr (ResidualConverse.observation_eq_of_le (g.tripod_recovery i j k hij hik hjk) x y
      (ResidualConverse.observation_eq_sup _ _ x y ((et i x y).mp (hh (some (i,3)) (by simp [tset])))
        ((et j x y).mp (hh (some (j,3)) (by simp [tset])))))
  have hcommon (i k : Three) (hik : i ≠ k) :
      c.Determines ((mset 0 ∪ mset 1 ∪ mset 2) ∪ tset i) (cset k) := by
    apply cd
    intro x y hh
    have hm : (fun j => msg j x) = (fun j => msg j y) := by
      funext j
      apply (em j x y).mp
      apply hh (some (j,2))
      fin_cases j <;> simp [mset]
    exact (ec k x y).mpr (ResidualConverse.observation_eq_of_le (g.common_le i k hik) x y
      (sig i x y hm ((et i x y).mp (hh (some (i,3)) (by simp [tset]))) ((eo x y).mp (hh none (by simp [oset])))))
  have hbridge (i k : Three) (hik : i ≠ k) :
      c.Determines (((mset 0 ∪ mset 1 ∪ mset 2) ∪ cset k) ∪ tset k) (tset i) := by
    apply cd
    intro x y hh
    have hm : (fun j => msg j x) = (fun j => msg j y) := by
      funext j
      apply (em j x y).mp
      apply hh (some (j,2))
      fin_cases j <;> simp [mset]
    exact (et i x y).mpr (ResidualConverse.observation_eq_of_le (g.common_bridge i k hik) x y
      (ResidualConverse.observation_eq_sup _ _ x y
        (sig k x y hm ((et k x y).mp (hh (some (k,3)) (by simp [tset]))) ((eo x y).mp (hh none (by simp [oset]))))
        ((ec k x y).mp (hh (some (k,4)) (by simp [cset])))))
  have rec (i j k : Three) (cover : ∀ l : Three, l = i ∨ l = j ∨ l = k) :
      h.Determines (rset i ∪ sset i ∪ mset j ∪ mset k) oset := by
    apply det
    intro x y hh
    have hs := fullSide i x y ((es i x y).mp (hh (some (i,0)) (by simp [sset])))
      ((er i x y).mp (hh (some (i,1)) (by simp [rset])))
    have hm : (fun l => msg l x) = (fun l => msg l y) := by
      funext l
      rcases cover l with he | he | he
      · subst l; exact congrArg (code.encode i) hs
      · subst l; exact (em j x y).mp (hh (some (j,2)) (by simp [mset]))
      · subst l; exact (em k x y).mp (hh (some (k,2)) (by simp [mset]))
    have hu : obs (task.U i) x = obs (task.U i) y := by
      change UploadBroadcast.observe K F (task.U i) x = UploadBroadcast.observe K F (task.U i) y
      rw [← code.zero_error x i,← code.zero_error y i]
      change code.decode i (code.broadcast (fun l => msg l x)) (obs (task.A i) x) =
        code.decode i (code.broadcast (fun l => msg l y)) (obs (task.A i) y)
      rw [hm,hs]
    exact (eo x y).mpr (ResidualConverse.observation_eq_of_le (g.demand_om i) x y hu)
  have fo (x y : Source K F n) : (∀ i ∈ oset, X x i = X y i) ↔ obs g.O x = obs g.O y := by
    simpa only [oset,Finset.mem_singleton,forall_eq] using eo x y
  have fr (i : Three) (x y : Source K F n) : (∀ j ∈ rset i, X x j = X y j) ↔
      obs (g.R i) x = obs (g.R i) y := by
    simpa only [rset,Finset.mem_singleton,forall_eq] using er i x y
  have fs (i : Three) (x y : Source K F n) : (∀ j ∈ sset i, X x j = X y j) ↔
      obs (g.S i) x = obs (g.S i) y := by
    simpa only [sset,Finset.mem_singleton,forall_eq] using es i x y
  have frs (x y : Source K F n) : (∀ j ∈ rset 0 ∪ rset 1 ∪ rset 2, X x j = X y j) ↔
      obs (g.R 0 ⊔ g.R 1 ⊔ g.R 2) x = obs (g.R 0 ⊔ g.R 1 ⊔ g.R 2) y := by
    constructor
    · intro hh
      exact ResidualConverse.observation_eq_sup _ _ x y
        (ResidualConverse.observation_eq_sup _ _ x y ((er 0 x y).mp (hh (some (0,1)) (by simp [rset])))
          ((er 1 x y).mp (hh (some (1,1)) (by simp [rset])))) ((er 2 x y).mp (hh (some (2,1)) (by simp [rset])))
    · intro hh j hj
      simp only [rset,Finset.mem_union,Finset.mem_singleton] at hj
      rcases hj with (rfl | rfl) | rfl
      · exact (er 0 x y).mpr (ResidualConverse.observation_eq_of_le (le_sup_left.trans le_sup_left) x y hh)
      · exact (er 1 x y).mpr (ResidualConverse.observation_eq_of_le (le_sup_right.trans le_sup_left) x y hh)
      · exact (er 2 x y).mpr (ResidualConverse.observation_eq_of_le le_sup_right x y hh)
  have joint := independent_of_linear_fibers X oset (rset 0 ∪ rset 1 ∪ rset 2)
    g.O (g.R 0 ⊔ g.R 1 ⊔ g.R 2) g.om_disjoint fo frs
  have pair (i j : Three) (hij : i ≠ j) := independent_of_linear_fibers X (rset i) (rset j)
    (g.R i) (g.R j) (g.residual_disjoint i j hij) (fr i) (fr j)
  have bound := lift_from_common h oset sset rset mset tset cset joint pair hside henc
    (rec 0 1 2 (by intro l; fin_cases l <;> simp))
    (rec 1 0 2 (by intro l; fin_cases l <;> simp))
    (rec 2 0 1 (by intro l; fin_cases l <;> simp)) lenc ldec htri hcommon hbridge
  have vo : h oset = entropy (obs g.O) μ := value_of_linear_fibers X _ _ fo
  have vr (i : Three) : h (rset i) = entropy (obs (g.R i)) μ := value_of_linear_fibers X _ _ (fr i)
  have vs (i : Three) : h (sset i) = entropy (obs (g.S i)) μ := value_of_linear_fibers X _ _ (fs i)
  have vrs : h (rset 0 ∪ rset 1 ∪ rset 2) = entropy (obs (g.R 0 ⊔ g.R 1 ⊔ g.R 2)) μ :=
    value_of_linear_fibers X _ _ frs
  have vm (i : Three) : h (mset i) = entropy (msg i) μ := by
    apply ResidualConverse.entropy_eq_of_fibers
    intro x y
    rw [ResidualConverse.observe_eq_iff]
    simpa only [mset,Finset.mem_singleton,forall_eq] using em i x y
  refine ⟨?_, ?_⟩
  · simpa only [vo,vr,vs,vrs,vm] using bound
  · have fm (i : Three) (x y : Source K F n) :
        (∀ j ∈ mset i, X x j = X y j) ↔ msg i x = msg i y := by
      simpa only [mset,Finset.mem_singleton,forall_eq] using em i x y
    have vc (i : Three) : (h.condition oset) (mset i) = condEntropy (msg i) (obs g.O) μ :=
      condition_of_fibers μ X (mset i) oset (msg i) (obs g.O) (fm i) fo
    have vj (i j k : Three) : h.CondMutual (mset j) (mset k) (rset i ∪ oset) =
        condMutualInfo (msg j) (msg k) (fun x => (obs (g.R i) x, obs g.O x)) μ :=
      cmi_of_fibers μ X (mset j) (mset k) (rset i ∪ oset) (msg j) (msg k)
        (fun x => (obs (g.R i) x, obs g.O x)) (fm j) (fm k)
        (union_fibers X (rset i) oset (obs (g.R i)) (obs g.O) (fr i) fo)
    have bounds := conditioned_retained_from_common h oset rset mset tset cset joint pair
      lenc ldec htri hcommon hbridge
    dsimp only at bounds ⊢
    simpa only [vj, vr, vrs, vc] using bounds

/-- The omniscience component of the joint-code entropy bounds. -/
theorem code_omniscience_entropy_bound {n : ℕ} {M : Three → Type*} {B : Type*}
    [∀ i, Fintype (M i)] [∀ i, MeasurableSpace (M i)] [∀ i, DiscreteMeasurableSpace (M i)]
    (task : Task K F) (g : Geometry task) (code : task.Code n M B) :
    let μ := uniformOn (Set.univ : Set (Source K F n))
    let obs := fun A : Submodule K F => UploadBroadcast.observe K F A (L := n)
    let msg := fun i x => code.encode i (obs (task.A i) x)
    (2 * entropy (obs (g.R 0 ⊔ g.R 1 ⊔ g.R 2)) μ -
      (entropy (obs (g.R 0)) μ + entropy (obs (g.R 1)) μ + entropy (obs (g.R 2)) μ)) +
      max (max (entropy (obs g.O) μ-entropy (obs (g.S 0)) μ)
        (max (entropy (obs g.O) μ-entropy (obs (g.S 1)) μ)
          (entropy (obs g.O) μ-entropy (obs (g.S 2)) μ)))
        (((entropy (obs g.O) μ-entropy (obs (g.S 0)) μ)+
          (entropy (obs g.O) μ-entropy (obs (g.S 1)) μ)+
          (entropy (obs g.O) μ-entropy (obs (g.S 2)) μ))/2) ≤
      entropy (msg 0) μ + entropy (msg 1) μ + entropy (msg 2) μ := by
  exact (code_entropy_bounds task g code).1

/-- All three Ω-conditioned residual inequalities for an arbitrary jointly
encoded nonlinear code. The retained CMI conditions on the actual original
residual side observation and Ω, not on a hypothetical residual-only encoder. -/
theorem code_conditioned_retained_entropy_bounds {n : ℕ} {M : Three → Type*} {B : Type*}
    [∀ i, Fintype (M i)] [∀ i, MeasurableSpace (M i)] [∀ i, DiscreteMeasurableSpace (M i)]
    (task : Task K F) (g : Geometry task) (code : task.Code n M B) :
    let μ := uniformOn (Set.univ : Set (Source K F n))
    let obs := fun A : Submodule K F => UploadBroadcast.observe K F A (L := n)
    let msg := fun i x => code.encode i (obs (task.A i) x)
    let Γ := 2 * entropy (obs (g.R 0 ⊔ g.R 1 ⊔ g.R 2)) μ -
      (entropy (obs (g.R 0)) μ + entropy (obs (g.R 1)) μ + entropy (obs (g.R 2)) μ)
    let J : Three → ℝ := ![
      condMutualInfo (msg 1) (msg 2) (fun x => (obs (g.R 0) x, obs g.O x)) μ,
      condMutualInfo (msg 0) (msg 2) (fun x => (obs (g.R 1) x, obs g.O x)) μ,
      condMutualInfo (msg 0) (msg 1) (fun x => (obs (g.R 2) x, obs g.O x)) μ]
    ∀ i j, i ≠ j → Γ + J i + J j ≤
      condEntropy (msg 0) (obs g.O) μ + condEntropy (msg 1) (obs g.O) μ +
        condEntropy (msg 2) (obs g.O) μ := by
  exact (code_entropy_bounds task g code).2

/-- Q-ary form of all three joint-code residual inequalities, with Γ
computed from the actual residual coefficient ranks. -/
theorem code_conditioned_retained_rank_bounds {n : ℕ} {M : Three → Type*} {B : Type*}
    [∀ i, Fintype (M i)] [∀ i, MeasurableSpace (M i)] [∀ i, DiscreteMeasurableSpace (M i)]
    (task : Task K F) (g : Geometry task) (code : task.Code n M B) :
    let μ := uniformOn (Set.univ : Set (Source K F n))
    let obs := fun A : Submodule K F => UploadBroadcast.observe K F A (L := n)
    let msg := fun i x => code.encode i (obs (task.A i) x)
    let q := Real.log (Nat.card K)
    let Γ := (n : ℝ) * (2 * (Module.finrank K ↥(g.R 0 ⊔ g.R 1 ⊔ g.R 2) : ℝ) -
      (Module.finrank K (g.R 0) + Module.finrank K (g.R 1) + Module.finrank K (g.R 2)))
    let J : Three → ℝ := ![
      condMutualInfo (msg 1) (msg 2) (fun x => (obs (g.R 0) x, obs g.O x)) μ / q,
      condMutualInfo (msg 0) (msg 2) (fun x => (obs (g.R 1) x, obs g.O x)) μ / q,
      condMutualInfo (msg 0) (msg 1) (fun x => (obs (g.R 2) x, obs g.O x)) μ / q]
    ∀ i j, i ≠ j → Γ + J i + J j ≤
      condEntropy (msg 0) (obs g.O) μ / q + condEntropy (msg 1) (obs g.O) μ / q +
        condEntropy (msg 2) (obs g.O) μ / q := by
  classical
  let μ := uniformOn (Set.univ : Set (Source K F n))
  let obs := fun A : Submodule K F => UploadBroadcast.observe K F A (L := n)
  let msg := fun i x => code.encode i (obs (task.A i) x)
  let q := Real.log (Nat.card K)
  have hq : 0 < q := Real.log_pos (by exact_mod_cast (Finite.one_lt_card (α := K)))
  have norm (A : Submodule K F) : entropy (obs A) μ / q = (n : ℝ) * Module.finrank K A :=
    LinearObservation.model_entropy_rank A n
  have hg : (2 * entropy (obs (g.R 0 ⊔ g.R 1 ⊔ g.R 2)) μ -
      (entropy (obs (g.R 0)) μ + entropy (obs (g.R 1)) μ + entropy (obs (g.R 2)) μ)) / q =
      (n : ℝ) * (2 * (Module.finrank K ↥(g.R 0 ⊔ g.R 1 ⊔ g.R 2) : ℝ) -
        (Module.finrank K (g.R 0) + Module.finrank K (g.R 1) + Module.finrank K (g.R 2))) := by
    simp only [sub_div, add_div, mul_div_assoc, norm]
    ring
  dsimp only [obs, μ] at hg
  have hb := code_conditioned_retained_entropy_bounds task g code
  dsimp only at hb ⊢
  intro i j hij
  have hd := (div_le_div_iff_of_pos_right hq).mpr (hb i j hij)
  simp only [add_div, hg] at hd
  have vec (a b c : ℝ) (k : Three) : ![a,b,c] k / q = ![a/q,b/q,c/q] k := by
    fin_cases k <;> rfl
  simpa only [vec] using hd

/-- The intrinsic residual-rank plus omniscience-deficit expression. -/
noncomputable def Geometry.rankBound {task : Task K F} (g : Geometry task) : ℝ :=
  (2 * (Module.finrank K ↥(g.R 0 ⊔ g.R 1 ⊔ g.R 2) : ℝ) -
    (Module.finrank K (g.R 0)+Module.finrank K (g.R 1)+Module.finrank K (g.R 2))) +
  max (max ((Module.finrank K g.O : ℝ)-Module.finrank K (g.S 0))
    (max ((Module.finrank K g.O : ℝ)-Module.finrank K (g.S 1))
      ((Module.finrank K g.O : ℝ)-Module.finrank K (g.S 2))))
    ((((Module.finrank K g.O : ℝ)-Module.finrank K (g.S 0))+
      ((Module.finrank K g.O : ℝ)-Module.finrank K (g.S 1))+
      ((Module.finrank K g.O : ℝ)-Module.finrank K (g.S 2)))/2)

/-- Actual global fixed-length upload lower bound. Ω conditioning, the three
residual inequalities, and the omniscience interaction bound are all proved
inside the entropy assembly; only coefficient geometry is supplied. -/
theorem code_upload_lower_bound {n : ℕ} {M : Three → Type*} {B : Type*}
    (task : Task K F) (g : Geometry task) (code : task.FiniteCode n M B) :
    g.rankBound ≤ code.toCode.uploadCost := by
  classical
  letI (i : Three) : Finite (M i) := code.finite_upload i
  letI (i : Three) : Fintype (M i) := Fintype.ofFinite _
  letI (i : Three) : MeasurableSpace (M i) := ⊤
  letI (i : Three) : DiscreteMeasurableSpace (M i) := ⟨fun _ => trivial⟩
  let μ := uniformOn (Set.univ : Set (Source K F n))
  let H := fun A : Submodule K F => entropy (UploadBroadcast.observe K F A (L := n)) μ
  let msg := fun i x => code.encode i (UploadBroadcast.observe K F (task.A i) x)
  let q := Real.log (Nat.card K)
  let d := (n:ℝ)*q
  have hn : (0:ℝ) < n := by exact_mod_cast code.positive_blocklength
  have hq : 0 < q := by
    apply Real.log_pos
    exact_mod_cast (Finite.one_lt_card (α := K))
  have hd : 0 < d := mul_pos hn hq
  have norm (A : Submodule K F) : H A / d = Module.finrank K A := by
    change entropy (UploadBroadcast.observe K F A (L := n)) μ / ((n:ℝ)*q) = _
    rw [mul_comm (n:ℝ) q,← div_div]
    change (entropy (UploadBroadcast.observe K F A (L := n)) μ / Real.log (Nat.card K)) / (n:ℝ) = _
    rw [LinearObservation.model_entropy_rank]
    simp [ne_of_gt hn]
  let Γ := 2*H (g.R 0 ⊔ g.R 1 ⊔ g.R 2)-(H (g.R 0)+H (g.R 1)+H (g.R 2))
  let δ := fun i => H g.O-H (g.S i)
  have ng : Γ/d = 2*(Module.finrank K ↥(g.R 0 ⊔ g.R 1 ⊔ g.R 2):ℝ)-
      (Module.finrank K (g.R 0)+Module.finrank K (g.R 1)+Module.finrank K (g.R 2)) := by
    simp only [Γ,sub_div,add_div,mul_div_assoc,norm]
  have nd (i : Three) : δ i/d = (Module.finrank K g.O : ℝ)-Module.finrank K (g.S i) := by
    simp only [δ,sub_div,norm]
  have nh : ((δ 0+δ 1+δ 2)/2)/d =
      (((Module.finrank K g.O : ℝ)-Module.finrank K (g.S 0))+
       ((Module.finrank K g.O : ℝ)-Module.finrank K (g.S 1))+
       ((Module.finrank K g.O : ℝ)-Module.finrank K (g.S 2)))/2 := by
    rw [div_right_comm]
    simp only [add_div,nd]
  have hb := code_omniscience_entropy_bound task g code.toCode
  change Γ + max (max (δ 0) (max (δ 1) (δ 2))) ((δ 0+δ 1+δ 2)/2) ≤
    entropy (msg 0) μ+entropy (msg 1) μ+entropy (msg 2) μ at hb
  have hbq := (div_le_div_iff_of_pos_right hd).mpr hb
  rw [add_div] at hbq
  simp only [← max_div_div_right hd.le] at hbq
  rw [ng,nd,nd,nd,nh] at hbq
  have cap (i : Three) : entropy (msg i) μ/q ≤
      Real.logb (Nat.card K) (Nat.card (Set.range (code.encode i))) := by
    have he : Set.range (msg i) = Set.range (code.encode i) := by
      ext a
      constructor
      · rintro ⟨x,rfl⟩; exact ⟨UploadBroadcast.observe K F (task.A i) x,rfl⟩
      · rintro ⟨w,rfl⟩
        obtain ⟨x,hx⟩ := w.exists_extend
        exact ⟨x,congrArg (code.encode i) hx⟩
    have hi := entropy_div_log_le_logb_attainable μ (msg i) Measurable.of_discrete (Nat.card K)
      (by exact_mod_cast (Finite.one_lt_card (α := K)))
    simpa only [he] using hi
  have hc : (entropy (msg 0) μ+entropy (msg 1) μ+entropy (msg 2) μ)/d ≤ code.toCode.uploadCost := by
    change (entropy (msg 0) μ+entropy (msg 1) μ+entropy (msg 2) μ)/((n:ℝ)*q) ≤
      (∑ i, Real.logb (Nat.card K) (Nat.card (Set.range (code.encode i))))/(n:ℝ)
    rw [mul_comm (n:ℝ) q,← div_div]
    apply div_le_div_of_nonneg_right _ hn.le
    rw [Fin.sum_univ_three]
    simp only [add_div]
    linarith [cap 0,cap 1,cap 2]
  exact hbq.trans hc

end CodeGeometry

end UploadBroadcast.GlobalUploadConverse
