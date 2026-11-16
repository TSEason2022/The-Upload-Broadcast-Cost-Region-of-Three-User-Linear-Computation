import UploadBroadcast.Shannon
import UploadBroadcast.Entropy
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring

/-! The omniscience lift, with the interaction bound derived from functional
recovery and independence in the Shannon entropy calculus. -/
namespace UploadBroadcast.EntropyFunction
variable {ι : Type*} [DecidableEq ι] (h : EntropyFunction ι)

/-- One user's omniscience interaction bound. The independence hypotheses are
on the residual observation and each remote upload together with Ω. -/
theorem omniscience_interaction (O S R M N : Finset ι)
    (side : h.Determines O S)
    (indM : h (R ∪ (O ∪ M)) = h R + h (O ∪ M))
    (indN : h (R ∪ (O ∪ N)) = h R + h (O ∪ N))
    (recover : h.Determines (R ∪ S ∪ M ∪ N) O) :
    h O - h S ≤ h.Mutual M O + h.Mutual N O + h.CondMutual M N (R ∪ O) := by
  have indO := h.independent_functions indM
    (h.determines_self R)
    (h.determines_of_subset (Finset.subset_union_left (s₁ := O) (s₂ := M)))
  have indS := h.independent_functions indO (h.determines_self R) side
  have rc : h.Determines (R ∪ S ∪ M ∪ N) (M ∪ N ∪ (R ∪ O)) := by
    apply h.determines_union
    · apply h.determines_union <;> apply h.determines_of_subset <;>
        intro x hx <;> simp only [Finset.mem_union] at * <;> tauto
    · exact h.determines_union (h.determines_of_subset (by
        intro x hx; simp only [Finset.mem_union]; tauto)) recover
  have hr := h.determines_le rc
  have hs := h.condMutual_nonneg M N (R ∪ S)
  have hm := h.subadd (R ∪ S) M
  have hn := h.subadd (R ∪ S) N
  unfold Mutual CondMutual at *
  have eM : M ∪ (R ∪ O) = R ∪ (O ∪ M) := by
    ext x; simp only [Finset.mem_union]; tauto
  have eN : N ∪ (R ∪ O) = R ∪ (O ∪ N) := by
    ext x; simp only [Finset.mem_union]; tauto
  have eMN : M ∪ N ∪ (R ∪ S) = R ∪ S ∪ M ∪ N := by
    ext x; simp only [Finset.mem_union]; tauto
  rw [eMN, Finset.union_comm M (R ∪ S), Finset.union_comm N (R ∪ S)] at hs
  rw [eM, eN, indM, indN, indO, Finset.union_comm M O, Finset.union_comm N O]
  rw [indS] at hs hm hn
  linarith

/-- Joint independence of Ω and the residual tuple plus pairwise residual
independence implies the remote-upload independence used above. -/
lemma independent_remote (O R T M : Finset ι)
    (ind : h (O ∪ (R ∪ T)) = h O + h (R ∪ T))
    (pair : h (R ∪ T) = h R + h T)
    (enc : h.Determines (O ∪ T) M) :
    h (R ∪ (O ∪ M)) = h R + h (O ∪ M) := by
  have indT := h.independent_functions ind (h.determines_self O)
    (h.determines_of_subset (Finset.subset_union_right (s₁ := R) (s₂ := T)))
  have e : R ∪ (O ∪ T) = O ∪ (R ∪ T) := by
    ext x; simp only [Finset.mem_union]; tauto
  have indRT : h (R ∪ (O ∪ T)) = h R + h (O ∪ T) := by
    rw [e, ind, pair, indT]; ring
  exact h.independent_functions indRT (h.determines_self R)
    (h.determines_union (h.determines_of_subset Finset.subset_union_left) enc)

lemma encode_enlarge (O S R M : Finset ι) (side : h.Determines O S)
    (enc : h.Determines (S ∪ R) M) : h.Determines (O ∪ R) M := by
  apply h.determines_trans _ enc
  exact h.determines_union
    (h.determines_mono_left side Finset.subset_union_left)
    (h.determines_of_subset Finset.subset_union_right)

/-- Lemma `omni-lift`: joint independence, pairwise residual independence,
local encoding, recovery, and the three residual bounds imply the full
omniscience-plus-residual lower bound. All quantities are entropies of sets
of observations, not free scalar variables. -/
theorem omniscience_lift
    (O S₁ S₂ S₃ R₁ R₂ R₃ M₁ M₂ M₃ : Finset ι) (Γ : ℝ)
    (joint : h (O ∪ (R₁ ∪ R₂ ∪ R₃)) = h O + h (R₁ ∪ R₂ ∪ R₃))
    (pair₁₂ : h (R₁ ∪ R₂) = h R₁ + h R₂)
    (pair₁₃ : h (R₁ ∪ R₃) = h R₁ + h R₃)
    (pair₂₃ : h (R₂ ∪ R₃) = h R₂ + h R₃)
    (side₁ : h.Determines O S₁) (side₂ : h.Determines O S₂)
    (side₃ : h.Determines O S₃)
    (enc₁ : h.Determines (S₁ ∪ R₁) M₁)
    (enc₂ : h.Determines (S₂ ∪ R₂) M₂)
    (enc₃ : h.Determines (S₃ ∪ R₃) M₃)
    (rec₁ : h.Determines (R₁ ∪ S₁ ∪ M₂ ∪ M₃) O)
    (rec₂ : h.Determines (R₂ ∪ S₂ ∪ M₁ ∪ M₃) O)
    (rec₃ : h.Determines (R₃ ∪ S₃ ∪ M₁ ∪ M₂) O)
    (bound₁₂ : Γ + h.CondMutual M₂ M₃ (R₁ ∪ O) + h.CondMutual M₁ M₃ (R₂ ∪ O) ≤
      h.condition O M₁ + h.condition O M₂ + h.condition O M₃)
    (bound₁₃ : Γ + h.CondMutual M₂ M₃ (R₁ ∪ O) + h.CondMutual M₁ M₂ (R₃ ∪ O) ≤
      h.condition O M₁ + h.condition O M₂ + h.condition O M₃)
    (bound₂₃ : Γ + h.CondMutual M₁ M₃ (R₂ ∪ O) + h.CondMutual M₁ M₂ (R₃ ∪ O) ≤
      h.condition O M₁ + h.condition O M₂ + h.condition O M₃) :
    Γ + max (max (h O - h S₁) (max (h O - h S₂) (h O - h S₃)))
      (((h O - h S₁) + (h O - h S₂) + (h O - h S₃)) / 2) ≤
      h M₁ + h M₂ + h M₃ := by
  have enc₁' := h.encode_enlarge O S₁ R₁ M₁ side₁ enc₁
  have enc₂' := h.encode_enlarge O S₂ R₂ M₂ side₂ enc₂
  have enc₃' := h.encode_enlarge O S₃ R₃ M₃ side₃ enc₃
  have joint' (A B : Finset ι) (sub : A ∪ B ⊆ R₁ ∪ R₂ ∪ R₃) :
      h (O ∪ (A ∪ B)) = h O + h (A ∪ B) :=
    h.independent_functions joint (h.determines_self O) (h.determines_of_subset sub)
  have j₁₂ := joint' R₁ R₂ (by intro x hx; simp only [Finset.mem_union] at *; tauto)
  have j₁₃ := joint' R₁ R₃ (by intro x hx; simp only [Finset.mem_union] at *; tauto)
  have j₂₃ := joint' R₂ R₃ (by intro x hx; simp only [Finset.mem_union] at *; tauto)
  have p₂₁ : h (R₂ ∪ R₁) = h R₂ + h R₁ := by rw [Finset.union_comm, pair₁₂]; ring
  have p₃₁ : h (R₃ ∪ R₁) = h R₃ + h R₁ := by rw [Finset.union_comm, pair₁₃]; ring
  have p₃₂ : h (R₃ ∪ R₂) = h R₃ + h R₂ := by rw [Finset.union_comm, pair₂₃]; ring
  have j₂₁ := joint' R₂ R₁ (by intro x hx; simp only [Finset.mem_union] at *; tauto)
  have j₃₁ := joint' R₃ R₁ (by intro x hx; simp only [Finset.mem_union] at *; tauto)
  have j₃₂ := joint' R₃ R₂ (by intro x hx; simp only [Finset.mem_union] at *; tauto)
  have d₁ := h.omniscience_interaction O S₁ R₁ M₂ M₃ side₁
    (h.independent_remote O R₁ R₂ M₂ j₁₂ pair₁₂ enc₂')
    (h.independent_remote O R₁ R₃ M₃ j₁₃ pair₁₃ enc₃') rec₁
  have d₂ := h.omniscience_interaction O S₂ R₂ M₁ M₃ side₂
    (h.independent_remote O R₂ R₁ M₁ j₂₁ p₂₁ enc₁')
    (h.independent_remote O R₂ R₃ M₃ j₂₃ pair₂₃ enc₃') rec₂
  have d₃ := h.omniscience_interaction O S₃ R₃ M₁ M₂ side₃
    (h.independent_remote O R₃ R₁ M₁ j₃₁ p₃₁ enc₁')
    (h.independent_remote O R₃ R₂ M₂ j₃₂ p₃₂ enc₂') rec₃
  apply Entropy.omniscience_scalar Γ
    (h.condition O M₁ + h.condition O M₂ + h.condition O M₃ - Γ)
    (h.Mutual M₁ O) (h.Mutual M₂ O) (h.Mutual M₃ O)
    (h.CondMutual M₂ M₃ (R₁ ∪ O)) (h.CondMutual M₁ M₃ (R₂ ∪ O))
    (h.CondMutual M₁ M₂ (R₃ ∪ O)) _ _ _ _
    (h.mutual_nonneg _ _) (h.mutual_nonneg _ _) (h.mutual_nonneg _ _)
    (h.condMutual_nonneg _ _ _) (h.condMutual_nonneg _ _ _) (h.condMutual_nonneg _ _ _)
    (by linarith) (by linarith) (by linarith) d₁ d₂ d₃
  change h M₁ + h M₂ + h M₃ = Γ +
    ((h (M₁ ∪ O) - h O) + (h (M₂ ∪ O) - h O) + (h (M₃ ∪ O) - h O) - Γ) +
    (h M₁ + h O - h (M₁ ∪ O)) + (h M₂ + h O - h (M₂ ∪ O)) +
    (h M₃ + h O - h (M₃ ∪ O))
  ring

end UploadBroadcast.EntropyFunction

namespace UploadBroadcast.Shannon
open MeasureTheory ProbabilityTheory
variable {Ω ι : Type*} [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  [Fintype ι] [DecidableEq ι]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ι → ℕ)

/-- Concrete finite-probability-space version of the omniscience lift.
Independence is `IndepFun`; encoding and recovery are actual conditional
entropy zero. Both the conclusion and residual hypotheses use actual PFR
Shannon entropy and conditional mutual information. -/
theorem omniscience_lift
    (O S₁ S₂ S₃ R₁ R₂ R₃ M₁ M₂ M₃ : Finset ι) (Γ : ℝ)
    (joint : IndepFun (observe X O) (observe X (R₁ ∪ R₂ ∪ R₃)) μ)
    (pair₁₂ : IndepFun (observe X R₁) (observe X R₂) μ)
    (pair₁₃ : IndepFun (observe X R₁) (observe X R₃) μ)
    (pair₂₃ : IndepFun (observe X R₂) (observe X R₃) μ)
    (side₁ : condEntropy (observe X S₁) (observe X O) μ = 0) (side₂ : condEntropy (observe X S₂) (observe X O) μ = 0)
    (side₃ : condEntropy (observe X S₃) (observe X O) μ = 0)
    (enc₁ : condEntropy (observe X M₁) (observe X (S₁ ∪ R₁)) μ = 0)
    (enc₂ : condEntropy (observe X M₂) (observe X (S₂ ∪ R₂)) μ = 0)
    (enc₃ : condEntropy (observe X M₃) (observe X (S₃ ∪ R₃)) μ = 0)
    (rec₁ : condEntropy (observe X O) (observe X (R₁ ∪ S₁ ∪ M₂ ∪ M₃)) μ = 0)
    (rec₂ : condEntropy (observe X O) (observe X (R₂ ∪ S₂ ∪ M₁ ∪ M₃)) μ = 0)
    (rec₃ : condEntropy (observe X O) (observe X (R₃ ∪ S₃ ∪ M₁ ∪ M₂)) μ = 0)
    (bound₁₂ : Γ + condMutualInfo (observe X M₂) (observe X M₃) (observe X (R₁ ∪ O)) μ + condMutualInfo (observe X M₁) (observe X M₃) (observe X (R₂ ∪ O)) μ ≤
      condEntropy (observe X M₁) (observe X O) μ + condEntropy (observe X M₂) (observe X O) μ + condEntropy (observe X M₃) (observe X O) μ)
    (bound₁₃ : Γ + condMutualInfo (observe X M₂) (observe X M₃) (observe X (R₁ ∪ O)) μ + condMutualInfo (observe X M₁) (observe X M₂) (observe X (R₃ ∪ O)) μ ≤
      condEntropy (observe X M₁) (observe X O) μ + condEntropy (observe X M₂) (observe X O) μ + condEntropy (observe X M₃) (observe X O) μ)
    (bound₂₃ : Γ + condMutualInfo (observe X M₁) (observe X M₃) (observe X (R₂ ∪ O)) μ + condMutualInfo (observe X M₁) (observe X M₂) (observe X (R₃ ∪ O)) μ ≤
      condEntropy (observe X M₁) (observe X O) μ + condEntropy (observe X M₂) (observe X O) μ + condEntropy (observe X M₃) (observe X O) μ) :
    Γ + max (max (condEntropy (observe X O) (observe X S₁) μ) (max (condEntropy (observe X O) (observe X S₂) μ) (condEntropy (observe X O) (observe X S₃) μ)))
      (((condEntropy (observe X O) (observe X S₁) μ) + (condEntropy (observe X O) (observe X S₂) μ) + (condEntropy (observe X O) (observe X S₃) μ)) / 2) ≤
      entropy (observe X M₁) μ + entropy (observe X M₂) μ + entropy (observe X M₃) μ := by
  have ind (A B : Finset ι) (hi : IndepFun (observe X A) (observe X B) μ) :
      (entropyFunction μ X) (A ∪ B) = (entropyFunction μ X) A + (entropyFunction μ X) B := by
    change value μ X (A ∪ B) = value μ X A + value μ X B
    rw [value_union]
    exact hi.entropy_pair_eq_add Measurable.of_discrete Measurable.of_discrete
  have deficit (S : Finset ι) (side : condEntropy (observe X S) (observe X O) μ = 0) :
      (entropyFunction μ X) O - (entropyFunction μ X) S =
        condEntropy (observe X O) (observe X S) μ := by
    rw [← condition_eq_condEntropy]
    have hh := (determines_iff μ X O S).mpr side
    change _ = (entropyFunction μ X) (O ∪ S) - (entropyFunction μ X) S
    rw [hh]
  have result := (entropyFunction μ X).omniscience_lift O S₁ S₂ S₃ R₁ R₂ R₃ M₁ M₂ M₃ Γ
    (ind _ _ joint) (ind _ _ pair₁₂) (ind _ _ pair₁₃) (ind _ _ pair₂₃)
    ((determines_iff μ X _ _).mpr side₁) ((determines_iff μ X _ _).mpr side₂)
    ((determines_iff μ X _ _).mpr side₃)
    ((determines_iff μ X _ _).mpr enc₁) ((determines_iff μ X _ _).mpr enc₂)
    ((determines_iff μ X _ _).mpr enc₃)
    ((determines_iff μ X _ _).mpr rec₁) ((determines_iff μ X _ _).mpr rec₂)
    ((determines_iff μ X _ _).mpr rec₃)
    (by simpa only [condMutual_eq, condition_eq_condEntropy] using bound₁₂)
    (by simpa only [condMutual_eq, condition_eq_condEntropy] using bound₁₃)
    (by simpa only [condMutual_eq, condition_eq_condEntropy] using bound₂₃)
  rw [deficit S₁ side₁, deficit S₂ side₂, deficit S₃ side₃] at result
  exact result

end UploadBroadcast.Shannon
