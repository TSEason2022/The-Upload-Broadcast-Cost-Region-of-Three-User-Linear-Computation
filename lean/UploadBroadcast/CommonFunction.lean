import UploadBroadcast.EntropyCalculus
import UploadBroadcast.Entropy
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-! The common-function converse in the general entropy calculus. Every
hypothesis is a functional-dependence or independence hypothesis from the
paper. The concrete Shannon instance is constructed in `Shannon.lean`. -/
namespace UploadBroadcast.EntropyFunction
variable {ι : Type*} [DecidableEq ι] (h : EntropyFunction ι)

/-- The common-function entropy bound, before conditioning. Applying this
result to `h.condition Ω` gives the paper's bound conditioned on Ω.
`Wᵢ` denotes `(Yᵢ,Tᵢ)`; local encoding and local recovery are expressed as
mutual determination of `Wᵢ` and `(Mᵢ,Tᵢ)`. -/
theorem commonFunction
    (W₁ W₂ W₃ M₁ M₂ M₃ T₁ T₂ T₃ Θ : Finset ι)
    (enc₁ : h.Determines W₁ (M₁ ∪ T₁))
    (enc₂ : h.Determines W₂ (M₂ ∪ T₂))
    (enc₃ : h.Determines W₃ (M₃ ∪ T₃))
    (dec₁ : h.Determines (M₁ ∪ T₁) W₁)
    (dec₂ : h.Determines (M₂ ∪ T₂) W₂)
    (dec₃ : h.Determines (M₃ ∪ T₃) W₃)
    (ind₁₂ : h (W₁ ∪ W₂) = h W₁ + h W₂)
    (ind₁₃ : h (W₁ ∪ W₃) = h W₁ + h W₃)
    (ind₂₃ : h (W₂ ∪ W₃) = h W₂ + h W₃)
    (tri₃ : h.Determines (T₁ ∪ T₂) T₃)
    (tri₂ : h.Determines (T₁ ∪ T₃) T₂)
    (common₁ : h.Determines ((M₁ ∪ M₂ ∪ M₃) ∪ T₁) Θ)
    (common₂ : h.Determines ((M₁ ∪ M₂ ∪ M₃) ∪ T₂) Θ)
    (bridge : h.Determines (((M₁ ∪ M₂ ∪ M₃) ∪ Θ) ∪ T₃) T₁) :
    2 * h (W₁ ∪ W₂ ∪ W₃) - (h W₁ + h W₂ + h W₃) +
      h.CondMutual M₂ M₃ (M₁ ∪ T₁) + h.CondMutual M₁ M₃ (M₂ ∪ T₂) ≤
      h M₁ + h M₂ + h M₃ := by
  let S := W₁ ∪ W₂ ∪ W₃
  let M := M₁ ∪ M₂ ∪ M₃
  let A := M ∪ T₁ ∪ T₂
  let B := M ∪ Θ ∪ T₃
  have sw₁ : h.Determines S W₁ := h.determines_of_subset (by
    intro x hx; simp only [S, Finset.mem_union]; tauto)
  have sw₂ : h.Determines S W₂ := h.determines_of_subset (by
    intro x hx; simp only [S, Finset.mem_union]; tauto)
  have sw₃ : h.Determines S W₃ := h.determines_of_subset (by
    intro x hx; simp only [S, Finset.mem_union]; tauto)
  have sb₁ := h.determines_trans sw₁ enc₁
  have sb₂ := h.determines_trans sw₂ enc₂
  have sb₃ := h.determines_trans sw₃ enc₃
  have sm₁ := h.determines_mono_right sb₁ Finset.subset_union_left
  have sm₂ := h.determines_mono_right sb₂ Finset.subset_union_left
  have sm₃ := h.determines_mono_right sb₃ Finset.subset_union_left
  have st₁ := h.determines_mono_right sb₁ Finset.subset_union_right
  have st₂ := h.determines_mono_right sb₂ Finset.subset_union_right
  have st₃ := h.determines_mono_right sb₃ Finset.subset_union_right
  have sm : h.Determines S M := h.determines_union (h.determines_union sm₁ sm₂) sm₃
  have sa : h.Determines S A := h.determines_union (h.determines_union sm st₁) st₂
  have sθ := h.determines_trans (h.determines_union sm st₁) common₁
  have sb : h.Determines S B := h.determines_union (h.determines_union sm sθ) st₃
  have at₃ : h.Determines A T₃ := h.determines_mono_left tri₃ (by
    intro x hx; simp only [A, Finset.mem_union] at *; tauto)
  have aw₁ : h.Determines A W₁ := h.determines_mono_left dec₁ (by
    intro x hx; simp only [A, M, Finset.mem_union] at *; tauto)
  have aw₂ : h.Determines A W₂ := h.determines_mono_left dec₂ (by
    intro x hx; simp only [A, M, Finset.mem_union] at *; tauto)
  have am₃ : h.Determines A M₃ := h.determines_of_subset (by
    intro x hx; simp only [A, M, Finset.mem_union]; tauto)
  have aw₃ := h.determines_trans (h.determines_union am₃ at₃) dec₃
  have aS : h.Determines A S := h.determines_union (h.determines_union aw₁ aw₂) aw₃
  have ha : h A = h S := h.eq_of_mutual_determines aS sa
  have bt₁ : h.Determines B T₁ := bridge
  have bt₃ : h.Determines B T₃ := h.determines_of_subset Finset.subset_union_right
  have bt₂ := h.determines_trans (h.determines_union bt₁ bt₃) tri₂
  have bm : h.Determines B M := h.determines_of_subset (by
    intro x hx; simp only [B, Finset.mem_union]; tauto)
  have ba : h.Determines B A := h.determines_union (h.determines_union bm bt₁) bt₂
  have bS := h.determines_trans ba aS
  have hb : h B = h S := h.eq_of_mutual_determines bS sb
  have hc₁ : h.Determines (M ∪ T₁) (M ∪ Θ) :=
    h.determines_union (h.determines_of_subset Finset.subset_union_left) common₁
  have hc₂ : h.Determines (M ∪ T₂) (M ∪ Θ) :=
    h.determines_union (h.determines_of_subset Finset.subset_union_left) common₂
  have hfunctional := h.functional_submod hc₁ hc₂
  have hab : (M ∪ T₁) ∪ (M ∪ T₂) = A := by
    ext x; simp only [A, Finset.mem_union]; tauto
  rw [hab, ha] at hfunctional
  have htail := h.increment_antitone (C := T₃) (A := M₃) (B := M ∪ Θ) (by
    intro x hx; simp only [M, Finset.mem_union]; tauto)
  have hb₁ : h (M₁ ∪ T₁) = h W₁ := h.eq_of_mutual_determines dec₁ enc₁
  have hb₂ : h (M₂ ∪ T₂) = h W₂ := h.eq_of_mutual_determines dec₂ enc₂
  have hb₃ : h (M₃ ∪ T₃) = h W₃ := h.eq_of_mutual_determines dec₃ enc₃
  change h B - h (M ∪ Θ) ≤ _ at htail
  rw [hb, hb₃] at htail
  have hbridge : 2 * h S - h W₃ + h M₃ ≤ h (M ∪ T₁) + h (M ∪ T₂) := by
    linarith
  have em₁ := h.determines_mono_right enc₁ Finset.subset_union_left
  have em₂ := h.determines_mono_right enc₂ Finset.subset_union_left
  have em₃ := h.determines_mono_right enc₃ Finset.subset_union_left
  have ei₁₂ := h.independent_functions ind₁₂ enc₁ em₂
  have ei₁₃ := h.independent_functions ind₁₃ enc₁ em₃
  have ind₂₁ : h (W₂ ∪ W₁) = h W₂ + h W₁ := by rw [Finset.union_comm, ind₁₂, add_comm]
  have ei₂₁ := h.independent_functions ind₂₁ enc₂ em₁
  have ei₂₃ := h.independent_functions ind₂₃ enc₂ em₃
  have hexp₁ : h (M ∪ T₁) = h W₁ + h M₂ + h M₃ - h.CondMutual M₂ M₃ (M₁ ∪ T₁) := by
    unfold CondMutual
    have e₁ : M₂ ∪ (M₁ ∪ T₁) = (M₁ ∪ T₁) ∪ M₂ := Finset.union_comm _ _
    have e₂ : M₃ ∪ (M₁ ∪ T₁) = (M₁ ∪ T₁) ∪ M₃ := Finset.union_comm _ _
    have e₃ : M₂ ∪ M₃ ∪ (M₁ ∪ T₁) = M ∪ T₁ := by
      ext x; simp only [M, Finset.mem_union]; tauto
    rw [e₁, e₂, e₃, ei₁₂, ei₁₃, hb₁]
    ring
  have hexp₂ : h (M ∪ T₂) = h W₂ + h M₁ + h M₃ - h.CondMutual M₁ M₃ (M₂ ∪ T₂) := by
    unfold CondMutual
    have e₁ : M₁ ∪ (M₂ ∪ T₂) = (M₂ ∪ T₂) ∪ M₁ := Finset.union_comm _ _
    have e₂ : M₃ ∪ (M₂ ∪ T₂) = (M₂ ∪ T₂) ∪ M₃ := Finset.union_comm _ _
    have e₃ : M₁ ∪ M₃ ∪ (M₂ ∪ T₂) = M ∪ T₂ := by
      ext x; simp only [M, Finset.mem_union]; tauto
    rw [e₁, e₂, e₃, ei₂₁, ei₂₃, hb₂]
    ring
  exact Entropy.commonFunction_scalar _ _ _ _ _ _ _ _ _ _ _ hbridge hexp₁ hexp₂

end UploadBroadcast.EntropyFunction
