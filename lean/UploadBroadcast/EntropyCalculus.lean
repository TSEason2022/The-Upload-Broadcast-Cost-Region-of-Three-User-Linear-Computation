import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Empty
import Mathlib.Tactic.Linarith
import Aesop

/-! A reusable calculus for normalized monotone submodular set functions.
`Shannon.lean` constructs an instance from actual finite probability spaces. -/

namespace UploadBroadcast

structure EntropyFunction (ι : Type*) [DecidableEq ι] where
  value : Finset ι → ℝ
  empty : value ∅ = 0
  mono : Monotone value
  submod : ∀ A B, value (A ∪ B) + value (A ∩ B) ≤ value A + value B

namespace EntropyFunction
variable {ι : Type*} [DecidableEq ι] (h : EntropyFunction ι)

instance : CoeFun (EntropyFunction ι) (fun _ => Finset ι → ℝ) := ⟨value⟩

/-- The observations in `B` carry no additional information given `A`. -/
def Determines (A B : Finset ι) : Prop := h (A ∪ B) = h A

/-- Set-function mutual information; for Shannon's set function this is the
ordinary mutual information of the two collections of observations. -/
def Mutual (A B : Finset ι) : ℝ := h A + h B - h (A ∪ B)

/-- Set-function conditional mutual information. -/
def CondMutual (A B C : Finset ι) : ℝ :=
  h (A ∪ C) + h (B ∪ C) - h C - h (A ∪ B ∪ C)

lemma nonneg (A : Finset ι) : 0 ≤ h A := by
  have := h.mono (Finset.empty_subset A)
  simpa only [h.empty] using this

lemma subadd (A B : Finset ι) : h (A ∪ B) ≤ h A + h B := by
  have := h.submod A B
  have := h.nonneg (A ∩ B)
  linarith

lemma determines_of_subset {A B : Finset ι} (hab : B ⊆ A) : h.Determines A B := by
  unfold Determines
  rw [Finset.union_eq_left.mpr hab]

lemma determines_self (A : Finset ι) : h.Determines A A :=
  h.determines_of_subset (Finset.Subset.refl _)

lemma determines_mono_left {A B D : Finset ι}
    (hab : h.Determines A B) (had : A ⊆ D) : h.Determines D B := by
  unfold Determines at *
  have hsub : A ⊆ (A ∪ B) ∩ D := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_left B hx, had hx⟩
  have hle := h.mono hsub
  have hupper := h.submod (A ∪ B) D
  have heq : (A ∪ B) ∪ D = D ∪ B := by
    ext x
    simp only [Finset.mem_union]
    constructor
    · rintro ((hx | hx) | hx)
      · exact Or.inl (had hx)
      · exact Or.inr hx
      · exact Or.inl hx
    · rintro (hx | hx)
      · exact Or.inr hx
      · exact Or.inl (Or.inr hx)
  rw [heq, hab] at hupper
  have hlower := h.mono (Finset.subset_union_left (s₁ := D) (s₂ := B))
  linarith

lemma determines_mono_right {A B C : Finset ι}
    (hab : h.Determines A B) (hcb : C ⊆ B) : h.Determines A C := by
  unfold Determines at *
  have hupper := h.mono (Finset.union_subset_union (Finset.Subset.refl A) hcb)
  have hlower := h.mono (Finset.subset_union_left (s₁ := A) (s₂ := C))
  linarith

lemma determines_union {A B C : Finset ι}
    (hab : h.Determines A B) (hac : h.Determines A C) : h.Determines A (B ∪ C) := by
  have hac' := h.determines_mono_left hac (Finset.subset_union_left (s₁ := A) (s₂ := B))
  unfold Determines at *
  rw [← Finset.union_assoc, hac', hab]

lemma determines_trans {A B C : Finset ι}
    (hab : h.Determines A B) (hbc : h.Determines B C) : h.Determines A C := by
  have hbc' := h.determines_mono_left hbc (Finset.subset_union_right (s₁ := A) (s₂ := B))
  have hfull : h.Determines A (B ∪ C) := by
    unfold Determines at *
    rw [← Finset.union_assoc, hbc', hab]
  exact h.determines_mono_right hfull (Finset.subset_union_right (s₁ := B) (s₂ := C))

lemma eq_of_mutual_determines {A B : Finset ι}
    (hab : h.Determines A B) (hba : h.Determines B A) : h A = h B := by
  unfold Determines at *
  rw [Finset.union_comm] at hba
  exact hab.symm.trans hba

lemma determines_le {A B : Finset ι} (hab : h.Determines A B) : h B ≤ h A := by
  have := h.mono (Finset.subset_union_right (s₁ := A) (s₂ := B))
  exact this.trans_eq hab

lemma functional_submod {A B C : Finset ι}
    (hac : h.Determines A C) (hbc : h.Determines B C) :
    h (A ∪ B) + h C ≤ h A + h B := by
  have hs := h.submod (A ∪ C) (B ∪ C)
  have hu := h.mono (Finset.union_subset_union
    (Finset.subset_union_left (s₁ := A) (s₂ := C))
    (Finset.subset_union_left (s₁ := B) (s₂ := C)))
  have hi := h.mono (Finset.subset_inter
    (Finset.subset_union_right (s₁ := A) (s₂ := C))
    (Finset.subset_union_right (s₁ := B) (s₂ := C)))
  change h (A ∪ C) = h A at hac
  change h (B ∪ C) = h B at hbc
  rw [hac, hbc] at hs
  linarith

lemma increment_antitone {A B C : Finset ι} (hab : A ⊆ B) :
    h (B ∪ C) - h B ≤ h (A ∪ C) - h A := by
  have hs := h.submod B (A ∪ C)
  have hi := h.mono (Finset.subset_inter hab (Finset.subset_union_left (s₁ := A) (s₂ := C)))
  have heq : B ∪ (A ∪ C) = B ∪ C := by
    rw [← Finset.union_assoc, Finset.union_eq_left.mpr hab]
  rw [heq] at hs
  linarith

lemma mutual_nonneg (A B : Finset ι) : 0 ≤ h.Mutual A B := by
  unfold Mutual
  linarith [h.subadd A B]

lemma condMutual_nonneg (A B C : Finset ι) : 0 ≤ h.CondMutual A B C := by
  have hs := h.submod (A ∪ C) (B ∪ C)
  have hi := h.mono (Finset.subset_inter
    (Finset.subset_union_right (s₁ := A) (s₂ := C))
    (Finset.subset_union_right (s₁ := B) (s₂ := C)))
  have heq : (A ∪ C) ∪ (B ∪ C) = A ∪ B ∪ C := by
    ext x
    simp only [Finset.mem_union]
    aesop
  rw [heq] at hs
  unfold CondMutual
  linarith

/-- Independence is preserved by taking functions of either observation. -/
lemma independent_functions {A B A' B' : Finset ι}
    (hind : h (A ∪ B) = h A + h B)
    (ha : h.Determines A A') (hb : h.Determines B B') :
    h (A' ∪ B') = h A' + h B' := by
  have left_step {P Q R : Finset ι}
      (ind : h (P ∪ Q) = h P + h Q) (dep : h.Determines Q R) :
      h (P ∪ R) = h P + h R := by
    have hs := h.functional_submod
      (h.determines_of_subset (Finset.subset_union_right (s₁ := P) (s₂ := R))) dep
    have hpq := h.mono (Finset.union_subset_union
      (Finset.subset_union_left (s₁ := P) (s₂ := R)) (Finset.Subset.refl Q))
    have hsub := h.subadd P R
    linarith
  have hab' := left_step hind hb
  have hb'a : h (B' ∪ A) = h B' + h A := by
    rw [Finset.union_comm, hab', add_comm]
  have := left_step hb'a ha
  rw [Finset.union_comm, add_comm] at this
  exact this

/-- Adding the same observations to two informationally equivalent collections
preserves their entropy equality. -/
lemma union_eq_of_mutual_determines {C D : Finset ι}
    (hcd : h.Determines C D) (hdc : h.Determines D C) (A : Finset ι) :
    h (A ∪ C) = h (A ∪ D) := by
  apply h.eq_of_mutual_determines
  · exact h.determines_union (h.determines_of_subset Finset.subset_union_left)
      (h.determines_mono_left hcd Finset.subset_union_right)
  · exact h.determines_union (h.determines_of_subset Finset.subset_union_left)
      (h.determines_mono_left hdc Finset.subset_union_right)

/-- Conditional mutual information is unchanged on replacing the conditioning
observations by an informationally equivalent collection. In the paper this
identifies conditioning on `(Mᵢ,Tᵢ,Ω)` with conditioning on `(Wᵢ,Ω)`. -/
lemma condMutual_congr_condition {C D : Finset ι}
    (hcd : h.Determines C D) (hdc : h.Determines D C) (A B : Finset ι) :
    h.CondMutual A B C = h.CondMutual A B D := by
  unfold CondMutual
  rw [h.union_eq_of_mutual_determines hcd hdc A,
    h.union_eq_of_mutual_determines hcd hdc B,
    h.union_eq_of_mutual_determines hcd hdc (A ∪ B),
    h.eq_of_mutual_determines hcd hdc]

/-- Conditioning a genuine entropy function on a fixed observation set
preserves all the entropy-function laws. -/
def condition (C : Finset ι) : EntropyFunction ι where
  value A := h (A ∪ C) - h C
  empty := by
    rw [Finset.empty_union, sub_self]
  mono := by
    intro A B hab
    exact sub_le_sub_right (h.mono (Finset.union_subset_union hab (Finset.Subset.refl C))) _
  submod := by
    intro A B
    have hs := h.submod (A ∪ C) (B ∪ C)
    have hu : (A ∪ C) ∪ (B ∪ C) = (A ∪ B) ∪ C := by
      ext x
      simp only [Finset.mem_union]
      aesop
    have hi : (A ∪ C) ∩ (B ∪ C) = (A ∩ B) ∪ C := by
      ext x
      simp only [Finset.mem_union, Finset.mem_inter]
      aesop
    rw [hu, hi] at hs
    linarith

end EntropyFunction
end UploadBroadcast
