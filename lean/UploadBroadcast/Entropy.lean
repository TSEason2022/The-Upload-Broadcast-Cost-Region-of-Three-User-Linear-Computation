import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith

/-!
# Algebraic cores of the nonlinear entropy converse

This file checks the numerical implication at the end of the paper's
common-function entropy bound and omniscience lift. It deliberately does **not**
identify arbitrary real numbers with entropies. In particular, the finite
probability-space facts supplying the hypotheses below have not been formalized
here. These theorems are not a verification of the full entropy lemmas.
-/

namespace UploadBroadcast.Entropy

/-- Functional submodularity for any monotone submodular real-valued set
function. The hypothesis that `C` is a common function is expressed by its
adding no value to either `A` or `B`. This is a theorem about set functions;
instantiating it with Shannon entropy still requires a separate construction
and proof that Shannon entropy is monotone and submodular. -/
theorem functionalSubmodularity {α : Type*} (H : Set α → ℝ)
    (monotonicity : Monotone H)
    (submodularity : ∀ A B, H (A ∪ B) + H (A ∩ B) ≤ H A + H B)
    (A B C : Set α)
    (commonA : H (A ∪ C) = H A)
    (commonB : H (B ∪ C) = H B) :
    H (A ∪ B) + H C ≤ H A + H B := by
  have hunion : A ∪ B ⊆ (A ∪ C) ∪ (B ∪ C) := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr (Or.inl hx)
  have hinter : C ⊆ (A ∪ C) ∩ (B ∪ C) := by
    intro x hx
    exact ⟨Or.inr hx, Or.inr hx⟩
  have hu := monotonicity hunion
  have hi := monotonicity hinter
  have hs := submodularity (A ∪ C) (B ∪ C)
  rw [commonA, commonB] at hs
  linarith

/-- Substitution in the common-function bound, after the functional
submodularity bridge and the two independence expansions have been established.
The variables `h`, `aᵢ`, `mᵢ`, `jᵢ`, `bᵢ` stand for their corresponding real-valued
entropy expressions in the paper. No entropy identities are axioms. -/
theorem commonFunction_scalar
    (h a₁ a₂ a₃ m₁ m₂ m₃ j₁ j₂ b₁ b₂ : ℝ)
    (bridge : 2 * h - a₃ + m₃ ≤ b₁ + b₂)
    (expand₁ : b₁ = a₁ + m₂ + m₃ - j₁)
    (expand₂ : b₂ = a₂ + m₁ + m₃ - j₂) :
    2 * h - (a₁ + a₂ + a₃) + j₁ + j₂ ≤ m₁ + m₂ + m₃ := by
  linarith

/-- The bridge inequality follows from functional submodularity, joint
recovery and the upper bound on a conditional entropy, once those facts have
been proved in a concrete probabilistic model. -/
theorem commonFunction_bridge_scalar
    (h a₃ m₃ b₁ b₂ common tail : ℝ)
    (submodularity : h + common ≤ b₁ + b₂)
    (recovery : h ≤ common + tail)
    (conditioning : tail ≤ a₃ - m₃) :
    2 * h - a₃ + m₃ ≤ b₁ + b₂ := by
  linarith

/-- The purely numerical omniscience lift. `Δ` is the excess conditional upload
entropy above the residual lower bound, `i₁,i₂,i₃` the nonnegative individual
mutual informations, `j₁,j₂,j₃` the nonnegative retained conditional mutual
informations, and `d₁,d₂,d₃` the omniscience deficits. The interaction bounds
`deficit₁`--`deficit₃` and the pair bounds are hypotheses, not claims that the
probabilistic part of the paper has already been verified. -/
theorem omniscience_scalar
    (Γ Δ i₁ i₂ i₃ j₁ j₂ j₃ d₁ d₂ d₃ total : ℝ)
    (hi₁ : 0 ≤ i₁) (hi₂ : 0 ≤ i₂) (hi₃ : 0 ≤ i₃)
    (hj₁ : 0 ≤ j₁) (hj₂ : 0 ≤ j₂) (_hj₃ : 0 ≤ j₃)
    (pair₁₂ : j₁ + j₂ ≤ Δ)
    (pair₁₃ : j₁ + j₃ ≤ Δ)
    (_pair₂₃ : j₂ + j₃ ≤ Δ)
    (deficit₁ : d₁ ≤ i₂ + i₃ + j₁)
    (deficit₂ : d₂ ≤ i₁ + i₃ + j₂)
    (deficit₃ : d₃ ≤ i₁ + i₂ + j₃)
    (decomposition : total = Γ + Δ + i₁ + i₂ + i₃) :
    Γ + max (max d₁ (max d₂ d₃)) ((d₁ + d₂ + d₃) / 2) ≤ total := by
  have h₁ : d₁ ≤ Δ + i₁ + i₂ + i₃ := by linarith
  have h₂ : d₂ ≤ Δ + i₁ + i₂ + i₃ := by linarith
  have h₃ : d₃ ≤ Δ + i₁ + i₂ + i₃ := by linarith
  have hsum : j₁ + j₂ + j₃ ≤ 2 * Δ := by linarith
  have havg : (d₁ + d₂ + d₃) / 2 ≤ Δ + i₁ + i₂ + i₃ := by linarith
  have hmax : max (max d₁ (max d₂ d₃)) ((d₁ + d₂ + d₃) / 2) ≤
      Δ + i₁ + i₂ + i₃ :=
    max_le (max_le h₁ (max_le h₂ h₃)) havg
  linarith

/-- Chain rule cancellation in the omniscience interaction identity, with
nonnegative conditional mutual information discarded. -/
theorem interaction_scalar
    (d single₁ single₂ individual₁ individual₂ retained redundant : ℝ)
    (identity : d = single₁ + single₂ + retained - redundant)
    (bound₁ : single₁ ≤ individual₁)
    (bound₂ : single₂ ≤ individual₂)
    (nonnegative : 0 ≤ redundant) :
    d ≤ individual₁ + individual₂ + retained := by
  linarith

end UploadBroadcast.Entropy
