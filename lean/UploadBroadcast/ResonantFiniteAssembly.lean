import UploadBroadcast.GlobalMenuAssembly
import UploadBroadcast.ResonantProfile

namespace UploadBroadcast.ResonantFiniteAssembly
open Module FiniteRelayAssembly GlobalMenuAssembly
open scoped BigOperators
variable {K : Type*} [Field K]

def increment (k : Fin 3) : Profile.Index → ℝ
  | .inl r => ResonantRelay.increment k r
  | .inr _ => 0

def weights (v : Fin 3 → ℤ) : Fin 3 → ℤ := ![v 2,v 1,v 0]

theorem weighted_increment (v : Fin 3 → ℤ) (r : Profile.Index) :
    (∑ k, (weights v k : ℝ)*increment k r) =
      firstIncrement (BinaryAugmentedAllocation.resonantIncrement v) r := by
  cases r with
  | inl r =>
      fin_cases r <;> norm_num [increment,ResonantRelay.increment,weights,firstIncrement,
        BinaryAugmentedAllocation.resonantIncrement,Fin.sum_univ_succ]
  | inr r => simp [increment,firstIncrement]

theorem jordan_menu_profile (n : ℕ) (k : Fin 3) (r : Profile.Index) :
    Profile.entry (ResonantRelay.jordanInducedTask K n k) r ≤
      Profile.entry (ResonantRelay.jordanTask K n) r + increment k r := by
  cases r with
  | inl r =>
    exact (ResonantRelay.jordan_induced_firstProfile K n k r).trans
      (congrArg (fun a : ℝ => a+ResonantRelay.increment k r)
        (ResonantRelay.jordan_full_firstProfile K n r).symm) |>.le
  | inr r =>
    obtain ⟨i,l⟩ := r
    have h₁ := ResonantRelay.jordan_induced_secondProfile K n k i l
    have h₂ := ResonantRelay.jordan_full_secondProfile K n i l
    change _ ≤ _+0
    linarith only [h₁,h₂]

theorem jordan_realizes (n : ℕ) :
    RealizesMenu (ResonantRelay.jordanTask K n) (3*(n+1)+1) increment := by
  intro k
  obtain ⟨hg,hf,hd⟩ := ResonantRelay.jordan_menu_construction K n k
  refine ⟨ResonantRelay.jordanRelay K n k,hg,hf,hd,?_⟩
  intro r
  rw [Task.inducedRelay_entry]
  exact jordan_menu_profile n k r

variable {R : Type*} [Fintype R]

abbrev task (n : R → ℕ) := FiniteRelayAssembly.task (fun t => ResonantRelay.jordanTask K (n t))
abbrev Ambient (n : R → ℕ) := ∀ t, ResonantEndomorphisms.Ambient K (JordanResonance.V K (n t))

/-- Resonant integer weights select actual original-field Jordan relays for
every component copy, with exact total relay rank. -/
theorem exists_of_weights (n : R → ℕ) (v : Fin 3 → ℤ)
    (hv : ∀ k, 0 ≤ v k) (hvs : ∑ k, v k = Fintype.card R) :
    ∃ P : Submodule K (Ambient (K := K) n), ∃ hg : (task (K := K) n).LocallyGenerated P,
      (task (K := K) n).RelayFeasible P ∧ finrank K P = ∑ t, (3*(n t+1)+1) ∧
      ∀ r, Profile.entry ((task (K := K) n).inducedRelay P hg) r ≤
        Profile.entry (task (K := K) n) r+
          firstIncrement (BinaryAugmentedAllocation.resonantIncrement v) r := by
  have hw : ∀ k, 0 ≤ weights v k := by
    intro k; fin_cases k <;> exact hv _
  have hs : ∑ k, weights v k = (Fintype.card R : ℤ) := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hvs
    change v 0+(v 1+v 2) = _ at hvs
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change v 2+(v 1+v 0) = _
    linarith only [hvs]
  apply assemble_int_weights (fun t => ResonantRelay.jordanTask K (n t))
    (fun t => 3*(n t+1)+1) increment (fun t => jordan_realizes (n t)) (weights v) hw hs
  intro r
  rw [weighted_increment]

end UploadBroadcast.ResonantFiniteAssembly
