import UploadBroadcast.OmniscienceTaskCode
import UploadBroadcast.RelayLinearComposition
import UploadBroadcast.LinearCodeSum

namespace UploadBroadcast.UploadAttainment
open Module
variable {K F V X₁ X₂ X₃ : Type*} [Field K] [Finite K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup X₁] [Module K X₁] [FiniteDimensional K X₁]
  [AddCommGroup X₂] [Module K X₂] [FiniteDimensional K X₂]
  [AddCommGroup X₃] [Module K X₃] [FiniteDimensional K X₃]

local notation "O" => OmniscienceOperational.task (K := K) (V := V)
  (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)
local notation "uO" => Omniscience.optimum (K := K) (V := V)
  (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)

/-- Genuine length-two original-field uploads for an omniscience summand and
any feasible locally generated residual relay. All coordinate lengths are
accounted for, before any optimality converse is applied. -/
theorem two_instance (T : Task K F) (P : Submodule K F)
    (hlocal : T.LocallyGenerated P) (hfeas : T.RelayFeasible P) :
    ∃ (r : Three → ℕ) (s : ℕ) (c : (Profile.directSum O T).LinearCode 2 r s),
      ((∑ i, r i : ℕ) : ℝ) / 2 = uO + finrank K P ∧
      c.toCode.uploadCost ≤ uO + finrank K P := by
  obtain ⟨a,cO,hO,_,_⟩ := OmniscienceOperational.exists_two_instance_optimal
    (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)
  obtain ⟨b,cR,hR,_,_⟩ := RelayLinearComposition.full_relay_linear_code T P hlocal hfeas
  let c := cO.directSum cR.repeatScalar
  have hnom : (∑ i : Three, ((a i+(b i+b i) : ℕ) : ℝ)) / 2 = uO + finrank K P := by
    simp only [Nat.cast_add,Finset.sum_add_distrib]
    have hR' : (∑ i, (b i : ℝ)) = finrank K P := by exact_mod_cast hR
    have hO' : (∑ i, (a i : ℝ)) / 2 = uO := by exact_mod_cast hO
    rw [hR']
    linarith
  refine ⟨_,_,c,?_,?_⟩
  · simpa only [Nat.cast_sum] using hnom
  · exact (cO.directSum_cost_bounds cR.repeatScalar).1.trans_eq (by simpa using hnom)

/-- Integral omniscience cost needs only scalar uploads. -/
theorem scalar (T : Task K F) (P : Submodule K F)
    (hlocal : T.LocallyGenerated P) (hfeas : T.RelayFeasible P)
    (n : ℕ) (hn : (n : ℝ) = uO) :
    ∃ (r : Three → ℕ) (s : ℕ) (c : (Profile.directSum O T).LinearCode 1 r s),
      ((∑ i, r i : ℕ) : ℝ) = uO + finrank K P ∧
      c.toCode.uploadCost ≤ uO + finrank K P := by
  obtain ⟨a,cO,hO,_,_⟩ := OmniscienceOperational.exists_scalar_optimal
    (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) n hn
  obtain ⟨b,cR,hR,_,_⟩ := RelayLinearComposition.full_relay_linear_code T P hlocal hfeas
  let c := cO.directSum cR
  have hnom : (∑ i : Three, ((a i+b i : ℕ) : ℝ)) = uO + finrank K P := by
    rw [← Nat.cast_sum,Finset.sum_add_distrib,hO,hR,Nat.cast_add,hn]
  refine ⟨_,_,c,?_,?_⟩
  · simpa only [Nat.cast_sum] using hnom
  · have h := (cO.directSum_cost_bounds cR).1
    simpa only [Nat.cast_one,div_one,hnom] using h

end UploadBroadcast.UploadAttainment
