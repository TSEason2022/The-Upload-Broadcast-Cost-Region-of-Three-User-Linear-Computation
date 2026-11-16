import UploadBroadcast.OmniscienceRelayProfile
import UploadBroadcast.LinearUploadRelay
import UploadBroadcast.OmniscienceTaskCode

namespace UploadBroadcast.OmniscienceRelayConstruction
open Module
variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Local generation and omniscience feasibility alone give the sharp
numerical lower bound on an actual coefficient relay's rank. -/
theorem value_le_rank (T : Task K W) (hU : ∀ i, T.U i=⊤)
    (P : Submodule K W) (hg : T.LocallyGenerated P) (hf : T.RelayFeasible P) :
    Allocation.omniscienceValue (condRank ⊤ (T.A 0)) (condRank ⊤ (T.A 1))
      (condRank ⊤ (T.A 2)) ≤ (finrank K P : ℝ) := by
  let A : Three → Submodule K P := fun i => (T.A i).comap P.subtype
  have h (i : Three) : finrank K (A i)+condRank ⊤ (T.A i)=finrank K P :=
    OptimalRelaySeparation.omniscience_induced_rank T hU P hf i
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  have hs := T.induced_sides_span P hg
  change (⨆ i, A i) = ⊤ at hs
  rw [Profile.three_iSup] at hs
  have hab := Submodule.finrank_add_le_finrank_add_finrank (A 0) (A 1)
  have hc := Submodule.finrank_add_le_finrank_add_finrank (A 0 ⊔ A 1) (A 2)
  rw [hs,finrank_top] at hc
  have hd₀ : (condRank ⊤ (T.A 0) : ℝ) ≤ finrank K P := by exact_mod_cast (by omega : condRank ⊤ (T.A 0) ≤ finrank K P)
  have hd₁ : (condRank ⊤ (T.A 1) : ℝ) ≤ finrank K P := by exact_mod_cast (by omega : condRank ⊤ (T.A 1) ≤ finrank K P)
  have hd₂ : (condRank ⊤ (T.A 2) : ℝ) ≤ finrank K P := by exact_mod_cast (by omega : condRank ⊤ (T.A 2) ≤ finrank K P)
  have hd : (condRank ⊤ (T.A 0) : ℝ)+condRank ⊤ (T.A 1)+condRank ⊤ (T.A 2) ≤ 2*finrank K P := by
    exact_mod_cast (by omega : condRank ⊤ (T.A 0)+condRank ⊤ (T.A 1)+condRank ⊤ (T.A 2) ≤ 2*finrank K P)
  unfold Allocation.omniscienceValue
  exact max_le (max_le hd₀ hd₁) (max_le hd₂ (by linarith only [hd]))

section Canonical
variable {V X₁ X₂ X₃ : Type*} [Finite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup X₁] [Module K X₁] [FiniteDimensional K X₁]
  [AddCommGroup X₂] [Module K X₂] [FiniteDimensional K X₂]
  [AddCommGroup X₃] [Module K X₃] [FiniteDimensional K X₃]

/-- The scalar optimal Ω code yields an actual original-field coefficient
relay. Its rank is forced to equal the numerical optimum by geometry, and
all fifteen induced entries and binary separation are established. -/
theorem exists_scalar (n : ℕ)
    (hn : (n : ℝ)=Omniscience.optimum (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)) :
    let O := OmniscienceOperational.task (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)
    ∃ P : Submodule K (OmniscienceOperational.Space V X₁ X₂ X₃), ∃ hg : O.LocallyGenerated P,
      O.RelayFeasible P ∧ finrank K P=n ∧
      (∀ r, Profile.entry (O.inducedRelay P hg) r = Profile.entry O r) ∧
      ∃ p : Equiv.Perm Three,
        (O.A (p 0)).comap P.subtype ⊓
          ((O.A (p 1)).comap P.subtype ⊔ (O.A (p 2)).comap P.subtype) = ⊥ := by
  let O := OmniscienceOperational.task (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)
  have hU : ∀ i, O.U i=⊤ := fun _ => rfl
  obtain ⟨r,c,_,hc,_⟩ := OmniscienceOperational.exists_scalar_optimal (K := K)
    (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) n hn
  have hval : (n : ℝ)=Allocation.omniscienceValue
      (condRank ⊤ (O.A 0)) (condRank ⊤ (O.A 1)) (condRank ⊤ (O.A 2)) :=
    hn.trans (OmniscienceOperational.optimum_eq_deficits (K := K)
      (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃))
  have hd : (finrank K c.uploadRelay : ℝ)=n := by
    apply le_antisymm
    · exact c.finrank_uploadRelay_le_uploadCost.trans_eq (hc.trans hn.symm)
    · exact hval.trans_le (value_le_rank O hU c.uploadRelay
        c.uploadRelay_locallyGenerated c.uploadRelay_feasible)
  refine ⟨c.uploadRelay,c.uploadRelay_locallyGenerated,c.uploadRelay_feasible,?_,?_,?_⟩
  · exact_mod_cast hd
  · intro r
    exact OmniscienceRelayProfile.entry_preserved O hU c.uploadRelay
      c.uploadRelay_locallyGenerated c.uploadRelay_feasible r
  · exact OptimalRelaySeparation.omniscience_minimum_separation O hU c.uploadRelay
      c.uploadRelay_locallyGenerated c.uploadRelay_feasible (hd.trans hval)

end Canonical
end UploadBroadcast.OmniscienceRelayConstruction
