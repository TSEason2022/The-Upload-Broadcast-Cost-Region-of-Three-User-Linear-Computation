import UploadBroadcast.FiniteRelayAssembly
import UploadBroadcast.OmniscienceProfile

namespace UploadBroadcast.OmniscienceRelayProfile
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Every feasible omniscience relay preserves all fifteen profile entries,
regardless of the chosen optimal encoder or coordinate presentation. -/
theorem entry_preserved (T : Task K V) (hU : ∀ i, T.U i = ⊤)
    (P : Submodule K V) (hg : T.LocallyGenerated P) (hf : T.RelayFeasible P)
    (r : Profile.Index) : Profile.entry (T.inducedRelay P hg) r = Profile.entry T r := by
  let S := T.inducedRelay P hg
  have hS (i : Three) : S.U i = ⊤ := by
    change (T.U i).comap P.subtype=⊤
    rw [hU,Submodule.comap_top]
  have hd (i : Three) : condRank (⊤ : Submodule K P) (S.A i) = condRank ⊤ (T.A i) := by
    have hm := Profile.condRank_map_injective P.subtype P.subtype_injective
      (⊤ : Submodule K P) ((T.A i).comap P.subtype)
    rw [Submodule.map_top,Submodule.range_subtype,Submodule.map_comap_subtype] at hm
    exact hm.symm.trans (by
      simpa only [inf_comm] using OmniscienceProfile.relay_deficits T hU P hf i)
  have ht : (Profile.totalDemand S : ℝ) = Profile.totalDemand T := by
    rw [OmniscienceProfile.totalDemand_eq_sum_rank S,OmniscienceProfile.totalDemand_eq_sum_rank T]
    simp only [hS,hU,hd]
  change Profile.entry S r = _
  cases r with
  | inl r => simp only [Profile.entry,Profile.firstEntry,hS,hU,inf_top_eq,sup_top_eq,ht,hd]
  | inr r => simp only [Profile.entry,Profile.secondEntry,hS,hU,inf_top_eq,sup_top_eq,ht,hd]

variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Extend a residual relay by an actual omniscience relay. Entrywise Ω
profile preservation and exact rank addition are proved, not assumed. -/
theorem product_profile (T : Task K V) (O : Task K W) (hOU : ∀ i, O.U i=⊤)
    (P : Submodule K V) (Q : Submodule K W)
    (hP : T.LocallyGenerated P) (hQ : O.LocallyGenerated Q)
    (hf : O.RelayFeasible Q) (r : Profile.Index) :
    Profile.entry ((Profile.directSum T O).inducedRelay (P.prod Q)
      (OptimalRelaySeparation.product_locally_generated T O P Q hP hQ)) r =
      Profile.entry (T.inducedRelay P hP) r + Profile.entry O r := by
  rw [FiniteRelayAssembly.product_inducedRelay_entry,entry_preserved O hOU Q hQ hf]

/-- Concrete Ω assembly with a minimum residual relay gives the full binary
separation condition as well as rank and profile control. -/
theorem assemble_binary [Finite K]
    (T : Task K V) (O : Task K W) (hOU : ∀ i, O.U i=⊤)
    (P : Submodule K V) (Q : Submodule K W)
    (hPl : T.LocallyGenerated P) (hPf : T.RelayFeasible P)
    (hQl : O.LocallyGenerated Q) (hQf : O.RelayFeasible Q)
    (hAB : Disjoint (T.A 0) (T.A 1)) (hAC : Disjoint (T.A 0) (T.A 2))
    (hBC : Disjoint (T.A 1) (T.A 2))
    (u v : ℕ) (hPd : finrank K P=u) (hQd : finrank K Q=v)
    (hPmin : (u : ℝ)=T.uploadOptimum)
    (hQmin : (v : ℝ)=Allocation.omniscienceValue
      (condRank ⊤ (O.A 0)) (condRank ⊤ (O.A 1)) (condRank ⊤ (O.A 2)))
    (D : ℝ) (hbudget : ∀ r, Profile.entry (T.inducedRelay P hPl) r+Profile.entry O r ≤ D) :
    ∃ S : Submodule K (V × W), ∃ hg : (Profile.directSum T O).LocallyGenerated S,
      (Profile.directSum T O).RelayFeasible S ∧ finrank K S=u+v ∧
      (∀ r, Profile.entry ((Profile.directSum T O).inducedRelay S hg) r ≤ D) ∧
      ∃ p : Equiv.Perm Three,
        (((Profile.directSum T O).A (p 0)).comap S.subtype) ⊓
          (((Profile.directSum T O).A (p 1)).comap S.subtype ⊔
            ((Profile.directSum T O).A (p 2)).comap S.subtype) = ⊥ := by
  refine ⟨P.prod Q,OptimalRelaySeparation.product_locally_generated T O P Q hPl hQl,
    OptimalRelaySeparation.product_relay_feasible T O P Q hPf hQf,?_,?_,?_⟩
  · rw [Profile.finrank_submodule_prod,hPd,hQd]
  · intro r
    rw [product_profile T O hOU P Q hPl hQl hQf]
    exact hbudget r
  · obtain ⟨p,_,hp⟩ := OptimalRelaySeparation.binary_relay_separation T O P Q hPl hPf
      hAB hAC hBC (by simpa only [hPd] using hPmin) hOU hQl hQf
      (by simpa only [hQd] using hQmin)
    exact ⟨p,hp⟩

end UploadBroadcast.OmniscienceRelayProfile
