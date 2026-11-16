import UploadBroadcast.PairSelection
import UploadBroadcast.AllocationRanks

namespace UploadBroadcast
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Conditional rank as the dimension lost on intersection with side information. -/
theorem condRank_eq_finrank_sub_inf (P A : Submodule K F) :
    condRank P A = Module.finrank K P - Module.finrank K ↥(P ⊓ A) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq P A
  have hle := Submodule.finrank_mono (show A ≤ P ⊔ A from le_sup_right)
  unfold condRank
  rw [sup_comm A P]
  omega

/-- An actual common block of maximal conditional rank under separated side
information. This holds over every field, including the binary field. -/
theorem exists_separated_common_block (A U : Fin 3 → Submodule K F)
    (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥) :
    ∃ C : Submodule K F, C ≤ U 0 ⊓ U 1 ⊓ U 2 ∧
      Module.finrank K C = Allocation.commonRank A U ∧ ∀ i, Disjoint (A i) C := by
  let T := U 0 ⊓ U 1 ⊓ U 2
  let S : Fin 3 → Submodule K T := fun i => (A i).comap T.subtype
  have hs : S 0 ⊓ (S 1 ⊔ S 2) = ⊥ := by
    apply le_antisymm _ bot_le
    intro t ht
    obtain ⟨b,hb,c,hc,hbc⟩ := Submodule.mem_sup.mp ht.2
    have hm : (t:F) ∈ A 0 ⊓ (A 1 ⊔ A 2) := by
      refine ⟨ht.1,Submodule.mem_sup.mpr ⟨b,hb,c,hc,?_⟩⟩
      exact congrArg Subtype.val hbc
    rw [hsep] at hm
    exact Subtype.ext hm
  obtain ⟨D,hD,hD0,hD1,hD2⟩ := maximum_disjoint_subspace (S 0) (S 1) (S 2) hs
  have hd (i : Fin 3) : Module.finrank K (S i) = Module.finrank K ↥(T ⊓ A i) := by
    have he := (Submodule.comapSubtypeEquivOfLe (inf_le_left : T ⊓ A i ≤ T)).finrank_eq
    have hcomap : (T ⊓ A i).comap T.subtype = S i := by
      ext t
      change ((t:F) ∈ T ∧ (t:F) ∈ A i) ↔ (t:F) ∈ A i
      exact and_iff_right t.property
    rwa [hcomap] at he
  refine ⟨D.map T.subtype,?_,?_,?_⟩
  · rintro _ ⟨t,_,rfl⟩
    exact t.property
  · rw [Submodule.finrank_map_subtype_eq,hD,hd 0,hd 1,hd 2]
    unfold Allocation.commonRank
    rw [condRank_eq_finrank_sub_inf,condRank_eq_finrank_sub_inf,condRank_eq_finrank_sub_inf]
    change Module.finrank K T - max (Module.finrank K ↥(T ⊓ A 0))
      (max (Module.finrank K ↥(T ⊓ A 1)) (Module.finrank K ↥(T ⊓ A 2))) = _
    dsimp [T] at *
    omega
  · intro i
    have hDi : D ⊓ S i = ⊥ := by fin_cases i <;> assumption
    rw [Submodule.disjoint_def]
    rintro t ht ⟨v,hv,rfl⟩
    have hm : v ∈ D ⊓ S i := ⟨hv,ht⟩
    rw [hDi] at hm
    exact congrArg Subtype.val (show v = 0 from hm)

end UploadBroadcast
