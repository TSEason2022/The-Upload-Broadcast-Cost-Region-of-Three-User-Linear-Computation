import UploadBroadcast.ScalarAchievability
import UploadBroadcast.BinaryIncidence
import UploadBroadcast.BinaryAssembly

namespace UploadBroadcast
open BinaryIncidence
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Adjoin the fixed common block to a coordinated pair/aligned assignment. -/
def adjoinCommonAssignment (U : Fin 3 → Submodule K F) {r x y z l : ℕ}
    (c : Fin r → F) (hc : ∀ j, c j ∈ U 0 ⊓ U 1 ⊓ U 2)
    (a : (g : Remaining x y z l) → Space U g) :
    (g : ScalarIncidence.Groups r x y z l) → ScalarIncidence.Space U g
  | Sum.inl j => ⟨c j,hc j⟩
  | Sum.inr (Sum.inl (Sum.inl j)) => a (Sum.inl (Sum.inl j))
  | Sum.inr (Sum.inl (Sum.inr (Sum.inl j))) => a (Sum.inl (Sum.inr (Sum.inl j)))
  | Sum.inr (Sum.inl (Sum.inr (Sum.inr j))) => a (Sum.inl (Sum.inr (Sum.inr j)))
  | Sum.inr (Sum.inr j) => a (Sum.inr j)

/-- Every incident remaining column is covered by the existing explicit
transmission list with its fixed common block adjoined. -/
theorem remaining_projection_mem_transmitted (U : Fin 3 → Submodule K F)
    {r x y z l : ℕ} {h : Fin 3 → ℕ}
    (c : Fin r → F) (hc : ∀ j, c j ∈ U 0 ⊓ U 1 ⊓ U 2)
    (a : (g : Remaining x y z l) → Space U g)
    (indiv : ∀ i, Fin (h i) → F) (i : Fin 3) (j : Local x y z l i) :
    projection U i (inclusion x y z l i j) (a (inclusion x y z l i j)) ∈
      Submodule.span K (Set.range (assignmentTransmitted U (adjoinCommonAssignment U c hc a) indiv)) := by
  fin_cases i <;> rcases j with (j | j) | j
  all_goals first
    | exact incident_projection_mem_transmitted U (adjoinCommonAssignment U c hc a) indiv 0
        (Sum.inr (Sum.inl (Sum.inl j)))
    | exact incident_projection_mem_transmitted U (adjoinCommonAssignment U c hc a) indiv 0
        (Sum.inr (Sum.inl (Sum.inr j)))
    | exact incident_projection_mem_transmitted U (adjoinCommonAssignment U c hc a) indiv 0
        (Sum.inr (Sum.inr j))
    | exact incident_projection_mem_transmitted U (adjoinCommonAssignment U c hc a) indiv 1
        (Sum.inr (Sum.inl (Sum.inl j)))
    | exact incident_projection_mem_transmitted U (adjoinCommonAssignment U c hc a) indiv 1
        (Sum.inr (Sum.inl (Sum.inr j)))
    | exact incident_projection_mem_transmitted U (adjoinCommonAssignment U c hc a) indiv 1
        (Sum.inr (Sum.inr j))
    | exact incident_projection_mem_transmitted U (adjoinCommonAssignment U c hc a) indiv 2
        (Sum.inr (Sum.inl (Sum.inl j)))
    | exact incident_projection_mem_transmitted U (adjoinCommonAssignment U c hc a) indiv 2
        (Sum.inr (Sum.inl (Sum.inr j)))
    | exact incident_projection_mem_transmitted U (adjoinCommonAssignment U c hc a) indiv 2
        (Sum.inr (Sum.inr j))

/-- Once the pair/aligned assignments are coordinated, the fixed-common
construction gives actual linear encoders and decoders of the allocation length. -/
theorem scalar_code_of_fixed_common_assignment [FiniteDimensional K F]
    (A U : Fin 3 → Submodule K F) (hAU : ∀ i, A i ≤ U i) (s : ScalarAllocation A U)
    (c : Fin s.r → F) (hc : ∀ j, c j ∈ U 0 ⊓ U 1 ⊓ U 2)
    (indiv : ∀ i, Fin (s.h i) → F) (hi : ∀ i j, indiv i j ∈ U i)
    (a : (g : Remaining s.x s.y s.z s.al) → Space U g)
    (hind : ∀ i, LinearIndependent K (Sum.elim
      (Sum.elim (Sum.elim (fun j => (Module.finBasis K (A i) j : F)) c) (indiv i))
      (fun j => projection U i (inclusion s.x s.y s.z s.al i j)
        (a (inclusion s.x s.y s.z s.al i j))))) :
    Nonempty (ScalarBroadcastCode A U s.length) := by
  let full := adjoinCommonAssignment U c hc a
  let columns := fun i => Sum.elim
    (Sum.elim (Sum.elim (fun j => (Module.finBasis K (A i) j : F)) c) (indiv i))
    (fun j => projection U i (inclusion s.x s.y s.z s.al i j)
      (a (inclusion s.x s.y s.z s.al i j)))
  have hc' : Nonempty (ScalarBroadcastCode A U
      (Fintype.card (ScalarTransmissionIndex s.r s.x s.y s.z s.al s.h))) := by
    apply scalarBroadcastCode_of_independent_columns A U columns
      (assignmentTransmitted U full indiv) hind
    · intro i j
      rcases j with ((j|j)|j)|j
      · exact hAU i (Module.finBasis K (A i) j).property
      · exact Allocation.common_le_signal U i (hc j)
      · exact hi i j
      · exact local_projection_mem U i j _
    · intro i
      have hh := scalarAllocation_local_card A U hAU s i
      fin_cases i <;>
        simp only [ScalarIncidence.Local,Local,Fintype.card_sum,Fintype.card_fin] at hh ⊢ <;>
        omega
    · intro i j
      rcases j with ((j|j)|j)|j
      · exact (show A i ≤ A i ⊔ Submodule.span K
          (Set.range (assignmentTransmitted U full indiv)) from le_sup_left)
          (Module.finBasis K (A i) j).property
      · apply (show Submodule.span K (Set.range (assignmentTransmitted U full indiv)) ≤
          A i ⊔ Submodule.span K (Set.range (assignmentTransmitted U full indiv)) from le_sup_right)
        exact Submodule.subset_span ⟨Sum.inl j,rfl⟩
      · exact (show Submodule.span K (Set.range (assignmentTransmitted U full indiv)) ≤
          A i ⊔ Submodule.span K (Set.range (assignmentTransmitted U full indiv)) from le_sup_right)
          (individual_mem_transmitted U full indiv i j)
      · exact (show Submodule.span K (Set.range (assignmentTransmitted U full indiv)) ≤
          A i ⊔ Submodule.span K (Set.range (assignmentTransmitted U full indiv)) from le_sup_right)
          (remaining_projection_mem_transmitted U c hc a indiv i j)
  simpa only [scalarTransmission_card,ScalarAllocation.length] using hc'

section Binary
variable {B : Type*} [AddCommGroup B] [Module (ZMod 2) B] [FiniteDimensional (ZMod 2) B]

/-- Every maximal-common allocation has an actual binary scalar realization
when side information spans the source and one side is separated from the other two. -/
theorem binaryScalarBroadcastCode_of_allocation
    (A U : Fin 3 → Submodule (ZMod 2) B) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥)
    (s : ScalarAllocation A U) (hr : s.r = Allocation.commonRank A U) :
    Nonempty (ScalarBroadcastCode A U s.length) := by
  obtain ⟨c,indiv,selected,hc,hi,hs,hind⟩ :=
    BinaryIncidence.separate_incidence_witnesses A U hAU hsep s hr
  obtain ⟨a,ha⟩ := binary_incidence_coordination A U hAU hspan c indiv selected hs hind
  exact scalar_code_of_fixed_common_assignment A U hAU s c hc indiv hi a ha

/-- Scalar zero-error achievability over F₂ at the ceiling of the actual rank
LP, with genuine linear encoders and decoders and no assumed coding theorem. -/
theorem binary_scalar_lcbc_achievability
    (A U : Fin 3 → Submodule (ZMod 2) B) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥) :
    ∃ n : ℕ, (n : ℤ) = ⌈Allocation.actualNumericLP A U⌉ ∧
      Nonempty (ScalarBroadcastCode A U n) := by
  obtain ⟨s,hr,hs⟩ := Allocation.actual_nat_lcbc_allocation A U
  exact ⟨s.length,hs,binaryScalarBroadcastCode_of_allocation A U hAU hspan hsep s hr⟩

/-- The constructed binary code's attained-alphabet cost is bounded by its
verified scalar transmission length. -/
theorem binary_scalar_lcbc_achievability_cost
    (A U : Fin 3 → Submodule (ZMod 2) B) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥) :
    ∃ (n : ℕ) (c : ScalarBroadcastCode A U n),
      (n : ℤ) = ⌈Allocation.actualNumericLP A U⌉ ∧
      Real.logb (Nat.card (ZMod 2)) (Nat.card (Set.range c.encode)) ≤ n := by
  obtain ⟨n,hn,⟨c⟩⟩ := binary_scalar_lcbc_achievability A U hAU hspan hsep
  exact ⟨n,c,hn,scalarBroadcastCode_cost_le c⟩

end Binary
end UploadBroadcast
