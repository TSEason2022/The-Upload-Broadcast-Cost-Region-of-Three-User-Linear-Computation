import UploadBroadcast.ScalarAssembly
import UploadBroadcast.ScalarIncidence
import UploadBroadcast.AllocationNat

namespace UploadBroadcast
open ScalarIncidence
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- The actual transmitted list associated to a coordinated parameter assignment. -/
def assignmentTransmitted (U : Fin 3 → Submodule K F)
    {r x y z l : ℕ} {h : Fin 3 → ℕ}
    (a : (g : Groups r x y z l) → Space U g)
    (indiv : ∀ i, Fin (h i) → F) : ScalarTransmissionIndex r x y z l h → F :=
  scalarTransmitted (fun j => projection U 0 (.inl j) (a (.inl j)))
    (fun j => projection U 0 (.inr (.inl (.inl j))) (a (.inr (.inl (.inl j)))))
    (fun j => projection U 0 (.inr (.inl (.inr (.inl j)))) (a (.inr (.inl (.inr (.inl j))))))
    (fun j => projection U 0 (.inr (.inl (.inr (.inr j)))) (a (.inr (.inl (.inr (.inr j))))))
    (fun j => relationProjection U 0 (a (.inr (.inr j))))
    (fun j => relationProjection U 1 (a (.inr (.inr j)))) indiv

/-- All incident shared coefficients can be recovered from the explicit
transmission. The third aligned projection is the sum of the two sent ones. -/
theorem incident_projection_mem_transmitted (U : Fin 3 → Submodule K F)
    {r x y z l : ℕ} {h : Fin 3 → ℕ}
    (a : (g : Groups r x y z l) → Space U g)
    (indiv : ∀ i, Fin (h i) → F) (i : Fin 3) (j : Local r x y z l i) :
    projection U i (inclusion r x y z l i j) (a (inclusion r x y z l i j)) ∈
      Submodule.span K (Set.range (assignmentTransmitted U a indiv)) := by
  obtain ⟨hc,hx,hy,hz,ha₀,ha₁,hi⟩ := scalarTransmitted_mem (K := K)
    (fun j => projection U 0 (.inl j) (a (.inl j)))
    (fun j => projection U 0 (.inr (.inl (.inl j))) (a (.inr (.inl (.inl j)))))
    (fun j => projection U 0 (.inr (.inl (.inr (.inl j)))) (a (.inr (.inl (.inr (.inl j))))))
    (fun j => projection U 0 (.inr (.inl (.inr (.inr j)))) (a (.inr (.inl (.inr (.inr j))))))
    (fun j => relationProjection U 0 (a (.inr (.inr j))))
    (fun j => relationProjection U 1 (a (.inr (.inr j)))) indiv
  fin_cases i <;> rcases j with j | (j | j) | j
  · exact hc j
  · exact hz j
  · exact hy j
  · exact ha₀ j
  · exact hc j
  · exact hz j
  · exact hx j
  · exact ha₁ j
  · exact hc j
  · exact hy j
  · exact hx j
  · have he := (a (.inr (.inr j))).property.2.2.2
    change relationProjection U 2 (a (.inr (.inr j))) ∈ _
    have hp : relationProjection U 2 (a (.inr (.inr j))) =
        relationProjection U 0 (a (.inr (.inr j))) +
          relationProjection U 1 (a (.inr (.inr j))) := he.symm
    rw [hp]
    exact Submodule.add_mem _ (ha₀ j) (ha₁ j)

/-- Individual completion columns are transmitted directly. -/
theorem individual_mem_transmitted (U : Fin 3 → Submodule K F)
    {r x y z l : ℕ} {h : Fin 3 → ℕ}
    (a : (g : Groups r x y z l) → Space U g)
    (indiv : ∀ i, Fin (h i) → F) (i : Fin 3) (j : Fin (h i)) :
    indiv i j ∈ Submodule.span K (Set.range (assignmentTransmitted U a indiv)) := by
  exact Submodule.subset_span ⟨.inr (.inr (.inr ⟨i,j⟩)),rfl⟩

/-- Reconcile independently chosen blocks and build an actual scalar code.
The incidence, lifting, and transmitted-coefficient conditions are discharged
by the concrete common, pair, and aligned relation spaces. -/
theorem scalar_code_of_incidence_witnesses [Fintype K] [FiniteDimensional K F]
    (A U : Fin 3 → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    {r x y z l : ℕ} {h : Fin 3 → ℕ}
    (indiv : ∀ i, Fin (h i) → F)
    (selected : ∀ i, Local r x y z l i → F)
    (hi : ∀ i j, indiv i j ∈ U i)
    (hs : ∀ i j, selected i j ∈ allowed U i (inclusion r x y z l i j))
    (hind : ∀ i, LinearIndependent K (Sum.elim
      (Sum.elim (fun j => (Module.finBasis K (A i) j : F)) (indiv i)) (selected i)))
    (hcard : ∀ i, Module.finrank K (A i) + h i +
      Fintype.card (Local r x y z l i) = Module.finrank K (U i))
    (hq : 3 ≤ Fintype.card K) :
    Nonempty (ScalarBroadcastCode A U (r+x+y+z+2*l+h 0+h 1+h 2)) := by
  classical
  let H : Fin 3 → Type := fun i => Fin (Module.finrank K (A i)) ⊕ Fin (h i)
  let fixed : ∀ i, H i → F := fun i =>
    Sum.elim (fun j => (Module.finBasis K (A i) j : F)) (indiv i)
  obtain ⟨a,ha⟩ := coordinate_lifted_block_families
    (Space U : Groups r x y z l → Type _) H (Local r x y z l)
    (inclusion r x y z l) (inclusion_injective r x y z l) fixed
    (fun i j => projection U i (inclusion r x y z l i j)) selected hind
    (fun i j => projection_lift U i _ _ (hs i j)) (by simpa using hq)
  let columns := fun i => Sum.elim (fixed i)
    (fun j => projection U i (inclusion r x y z l i j) (a (inclusion r x y z l i j)))
  have hc : Nonempty (ScalarBroadcastCode A U
      (Fintype.card (ScalarTransmissionIndex r x y z l h))) := by
    apply scalarBroadcastCode_of_independent_columns A U columns
      (assignmentTransmitted U a indiv) ha
    · intro i j
      rcases j with (j|j)|j
      · exact hAU i (Module.finBasis K (A i) j).property
      · exact hi i j
      · exact local_projection_mem U i j _
    · intro i
      simpa only [H,Fintype.card_sum,Fintype.card_fin] using hcard i
    · intro i j
      rcases j with (j|j)|j
      · exact (show A i ≤ A i ⊔ Submodule.span K
          (Set.range (assignmentTransmitted U a indiv)) from le_sup_left)
          (Module.finBasis K (A i) j).property
      · exact (show Submodule.span K (Set.range (assignmentTransmitted U a indiv)) ≤
          A i ⊔ Submodule.span K (Set.range (assignmentTransmitted U a indiv)) from
          le_sup_right) (individual_mem_transmitted U a indiv i j)
      · exact (show Submodule.span K (Set.range (assignmentTransmitted U a indiv)) ≤
          A i ⊔ Submodule.span K (Set.range (assignmentTransmitted U a indiv)) from
          le_sup_right) (incident_projection_mem_transmitted U a indiv i j)
  simpa only [scalarTransmission_card] using hc

/-- Allocation totals are exactly the cardinalities needed for user bases. -/
theorem scalarAllocation_local_card [FiniteDimensional K F]
    (A U : Fin 3 → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (s : ScalarAllocation A U) (i : Fin 3) :
    Module.finrank K (A i) + s.h i +
      Fintype.card (Local s.r s.x s.y s.z s.al i) = Module.finrank K (U i) := by
  have hdim := Submodule.finrank_mono (hAU i)
  have h₀ := s.total0
  have h₁ := s.total1
  have h₂ := s.total2
  rw [Allocation.demandRank_eq_finrank_sub A U 0 (hAU 0)] at h₀
  rw [Allocation.demandRank_eq_finrank_sub A U 1 (hAU 1)] at h₁
  rw [Allocation.demandRank_eq_finrank_sub A U 2 (hAU 2)] at h₂
  fin_cases i
  · change Module.finrank K (A 0) ≤ Module.finrank K (U 0) at hdim
    change Module.finrank K (A 0) + s.h 0 + _ = Module.finrank K (U 0)
    simp only [Local,Fintype.card_sum,Fintype.card_fin]
    omega
  · change Module.finrank K (A 1) ≤ Module.finrank K (U 1) at hdim
    change Module.finrank K (A 1) + s.h 1 + _ = Module.finrank K (U 1)
    simp only [Local,Fintype.card_sum,Fintype.card_fin]
    omega
  · change Module.finrank K (A 2) ≤ Module.finrank K (U 2) at hdim
    change Module.finrank K (A 2) + s.h 2 + _ = Module.finrank K (U 2)
    simp only [Local,Fintype.card_sum,Fintype.card_fin]
    omega

/-- Every feasible integer allocation is implemented over the original field
when its cardinality is at least three. No code, basis, separate witness, or
upload-feasibility hypothesis is assumed. -/
theorem scalarBroadcastCode_of_allocation [Fintype K] [FiniteDimensional K F]
    (A U : Fin 3 → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (s : ScalarAllocation A U) (hq : 3 ≤ Fintype.card K) :
    Nonempty (ScalarBroadcastCode A U s.length) := by
  obtain ⟨indiv,selected,hi,hs,hind⟩ := separate_incidence_witnesses A U hAU s
  exact scalar_code_of_incidence_witnesses A U hAU indiv selected hi hs hind
    (scalarAllocation_local_card A U hAU s) hq

/-- Operational scalar achievability at the ceiling of the actual rank LP.
The existential witness includes actual linear encoders and linear decoders. -/
theorem scalar_lcbc_achievability [Finite K] [FiniteDimensional K F]
    (A U : Fin 3 → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (hq : 3 ≤ Nat.card K) :
    ∃ n : ℕ, (n : ℤ) = ⌈Allocation.actualNumericLP A U⌉ ∧
      Nonempty (ScalarBroadcastCode A U n) := by
  classical
  letI := Fintype.ofFinite K
  obtain ⟨s,_,hs⟩ := Allocation.actual_nat_lcbc_allocation A U
  exact ⟨s.length,hs,scalarBroadcastCode_of_allocation A U hAU s
    (by simpa only [Nat.card_eq_fintype_card] using hq)⟩

/-- The attained-alphabet cost of the constructed scalar code is bounded by
its nominal length, which equals the ceiling of the actual rank LP. -/
theorem scalar_lcbc_achievability_cost [Finite K] [FiniteDimensional K F]
    (A U : Fin 3 → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (hq : 3 ≤ Nat.card K) :
    ∃ (n : ℕ) (c : ScalarBroadcastCode A U n),
      (n : ℤ) = ⌈Allocation.actualNumericLP A U⌉ ∧
      Real.logb (Nat.card K) (Nat.card (Set.range c.encode)) ≤ n := by
  obtain ⟨n,hn,⟨c⟩⟩ := scalar_lcbc_achievability A U hAU hq
  exact ⟨n,c,hn,scalarBroadcastCode_cost_le c⟩

end UploadBroadcast
