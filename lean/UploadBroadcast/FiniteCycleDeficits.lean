import UploadBroadcast.EdgeDeficits
import UploadBroadcast.ResonantFiniteAssembly
import UploadBroadcast.PositiveExcessNoEdges
import UploadBroadcast.OrientationRepairAllocation

namespace UploadBroadcast.FiniteCycleDeficits
open Module EdgeDeficits EdgeExtraction
open scoped BigOperators
variable {K I : Type*} {F : I → Type*} [Field K] [Fintype I]
  [∀ t, AddCommGroup (F t)] [∀ t, Module K (F t)] [∀ t, FiniteDimensional K (F t)]

theorem finite_product_price (T : (t : I) → Task K (F t)) (p : Equiv.Perm Three) :
    price (FiniteRelayAssembly.task T) p=∑ t, price (T t) p := by
  simp only [price,FiniteRelayAssembly.firstEntry_task,FiniteRelayAssembly.secondEntry_task,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]

variable {R V : Type*} [Fintype R] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem resonant_price (n : R → ℕ) (p : Equiv.Perm Three) :
    price (ResonantFiniteAssembly.task (K := K) n) p = -∑ t, ((n t : ℝ)+1) := by
  rw [finite_product_price]
  simp only [jordan_price,Finset.sum_neg_distrib]

theorem complement_edge_deficit (T : Task K V) (n : R → ℕ)
    (p : Equiv.Perm Three) (D : ℝ)
    (hD : Profile.rankBound (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) T) ≤ D) :
    max 0 ((Fintype.card R : ℝ)-
      orientationSlack (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) T) p D) ≤
      (multiplicity T (p 0) (p 1) (p 2) : ℝ) := by
  have hlo := price_lower_bound (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) T) p D hD
  rw [price_directSum,resonant_price] at hlo
  have hhi := EdgeProfile.edge_price_le_extractable T p
  change price T p ≤ (multiplicity T (p 0) (p 1) (p 2) : ℝ) at hhi
  have hc : (Fintype.card R : ℝ) ≤ ∑ t, ((n t : ℝ)+1) := by
    calc
      (Fintype.card R : ℝ) = ∑ _t : R, (1 : ℝ) := by simp
      _ ≤ ∑ t, ((n t : ℝ)+1) := Finset.sum_le_sum fun t _ => le_add_of_nonneg_left (Nat.cast_nonneg _)
  exact max_le (Nat.cast_nonneg _) (by linarith only [hlo,hhi,hc])

/-- Physical cycle supply for the finite dependent Jordan product used by the
actual component partition, without converting to a list-based task. -/
theorem complement_cycle_deficit (T : Task K V) (n : R → ℕ)
    (p : Equiv.Perm Three) (D : ℝ)
    (hD : Profile.rankBound (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) T) ≤ D) :
    max 0 ((Fintype.card R : ℝ)-
      orientationSlack (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) T) p D) ≤
      (cycleMultiplicity T p : ℝ) := by
  have hh (a : Three) := complement_edge_deficit T n (cyclicPerm p a) D hD
  simp only [orientationSlack_cyclic] at hh
  rw [cycleMultiplicity,Nat.cast_min,Nat.cast_min]
  exact le_min (hh 0) (le_min (hh 1) (hh 2))

variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- All required cycles can be taken wholly outside the menu-bearing factors
once their proven edge multiplicities vanish. -/
theorem zero_complement_cycle_deficit (M : Task K W) (Z : Task K V) (n : R → ℕ)
    (hzero : ∀ i j k : Three, i≠j → i≠k → j≠k → multiplicity M i j k=0)
    (p : Equiv.Perm Three) (D : ℝ)
    (hD : Profile.rankBound (Profile.directSum (ResonantFiniteAssembly.task (K := K) n)
      (Profile.directSum M Z)) ≤ D) :
    max 0 ((Fintype.card R : ℝ)-
      orientationSlack (Profile.directSum (ResonantFiniteAssembly.task (K := K) n)
        (Profile.directSum M Z)) p D) ≤ (cycleMultiplicity Z p : ℝ) := by
  have hh (a : Three) := complement_edge_deficit (Profile.directSum M Z) n (cyclicPerm p a) D hD
  have hz (a : Three) := hzero ((cyclicPerm p a) 0) ((cyclicPerm p a) 1) ((cyclicPerm p a) 2)
    ((cyclicPerm p a).injective.ne (by decide)) ((cyclicPerm p a).injective.ne (by decide))
    ((cyclicPerm p a).injective.ne (by decide))
  simp only [orientationSlack_cyclic,multiplicity_directSum,hz,zero_add] at hh
  rw [cycleMultiplicity,Nat.cast_min,Nat.cast_min]
  exact le_min (hh 0) (le_min (hh 1) (hh 2))

/-- Convert the deficit bound directly into the requested number of genuinely
independent physical cycles in the zero-excess complement. -/
theorem zero_complement_bundle (M : Task K W) (Z : Task K V) (n : R → ℕ)
    (hzero : ∀ i j k : Three, i≠j → i≠k → j≠k → multiplicity M i j k=0)
    (p : Equiv.Perm Three) (D : ℝ)
    (hD : Profile.rankBound (Profile.directSum (ResonantFiniteAssembly.task (K := K) n)
      (Profile.directSum M Z)) ≤ D) (ε : ℕ)
    (hε : (ε : ℝ) ≤ max 0 ((Fintype.card R : ℝ)-
      orientationSlack (Profile.directSum (ResonantFiniteAssembly.task (K := K) n)
        (Profile.directSum M Z)) p D)) :
    ∃ (v : Three → Fin ε → V) (Q : Submodule K V),
      LinearIndependent K (fun x : (_a : Three) × Fin ε => v x.1 x.2) ∧
      (∀ a, EdgeBlock Z (cyclicPerm p a 0) (cyclicPerm p a 1) (cyclicPerm p a 2)
          (Submodule.span K (Set.range (v a))) ∧
        finrank K (Submodule.span K (Set.range (v a)))=ε) ∧
      TaskDecomposition.Split (configuration Z).spaces ⊤ Q
        (⨆ a, Submodule.span K (Set.range (v a))) := by
  have he : (ε : ℝ) ≤ cycleMultiplicity Z p := hε.trans (zero_complement_cycle_deficit M Z n hzero p D hD)
  exact exists_cycle_bundle Z p ε (by exact_mod_cast he)

end UploadBroadcast.FiniteCycleDeficits
