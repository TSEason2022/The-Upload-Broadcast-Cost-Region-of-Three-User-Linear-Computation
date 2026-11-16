import UploadBroadcast.FiniteCycleDeficits
import UploadBroadcast.OmniscienceProfile

namespace UploadBroadcast.OmniscienceCycleDeficits
open Module EdgeDeficits EdgeExtraction
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem omniscience_price_zero (O : Task K V) (hU : ∀ i, O.U i=⊤) (p : Equiv.Perm Three) :
    price O p=0 := by
  have h₀ := OmniscienceProfile.first_entry O hU p
  have h₁ := OmniscienceProfile.first_entry O hU (cyclicPerm p 1)
  change Profile.firstEntry O (p 1) (p 2) (p 0)=(condRank ⊤ (O.A (p 1)) : ℝ) at h₁
  have hQ := OmniscienceProfile.second_entry O hU ((Equiv.swap 0 1).trans p) (p 2)
  change 2*Profile.secondEntry O (p 1) (p 0) (p 2) (p 2)=
    (∑ i, (condRank ⊤ (O.A i) : ℝ))-condRank ⊤ (O.A (p 2)) at hQ
  rw [OmniscienceProfile.sum_reindex_three _ p] at hQ
  unfold price
  linarith only [h₀,h₁,hQ]

theorem omniscience_multiplicity_zero (O : Task K V) (hU : ∀ i, O.U i=⊤) (i j k : Three) :
    multiplicity O i j k=0 := by
  have hb : EdgeExtraction.blocked O i j=⊤ := by
    unfold EdgeExtraction.blocked
    rw [hU i,hU j,inf_top_eq,sup_top_eq]
  rw [EdgeExtraction.multiplicity,hb,inf_top_eq,Nat.sub_self]

variable {R X Y Z : Type*} [Fintype R]
  [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
  [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]

theorem zero_edge_deficit (n : R → ℕ) (M : Task K X) (N : Task K Y) (O : Task K Z)
    (hM : ∀ i j k : Three, i≠j → i≠k → j≠k → multiplicity M i j k=0)
    (hO : ∀ i, O.U i=⊤) (p : Equiv.Perm Three) (D : ℝ)
    (hD : Profile.rankBound (Profile.directSum
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (Profile.directSum M N)) O) ≤ D) :
    max 0 ((Fintype.card R : ℝ)-orientationSlack (Profile.directSum
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (Profile.directSum M N)) O) p D) ≤
      (multiplicity N (p 0) (p 1) (p 2) : ℝ) := by
  have hlo := price_lower_bound (Profile.directSum
    (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (Profile.directSum M N)) O) p D hD
  rw [price_directSum,price_directSum,price_directSum,FiniteCycleDeficits.resonant_price,
    omniscience_price_zero O hO,add_zero] at hlo
  have hm := EdgeProfile.edge_price_le_extractable M p
  change price M p ≤ (multiplicity M (p 0) (p 1) (p 2) : ℝ) at hm
  rw [hM _ _ _ (p.injective.ne (by decide)) (p.injective.ne (by decide))
    (p.injective.ne (by decide)),Nat.cast_zero] at hm
  have hn := EdgeProfile.edge_price_le_extractable N p
  change price N p ≤ (multiplicity N (p 0) (p 1) (p 2) : ℝ) at hn
  have hc : (Fintype.card R : ℝ) ≤ ∑ t, ((n t : ℝ)+1) := by
    calc
      (Fintype.card R : ℝ) = ∑ _t : R, (1 : ℝ) := by simp
      _ ≤ ∑ t, ((n t : ℝ)+1) := Finset.sum_le_sum fun t _ => le_add_of_nonneg_left (Nat.cast_nonneg _)
  exact max_le (Nat.cast_nonneg _) (by linarith only [hlo,hm,hn,hc])

/-- The full task's Ω profile stays in the budget calculation, but every
required physical cycle is extracted solely from the zero-excess residual. -/
theorem zero_cycle_deficit (n : R → ℕ) (M : Task K X) (N : Task K Y) (O : Task K Z)
    (hM : ∀ i j k : Three, i≠j → i≠k → j≠k → multiplicity M i j k=0)
    (hO : ∀ i, O.U i=⊤) (p : Equiv.Perm Three) (D : ℝ)
    (hD : Profile.rankBound (Profile.directSum
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (Profile.directSum M N)) O) ≤ D) :
    max 0 ((Fintype.card R : ℝ)-orientationSlack (Profile.directSum
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (Profile.directSum M N)) O) p D) ≤
      (cycleMultiplicity N p : ℝ) := by
  have hh (a : Three) := zero_edge_deficit n M N O hM hO (cyclicPerm p a) D hD
  simp only [orientationSlack_cyclic] at hh
  rw [cycleMultiplicity,Nat.cast_min,Nat.cast_min]
  exact le_min (hh 0) (le_min (hh 1) (hh 2))

end UploadBroadcast.OmniscienceCycleDeficits
