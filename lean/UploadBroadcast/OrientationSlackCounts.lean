import UploadBroadcast.OmniscienceCycleDeficits

namespace UploadBroadcast.OrientationSlackCounts
open EdgeDeficits OrientationRepairAllocation
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem plus_slack (T : Task K V) (D : ℝ) (c : Fin 6 → ℤ)
    (hc : ∀ j, Profile.entry T (.inl j)+(c j : ℝ)=D) :
    orientationSlack T (Equiv.refl _) D=(plus c : ℝ) := by
  have h₀ := hc 0
  have h₃ := hc 3
  have h₄ := hc 4
  change Profile.firstEntry T 0 1 2+(c 0 : ℝ)=D at h₀
  change Profile.firstEntry T 1 2 0+(c 3 : ℝ)=D at h₃
  change Profile.firstEntry T 2 0 1+(c 4 : ℝ)=D at h₄
  change (D-Profile.firstEntry T 0 1 2)+(D-Profile.firstEntry T 1 2 0)+
    (D-Profile.firstEntry T 2 0 1)=(plus c : ℝ)
  simp only [plus,Int.cast_add]
  linarith only [h₀,h₃,h₄]

theorem minus_slack (T : Task K V) (D : ℝ) (c : Fin 6 → ℤ)
    (hc : ∀ j, Profile.entry T (.inl j)+(c j : ℝ)=D) :
    orientationSlack T (Equiv.swap 0 1) D=(minus c : ℝ) := by
  have h₁ := hc 1
  have h₂ := hc 2
  have h₅ := hc 5
  change Profile.firstEntry T 0 2 1+(c 1 : ℝ)=D at h₁
  change Profile.firstEntry T 1 0 2+(c 2 : ℝ)=D at h₂
  change Profile.firstEntry T 2 1 0+(c 5 : ℝ)=D at h₅
  change (D-Profile.firstEntry T 1 0 2)+(D-Profile.firstEntry T 0 2 1)+
    (D-Profile.firstEntry T 2 1 0)=(minus c : ℝ)
  simp only [minus,Int.cast_add]
  linarith only [h₁,h₂,h₅]

theorem toNat_cast (a : ℤ) (ha : 0 ≤ a) : (a.toNat : ℝ)=(a : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg ha

theorem positive_cast (m : ℤ) (c : Fin 6 → ℤ) :
    (positiveCount m c : ℝ)=max 0 ((m : ℝ)-(plus c : ℝ)) := by
  simp only [positiveCount,Int.cast_max,Int.cast_zero,Int.cast_sub]

theorem negative_cast (m : ℤ) (c : Fin 6 → ℤ) :
    (negativeCount m c : ℝ)=max 0 ((m : ℝ)-(minus c : ℝ)) := by
  simp only [negativeCount,Int.cast_max,Int.cast_zero,Int.cast_sub]

variable {R X Y Z : Type*} [Fintype R]
  [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
  [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]

/-- Exact integer repair counts are bounded by actual physical cycle
multiplicities, using the full Ω-plus-residual budget. -/
theorem counts_le_cycles (n : R → ℕ) (M : Task K X) (N : Task K Y) (O : Task K Z)
    (hM : ∀ i j k : Three, i≠j → i≠k → j≠k → EdgeExtraction.multiplicity M i j k=0)
    (hO : ∀ i, O.U i=⊤) (D : ℝ)
    (hD : Profile.rankBound (Profile.directSum
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (Profile.directSum M N)) O) ≤ D)
    (c : Fin 6 → ℤ)
    (hc : ∀ j, Profile.entry (Profile.directSum
      (Profile.directSum (ResonantFiniteAssembly.task (K := K) n) (Profile.directSum M N)) O) (.inl j)+
        (c j : ℝ)=D) :
    (positiveCount (Fintype.card R) c).toNat ≤ cycleMultiplicity N (Equiv.refl _) ∧
    (negativeCount (Fintype.card R) c).toNat ≤ cycleMultiplicity N (Equiv.swap 0 1) := by
  have hp := OmniscienceCycleDeficits.zero_cycle_deficit n M N O hM hO (Equiv.refl _) D hD
  have hn := OmniscienceCycleDeficits.zero_cycle_deficit n M N O hM hO (Equiv.swap 0 1) D hD
  rw [plus_slack _ D c hc] at hp
  rw [minus_slack _ D c hc] at hn
  have heP : ((positiveCount (Fintype.card R) c).toNat : ℝ)=
      max 0 ((Fintype.card R : ℝ)-(plus c : ℝ)) := by
    rw [toNat_cast (positiveCount (Fintype.card R) c) (le_max_left _ _),positive_cast,Int.cast_natCast]
  have heN : ((negativeCount (Fintype.card R) c).toNat : ℝ)=
      max 0 ((Fintype.card R : ℝ)-(minus c : ℝ)) := by
    rw [toNat_cast (negativeCount (Fintype.card R) c) (le_max_left _ _),negative_cast,Int.cast_natCast]
  constructor
  · exact_mod_cast heP.trans_le hp
  · exact_mod_cast heN.trans_le hn

end UploadBroadcast.OrientationSlackCounts
