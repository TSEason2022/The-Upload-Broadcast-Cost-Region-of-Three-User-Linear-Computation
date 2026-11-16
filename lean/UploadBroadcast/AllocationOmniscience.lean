import UploadBroadcast.Allocation

namespace UploadBroadcast.Allocation

/-- If the numerical optimum for integer deficits is integral, it is
attained by integer rates. Together with omniscience_half_integral this
proves the exact one-or-two-instance arithmetic assertion. -/
theorem omniscience_integral_optimizer (a b c n : ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hn : (n:ℝ) = omniscienceValue a b c) :
    ∃ X Y Z : ℤ, OmniscienceFeasible a b c X Y Z ∧
      (X:ℝ)+Y+Z = omniscienceValue a b c := by
  have ha' : (0:ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (0:ℝ) ≤ b := by exact_mod_cast hb
  have hc' : (0:ℝ) ≤ c := by exact_mod_cast hc
  have va : (a:ℝ) ≤ omniscienceValue a b c :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have vb : (b:ℝ) ≤ omniscienceValue a b c :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have vc : (c:ℝ) ≤ omniscienceValue a b c :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have vs : ((a:ℝ)+b+c)/2 ≤ omniscienceValue a b c :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  by_cases h₁ : (a:ℝ) ≤ b+c
  · by_cases h₂ : (b:ℝ) ≤ a+c
    · by_cases h₃ : (c:ℝ) ≤ a+b
      · have vu : omniscienceValue a b c ≤ ((a:ℝ)+b+c)/2 := by
          unfold omniscienceValue
          simp only [max_le_iff]
          exact ⟨⟨by linarith,by linarith⟩,by linarith,le_refl _⟩
        refine ⟨n-a,n-b,n-c,?_,?_⟩
        · unfold OmniscienceFeasible
          push_cast
          exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
        · push_cast
          linarith
      · have hf : OmniscienceFeasible a b c b ((c-b : ℤ) : ℝ) ((0 : ℤ) : ℝ) := by
          unfold OmniscienceFeasible
          push_cast
          exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
        refine ⟨b,c-b,0,hf,le_antisymm ?_ (omniscience_lower_bound hf)⟩
        push_cast
        linarith
    · have hf : OmniscienceFeasible a b c c ((0 : ℤ) : ℝ) ((b-c : ℤ) : ℝ) := by
        unfold OmniscienceFeasible
        push_cast
        exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
      refine ⟨c,0,b-c,hf,le_antisymm ?_ (omniscience_lower_bound hf)⟩
      push_cast
      linarith
  · have hf : OmniscienceFeasible a b c ((0 : ℤ) : ℝ) c ((a-c : ℤ) : ℝ) := by
      unfold OmniscienceFeasible
      push_cast
      exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
    refine ⟨0,c,a-c,hf,le_antisymm ?_ (omniscience_lower_bound hf)⟩
    push_cast
    linarith

/-- Natural-number rate version for finite-dimensional encoder APIs. -/
theorem omniscience_integral_optimizer_nat (a b c n : ℕ)
    (hn : (n:ℝ) = omniscienceValue a b c) :
    ∃ X Y Z : ℕ, OmniscienceFeasible a b c X Y Z ∧
      (X:ℝ)+Y+Z = omniscienceValue a b c := by
  obtain ⟨X,Y,Z,hf,he⟩ := omniscience_integral_optimizer a b c n
    (by positivity) (by positivity) (by positivity) (by simpa using hn)
  have hx : (0:ℤ) ≤ X := by exact_mod_cast hf.1
  have hy : (0:ℤ) ≤ Y := by exact_mod_cast hf.2.1
  have hz : (0:ℤ) ≤ Z := by exact_mod_cast hf.2.2.1
  have hx' : ((X.toNat:ℕ):ℝ) = (X:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hx
  have hy' : ((Y.toNat:ℕ):ℝ) = (Y:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hy
  have hz' : ((Z.toNat:ℕ):ℝ) = (Z:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hz
  refine ⟨X.toNat,Y.toNat,Z.toNat,?_,?_⟩
  · simpa only [hx',hy',hz',Int.cast_natCast] using hf
  · simpa only [hx',hy',hz',Int.cast_natCast] using he

/-- Natural-number numerator version of the optimal two-instance rates. -/
theorem omniscience_half_integral_nat (a b c : ℕ) :
    ∃ X Y Z : ℕ,
      OmniscienceFeasible a b c ((X:ℝ)/2) ((Y:ℝ)/2) ((Z:ℝ)/2) ∧
      ((X:ℝ)/2)+((Y:ℝ)/2)+((Z:ℝ)/2) = omniscienceValue a b c := by
  obtain ⟨X,Y,Z,hf,he⟩ := omniscience_half_integral a b c
    (by positivity) (by positivity) (by positivity)
  have hx : (0:ℤ) ≤ X := by
    have : (0:ℝ) ≤ X := by linarith [hf.1]
    exact_mod_cast this
  have hy : (0:ℤ) ≤ Y := by
    have : (0:ℝ) ≤ Y := by linarith [hf.2.1]
    exact_mod_cast this
  have hz : (0:ℤ) ≤ Z := by
    have : (0:ℝ) ≤ Z := by linarith [hf.2.2.1]
    exact_mod_cast this
  have hx' : ((X.toNat:ℕ):ℝ) = (X:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hx
  have hy' : ((Y.toNat:ℕ):ℝ) = (Y:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hy
  have hz' : ((Z.toNat:ℕ):ℝ) = (Z:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hz
  refine ⟨X.toNat,Y.toNat,Z.toNat,?_,?_⟩
  · simpa only [hx',hy',hz',Int.cast_natCast] using hf
  · simpa only [hx',hy',hz',Int.cast_natCast] using he

end UploadBroadcast.Allocation
