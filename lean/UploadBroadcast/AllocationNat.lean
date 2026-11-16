import UploadBroadcast.AllocationRanks

namespace UploadBroadcast
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Natural-number quotas for the scalar construction. Pair labels are
complementary: x is shared by users 1 and 2, y by 0 and 2, z by 0 and 1. -/
structure ScalarAllocation (A U : Fin 3 → Submodule K F) where
  r : ℕ
  x : ℕ
  y : ℕ
  z : ℕ
  al : ℕ
  h : Fin 3 → ℕ
  hcommon : ∀ i, r ≤ condRank (U 0 ⊓ U 1 ⊓ U 2) (A i)
  hpair12 : r+x ≤ Allocation.pairRank A U 1 2
  hpair02 : r+y ≤ Allocation.pairRank A U 0 2
  hpair01 : r+z ≤ Allocation.pairRank A U 0 1
  hpairs0 : r+y+z ≤ Allocation.pairSumRank A U 0 1 2
  hpairs1 : r+x+z ≤ Allocation.pairSumRank A U 1 0 2
  hpairs2 : r+x+y ≤ Allocation.pairSumRank A U 2 0 1
  hal0 : r+y+z+al ≤ Allocation.enlargedRank A U 0 1 2
  hal1 : r+x+z+al ≤ Allocation.enlargedRank A U 1 0 2
  hal2 : r+x+y+al ≤ Allocation.enlargedRank A U 2 0 1
  total0 : r+y+z+al+h 0 = Allocation.demandRank A U 0
  total1 : r+x+z+al+h 1 = Allocation.demandRank A U 1
  total2 : r+x+y+al+h 2 = Allocation.demandRank A U 2

/-- Number of scalar broadcasts used by these quotas. -/
def ScalarAllocation.length {A U : Fin 3 → Submodule K F} (s : ScalarAllocation A U) : ℕ :=
  s.r+s.x+s.y+s.z+2*s.al+s.h 0+s.h 1+s.h 2

namespace Allocation
/-- Numerical LP optimum; this definition makes no operational optimality claim. -/
noncomputable def actualNumericLP (A U : Fin 3 → Submodule K F) : ℝ :=
  lcbcCostValue (commonRank A U) (pairRank A U 1 2) (pairRank A U 0 2)
    (pairRank A U 0 1) (pairSumRank A U 0 1 2) (pairSumRank A U 1 0 2)
    (pairSumRank A U 2 0 1) (enlargedRank A U 0 1 2)
    (enlargedRank A U 1 0 2) (enlargedRank A U 2 0 1)
    ((demandRank A U 0 : ℝ)+demandRank A U 1+demandRank A U 2)
/-- The exact integer allocation gives honest natural quotas, with all
residual dimensions nonnegative before conversion. -/
theorem actual_nat_lcbc_allocation (A U : Fin 3 → Submodule K F) :
    ∃ s : ScalarAllocation A U,
      s.r = commonRank A U ∧ (s.length : ℤ) = ⌈actualNumericLP A U⌉ := by
  obtain ⟨X,Y,Z,a,hf,hm0,hm1,hm2,hcost⟩ := actual_integer_lcbc_allocation A U
  rcases hf with ⟨_,hX,hY,hZ,ha,_,hu1,hu2,hu3,hp0,hp1,hp2,hb0,hb1,hb2⟩
  have hXi : 0 ≤ X := by exact_mod_cast hX
  have hYi : 0 ≤ Y := by exact_mod_cast hY
  have hZi : 0 ≤ Z := by exact_mod_cast hZ
  have hai : 0 ≤ a := by exact_mod_cast ha
  lift X to ℕ using hXi with X hXeq
  lift Y to ℕ using hYi with Y hYeq
  lift Z to ℕ using hZi with Z hZeq
  lift a to ℕ using hai with a haeq
  have u1 : commonRank A U+X ≤ pairRank A U 1 2 := by exact_mod_cast hu1
  have u2 : commonRank A U+Y ≤ pairRank A U 0 2 := by exact_mod_cast hu2
  have u3 : commonRank A U+Z ≤ pairRank A U 0 1 := by exact_mod_cast hu3
  have p0 : commonRank A U+Y+Z ≤ pairSumRank A U 0 1 2 := by exact_mod_cast hp0
  have p1 : commonRank A U+X+Z ≤ pairSumRank A U 1 0 2 := by exact_mod_cast hp1
  have p2 : commonRank A U+X+Y ≤ pairSumRank A U 2 0 1 := by exact_mod_cast hp2
  have b0 : commonRank A U+Y+Z+a ≤ enlargedRank A U 0 1 2 := by exact_mod_cast hb0
  have b1 : commonRank A U+X+Z+a ≤ enlargedRank A U 1 0 2 := by exact_mod_cast hb1
  have b2 : commonRank A U+X+Y+a ≤ enlargedRank A U 2 0 1 := by exact_mod_cast hb2
  let h : Fin 3 → ℕ := ![demandRank A U 0-(commonRank A U+Y+Z+a),
    demandRank A U 1-(commonRank A U+X+Z+a),
    demandRank A U 2-(commonRank A U+X+Y+a)]
  have t0 : commonRank A U+Y+Z+a+h 0 = demandRank A U 0 := by
    dsimp [h]; omega
  have t1 : commonRank A U+X+Z+a+h 1 = demandRank A U 1 := by
    dsimp [h]; omega
  have t2 : commonRank A U+X+Y+a+h 2 = demandRank A U 2 := by
    dsimp [h]; omega
  let s : ScalarAllocation A U := ⟨commonRank A U,X,Y,Z,a,h,
    commonRank_le A U,u1,u2,u3,p0,p1,p2,b0,b1,b2,t0,t1,t2⟩
  refine ⟨s,rfl,?_⟩
  have tc0 := congrArg (fun n : ℕ => (n : ℤ)) t0
  have tc1 := congrArg (fun n : ℕ => (n : ℤ)) t1
  have tc2 := congrArg (fun n : ℕ => (n : ℤ)) t2
  norm_cast at tc0 tc1 tc2
  dsimp [ScalarAllocation.length,s]
  push_cast
  have hc : (demandRank A U 0 : ℤ)+demandRank A U 1+demandRank A U 2-
      2*(commonRank A U : ℤ)-X-Y-Z-a = ⌈actualNumericLP A U⌉ := by
    simpa [actualNumericLP] using hcost
  omega

end Allocation
end UploadBroadcast
