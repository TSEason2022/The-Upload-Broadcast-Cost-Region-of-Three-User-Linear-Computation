import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Nilpotent.Basic

namespace UploadBroadcast.NilpotentFiltration

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

/-- A commuting endomorphism that vanishes on the first kernel level also vanishes
on each higher kernel level after the corresponding number of iterations. -/
theorem ker_pow_le_of_commute {D J : Module.End K X}
    (hc : Commute D J) (hk : LinearMap.ker J ≤ LinearMap.ker D) (m : ℕ) :
    LinearMap.ker (J ^ m) ≤ LinearMap.ker (D ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    intro x hx
    change (D ^ (m + 1)) x = 0
    have hJ : (J ^ m) (J x) = 0 := by
      simpa only [LinearMap.mem_ker, pow_succ, Module.End.mul_apply] using hx
    have hD : (D ^ m) (J x) = 0 := ih hJ
    have hJD : J ((D ^ m) x) = 0 := by
      have he := congrArg (fun f : Module.End K X => f x) (hc.pow_left m).eq
      simpa only [Module.End.mul_apply] using he.symm.trans hD
    have := hk hJD
    simpa only [LinearMap.mem_ker, pow_succ', Module.End.mul_apply] using this

/-- Kernel inclusion and commutation transfer a specified nilpotence bound. -/
theorem pow_eq_zero_of_commute {D J : Module.End K X}
    (hc : Commute D J) (hk : LinearMap.ker J ≤ LinearMap.ker D)
    {m : ℕ} (hJ : J ^ m = 0) : D ^ m = 0 := by
  ext x
  have hx : x ∈ LinearMap.ker (J ^ m) := by simp [hJ]
  exact ker_pow_le_of_commute hc hk m hx

/-- Every idempotent that is scalar plus nilpotent is trivial. No finite
-dimensionality or nontriviality assumption is needed. -/
theorem idempotent_eq_zero_or_one_of_sub_smul_nilpotent
    {f : Module.End K X} (hi : IsIdempotentElem f) (a : K)
    (hn : IsNilpotent (f - a • (1 : Module.End K X))) : f = 0 ∨ f = 1 := by
  by_cases ha : a = 0
  · left
    subst a
    simp only [zero_smul, sub_zero] at hn
    exact hi.eq_zero_of_isNilpotent hn
  · right
    have hu : IsUnit (a • (1 : Module.End K X)) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (isUnit_iff_ne_zero.mpr ha).map (algebraMap K (Module.End K X))
    have hc : Commute (f - a • (1 : Module.End K X)) (a • 1) := by
      change (f - a • 1) * (a • 1) = (a • 1) * (f - a • 1)
      simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    have hf : IsUnit f := by
      simpa only [add_sub_cancel] using hn.isUnit_add_left_of_commute hu hc
    exact (IsIdempotentElem.iff_eq_one_of_isUnit hf).mp hi

#print axioms idempotent_eq_zero_or_one_of_sub_smul_nilpotent
#print axioms ker_pow_le_of_commute
#print axioms pow_eq_zero_of_commute

end UploadBroadcast.NilpotentFiltration
