import UploadBroadcast.LinearAlgebra
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Fin

/-! Descent of local cofactor functionals along the aligned relation space.
This proves the no-odd-dependency step of the binary broadcast construction. -/
namespace UploadBroadcast.AlignedRelation
open scoped BigOperators
variable {K F I : Type*} [Field K] [AddCommGroup F] [Module K F]
  [Fintype I] [DecidableEq I]

def signalSum (U : I → Submodule K F) : (∀ i, U i) →ₗ[K] F :=
  ∑ i, (U i).subtype.comp (LinearMap.proj i)

def formSum (U : I → Submodule K F) (f : ∀ i, U i →ₗ[K] K) :
    (∀ i, U i) →ₗ[K] K := ∑ i, (f i).comp (LinearMap.proj i)

def relationForm (U : I → Submodule K F) (f : ∀ i, U i →ₗ[K] K) (i : I) :
    LinearMap.ker (signalSum U) →ₗ[K] K :=
  ((f i).comp (LinearMap.proj i)).comp (LinearMap.ker (signalSum U)).subtype

/-- If local functionals vanish on their side-information spaces, and their
sum vanishes on the aligned relation kernel, each local functional is zero,
provided the side-information spaces span the ambient space. -/
theorem forms_zero_of_relation_sum_zero
    (A U : I → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (f : ∀ i, U i →ₗ[K] K)
    (hlocal : ∀ i (v : U i), (v : F) ∈ A i → f i v = 0)
    (hrel : (∑ i, relationForm U f i) = 0) : ∀ i, f i = 0 := by
  classical
  have hker : LinearMap.ker (signalSum U) ≤ LinearMap.ker (formSum U f) := by
    intro w hw
    have hh := LinearMap.congr_fun hrel ⟨w,hw⟩
    simpa [relationForm, formSum] using hh
  obtain ⟨l,hl⟩ := UploadBroadcast.factors_through_of_ker_le (signalSum U) (formSum U f) hker
  have hsingle (i : I) (v : U i) : l (v : F) = f i v := by
    have hh := LinearMap.congr_fun hl (Pi.single i v)
    have hs : signalSum U (Pi.single i v) = (v : F) := by
      simp only [signalSum, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        Submodule.subtype_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji]
      · simp
    have hf : formSum U f (Pi.single i v) = f i v := by
      simp only [formSum, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji]
      · simp
    simpa only [LinearMap.comp_apply, hs, hf] using hh
  have hAz : (⨆ i, A i) ≤ LinearMap.ker l := by
    apply iSup_le
    intro i a ha
    change l a = 0
    exact (hsingle i ⟨a,hAU i ha⟩).trans (hlocal i ⟨a,hAU i ha⟩ ha)
  have hlzero : l = 0 := by
    apply LinearMap.ker_eq_top.mp
    apply top_unique
    simpa [hspan] using hAz
  intro i
  ext v
  have hh := hsingle i v
  simpa [hlzero] using hh.symm

/-- In particular nonzero local relation forms cannot sum to zero. -/
theorem relation_sum_ne_zero
    (A U : I → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (f : ∀ i, U i →ₗ[K] K)
    (hlocal : ∀ i (v : U i), (v : F) ∈ A i → f i v = 0)
    (hnonzero : ∃ i, relationForm U f i ≠ 0) :
    (∑ i, relationForm U f i) ≠ 0 := by
  intro hrel
  obtain ⟨i,hi⟩ := hnonzero
  have hz := forms_zero_of_relation_sum_zero A U hAU hspan f hlocal hrel i
  apply hi
  simp [relationForm, hz]

end UploadBroadcast.AlignedRelation
