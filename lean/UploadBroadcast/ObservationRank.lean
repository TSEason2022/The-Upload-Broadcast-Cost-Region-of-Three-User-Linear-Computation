import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The dual-source representation is the basis-free version of xᵀB.
This file proves its single and joint rank identities without probabilistic
assumptions. -/
namespace UploadBroadcast
open Module
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Restriction of a source covector to its observed coefficient subspace. -/
def dualObserve (B : Submodule K F) : (F →ₗ[K] K) →ₗ[K] (B →ₗ[K] K) where
  toFun x := x.comp B.subtype
  map_add' x y := by ext b; rfl
  map_smul' a x := by ext b; rfl

theorem dualObserve_surjective (B : Submodule K F) :
    Function.Surjective (dualObserve B) := by
  intro b
  obtain ⟨x,hx⟩ := b.exists_extend
  exact ⟨x,hx⟩

theorem dualObserve_rank [FiniteDimensional K F] (B : Submodule K F) :
    finrank K (LinearMap.range (dualObserve B)) = finrank K B := by
  rw [LinearMap.range_eq_top.mpr (dualObserve_surjective B), finrank_top,
    Subspace.dual_finrank_eq]

theorem dualObserve_joint_ker (B C : Submodule K F) :
    LinearMap.ker ((dualObserve B).prod (dualObserve C)) =
      LinearMap.ker (dualObserve (B ⊔ C)) := by
  ext x
  constructor
  · intro hx
    have hBC : dualObserve B x = 0 ∧ dualObserve C x = 0 := by
      change (dualObserve B x, dualObserve C x) = (0,0) at hx
      exact ⟨congrArg Prod.fst hx, congrArg Prod.snd hx⟩
    apply LinearMap.mem_ker.mpr
    ext z
    obtain ⟨b,hb,c,hc,hbc⟩ := Submodule.mem_sup.mp z.property
    have hb0 := LinearMap.congr_fun hBC.1 ⟨b,hb⟩
    have hc0 := LinearMap.congr_fun hBC.2 ⟨c,hc⟩
    change x (z:F) = 0
    rw [← hbc, map_add]
    exact (congrArg₂ (· + ·) hb0 hc0).trans (zero_add 0)
  · intro hx
    have hh := LinearMap.mem_ker.mp hx
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · ext b
      exact LinearMap.congr_fun hh ⟨b, (show B ≤ B ⊔ C from le_sup_left) b.property⟩
    · ext c
      exact LinearMap.congr_fun hh ⟨c, (show C ≤ B ⊔ C from le_sup_right) c.property⟩

theorem dualObserve_joint_rank [FiniteDimensional K F] (B C : Submodule K F) :
    finrank K (LinearMap.range ((dualObserve B).prod (dualObserve C))) =
      finrank K ↥(B ⊔ C) := by
  have h₁ := ((dualObserve B).prod (dualObserve C)).finrank_range_add_finrank_ker
  have h₂ := (dualObserve (B ⊔ C)).finrank_range_add_finrank_ker
  rw [dualObserve_joint_ker] at h₁
  rw [dualObserve_rank] at h₂
  omega

end UploadBroadcast
