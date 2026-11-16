import UploadBroadcast.Model

/-! Exact dimension loss on restriction to a relay kernel. -/
namespace UploadBroadcast
variable {K F W : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup W] [Module K W] [FiniteDimensional K F]

theorem condRank_add_intersection (B A : Submodule K F) :
    condRank B A + Module.finrank K ↥(A ⊓ B) = Module.finrank K B := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hle := Submodule.finrank_mono (le_sup_left : A ≤ A ⊔ B)
  unfold condRank
  omega

theorem restriction_rank_add_kernel (f : F →ₗ[K] W) (B : Submodule K F) :
    Module.finrank K (LinearMap.range (f.comp B.subtype)) +
      Module.finrank K ↥(B ⊓ LinearMap.ker f) = Module.finrank K B := by
  have h := (f.comp B.subtype).finrank_range_add_finrank_ker
  have hk : LinearMap.ker (f.comp B.subtype) =
      (B ⊓ LinearMap.ker f).comap B.subtype := by
    ext x
    simp [LinearMap.mem_ker, x.property]
  have hd := (Submodule.comapSubtypeEquivOfLe
    (inf_le_left : B ⊓ LinearMap.ker f ≤ B)).finrank_eq
  rw [hk, hd] at h
  exact h

/-- `eq:hyperplane-rank-loss`, strengthened to the kernel of any linear map.
Integer subtraction avoids silently truncating either difference. -/
theorem kernel_condRank_loss (f : F →ₗ[K] W) (B A : Submodule K F) :
    (condRank B A : ℤ) - (condRank (B ⊓ LinearMap.ker f) (A ⊓ LinearMap.ker f) : ℤ) =
      (Module.finrank K (LinearMap.range (f.comp B.subtype)) : ℤ) -
      (Module.finrank K (LinearMap.range (f.comp (A ⊓ B).subtype)) : ℤ) := by
  have h₁ := condRank_add_intersection B A
  have h₂ := condRank_add_intersection (B ⊓ LinearMap.ker f) (A ⊓ LinearMap.ker f)
  have h₃ := restriction_rank_add_kernel f B
  have h₄ := restriction_rank_add_kernel f (A ⊓ B)
  have heq : (A ⊓ LinearMap.ker f) ⊓ (B ⊓ LinearMap.ker f) =
      (A ⊓ B) ⊓ LinearMap.ker f := by
    rw [inf_inf_inf_comm, inf_idem]
  rw [heq] at h₂
  omega

end UploadBroadcast
