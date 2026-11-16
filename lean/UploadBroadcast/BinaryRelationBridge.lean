import UploadBroadcast.BinaryCoordination
import UploadBroadcast.ScalarIncidence

/-! Exact transport between the kernel-of-sum and the three-coordinate
aligned relation used by the scalar coding implementation. -/
namespace UploadBroadcast
variable {F : Type*} [AddCommGroup F] [Module (ZMod 2) F]

private theorem binary_add_self (x : F) : x+x=0 := by
  have hz : (2 : ZMod 2)=0 := by decide
  calc
    x+x = (2 : ZMod 2) • x := (two_smul (ZMod 2) x).symm
    _ = 0 := by rw [hz,zero_smul]

def kernelToAligned (U : Fin 3 → Submodule (ZMod 2) F) :
    LinearMap.ker (AlignedRelation.signalSum U) →ₗ[ZMod 2]
      alignedRelation (U 0) (U 1) (U 2) where
  toFun h := ⟨((h.1 0:F),(h.1 1:F),(h.1 2:F)),
    (h.1 0).property,(h.1 1).property,(h.1 2).property,by
      have hz := h.property
      change AlignedRelation.signalSum U h.1=0 at hz
      have hs : (h.1 0:F)+(h.1 1:F)+(h.1 2:F)=0 := by
        simpa [AlignedRelation.signalSum,LinearMap.sum_apply,Fin.sum_univ_succ,add_assoc] using hz
      change (h.1 0:F)+(h.1 1:F)=(h.1 2:F)
      calc
        (h.1 0:F)+(h.1 1:F) = ((h.1 0:F)+(h.1 1:F)+(h.1 2:F))+(h.1 2:F) := by
          rw [add_assoc, binary_add_self, add_zero]
        _ = (h.1 2:F) := by rw [hs,zero_add]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem kernelToAligned_projection (U : Fin 3 → Submodule (ZMod 2) F)
    (h : LinearMap.ker (AlignedRelation.signalSum U)) (i : Fin 3) :
    ScalarIncidence.relationProjection U i (kernelToAligned U h) = (h.1 i:F) := by
  fin_cases i <;> rfl

def alignedToKernel (U : Fin 3 → Submodule (ZMod 2) F) :
    alignedRelation (U 0) (U 1) (U 2) →ₗ[ZMod 2]
      LinearMap.ker (AlignedRelation.signalSum U) where
  toFun h := ⟨fun i =>
      ⟨ScalarIncidence.relationProjection U i h, by
        fin_cases i
        · exact h.property.1
        · exact h.property.2.1
        · exact h.property.2.2.1⟩,
    by
      change AlignedRelation.signalSum U _ = 0
      simp only [AlignedRelation.signalSum,LinearMap.sum_apply,LinearMap.comp_apply,
        LinearMap.proj_apply,Submodule.subtype_apply,Fin.sum_univ_succ]
      change h.1.1+(h.1.2.1+(h.1.2.2+0))=0
      rw [add_zero, ← add_assoc, h.property.2.2.2, binary_add_self]⟩
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

/-- Actual linear equivalence of the two relation representations. -/
def binaryRelationEquiv (U : Fin 3 → Submodule (ZMod 2) F) :
    LinearMap.ker (AlignedRelation.signalSum U) ≃ₗ[ZMod 2]
      alignedRelation (U 0) (U 1) (U 2) where
  toLinearMap := kernelToAligned U
  invFun := alignedToKernel U
  left_inv h := by ext i; exact kernelToAligned_projection U h i
  right_inv h := by apply Subtype.ext; rfl

/-- Usable aligned-group selector for the actual scalar-broadcast representation. -/
theorem binary_aligned_projection_group
    (A U : Fin 3 → Submodule (ZMod 2) F) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i)=⊤) (f : Fin 3 → F →ₗ[ZMod 2] ZMod 2)
    (hlocal : ∀ i x, x ∈ A i → f i x=0)
    (hnz : ∀ i, (f i).comp (ScalarIncidence.relationProjection U i) ≠ 0) :
    ∃ t : alignedRelation (U 0) (U 1) (U 2),
      ∀ i, f i (ScalarIncidence.relationProjection U i t) ≠ 0 := by
  let g : ∀ i, U i →ₗ[ZMod 2] ZMod 2 := fun i => (f i).comp (U i).subtype
  have hgnz : ∀ i, AlignedRelation.relationForm U g i ≠ 0 := by
    intro i he
    apply hnz i
    ext t
    have hh := LinearMap.congr_fun he (alignedToKernel U t)
    exact hh
  obtain ⟨h,hh⟩ := binary_aligned_group A U hAU hspan g
    (fun i v hv => hlocal i v hv) hgnz
  refine ⟨kernelToAligned U h, fun i => ?_⟩
  rw [kernelToAligned_projection]
  change g i (h.1 i) ≠ 0
  rw [hh i]
  exact one_ne_zero

end UploadBroadcast
