import UploadBroadcast.TripodSubobjectExclusion
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Removing the intrinsic tripod plane leaves genuinely independent sides.
The regularity input is used only to show that demand dimensions survive. -/
namespace UploadBroadcast.TripodQuotient
open TaskDecomposition TripodSubobjectExclusion
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- The full tripod plane is contained in every pair of side sums. -/
theorem tripodPlane_le_pairs (T : TaskDecomposition.Task K F) :
    tripodPlane K T ≤ T.A 0 ⊔ T.A 1 ∧
    tripodPlane K T ≤ T.A 0 ⊔ T.A 2 ∧
    tripodPlane K T ≤ T.A 1 ⊔ T.A 2 := by
  exact ⟨sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right),
    sup_le (inf_le_left.trans le_sup_left) inf_le_right,
    sup_le inf_le_right (inf_le_left.trans le_sup_left)⟩

/-- The third tripod side also lies in the plane defined using the first two. -/
theorem third_tripod_le (T : TaskDecomposition.Task K F) :
    T.A 2 ⊓ (T.A 0 ⊔ T.A 1) ≤ tripodPlane K T := by
  intro p hp
  obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp hp.2
  have ha' : a ∈ T.A 1 ⊔ T.A 2 := by
    have he' : a=p-b := by rw [←he]; abel
    rw [he']
    exact (T.A 1 ⊔ T.A 2).sub_mem (Submodule.mem_sup_right hp.1) (Submodule.mem_sup_left hb)
  have hb' : b ∈ T.A 0 ⊔ T.A 2 := by
    have he' : b=p-a := by rw [←he]; abel
    rw [he']
    exact (T.A 0 ⊔ T.A 2).sub_mem (Submodule.mem_sup_right hp.1) (Submodule.mem_sup_left ha)
  exact Submodule.mem_sup.mpr ⟨a,⟨ha,ha'⟩,b,⟨hb,hb'⟩,he⟩

/-- A quotient separates A from B whenever the quotient kernel lies in B
and contains their entire intersection. -/
theorem disjoint_quotient_images (A B P : Submodule K F)
    (hPB : P ≤ B) (hAB : A ⊓ B ≤ P) :
    Disjoint (A.map P.mkQ) (B.map P.mkQ) := by
  apply Submodule.disjoint_def.mpr
  intro q hqA hqB
  obtain ⟨a,ha,heA⟩ := Submodule.mem_map.mp hqA
  obtain ⟨b,hb,heB⟩ := Submodule.mem_map.mp hqB
  have he : P.mkQ (a-b)=0 := by rw [map_sub,heA,heB,sub_self]
  have hab : a-b ∈ P := (Submodule.Quotient.mk_eq_zero P).mp he
  have haB : a ∈ B := by
    have haa : a=(a-b)+b := by abel
    rw [haa]
    exact B.add_mem (hPB hab) hb
  have haP := hAB ⟨ha,haB⟩
  rw [←heA]
  exact (Submodule.Quotient.mk_eq_zero P).mpr haP

/-- The three sides become mutually independent after removing the full
tripod plane; each side misses the sum of the other two. -/
theorem quotient_sides_independent (T : TaskDecomposition.Task K F) :
    let P := tripodPlane K T
    Disjoint ((T.A 0).map P.mkQ) (((T.A 1).map P.mkQ) ⊔ ((T.A 2).map P.mkQ)) ∧
    Disjoint ((T.A 1).map P.mkQ) (((T.A 0).map P.mkQ) ⊔ ((T.A 2).map P.mkQ)) ∧
    Disjoint ((T.A 2).map P.mkQ) (((T.A 0).map P.mkQ) ⊔ ((T.A 1).map P.mkQ)) := by
  dsimp only
  rw [←Submodule.map_sup,←Submodule.map_sup,←Submodule.map_sup]
  exact ⟨disjoint_quotient_images _ _ _ (tripodPlane_le_pairs T).2.2 le_sup_left,
    disjoint_quotient_images _ _ _ (tripodPlane_le_pairs T).2.1 le_sup_right,
    disjoint_quotient_images _ _ _ (tripodPlane_le_pairs T).1 (third_tripod_le T)⟩

/-- Side spanning descends through the actual quotient map. -/
theorem quotient_sides_span (T : TaskDecomposition.Task K F)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2=⊤) :
    let P := tripodPlane K T
    (((T.A 0).map P.mkQ) ⊔ ((T.A 1).map P.mkQ)) ⊔ ((T.A 2).map P.mkQ)=⊤ := by
  dsimp only
  rw [←Submodule.map_sup,←Submodule.map_sup,hspan]
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)

/-- Kernel of quotient restricted to a subspace, with both memberships retained. -/
def quotientRestrictedKernelEquiv (A P : Submodule K F) :
    LinearMap.ker (P.mkQ.comp A.subtype) ≃ₗ[K] ↥(A ⊓ P) where
  toFun x := ⟨x.1.1,x.1.property,(Submodule.Quotient.mk_eq_zero P).mp x.property⟩
  invFun x := ⟨⟨x.1,x.property.1⟩,(Submodule.Quotient.mk_eq_zero P).mpr x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem quotient_image_finrank [FiniteDimensional K F] (A P : Submodule K F) :
    Module.finrank K (A.map P.mkQ)+Module.finrank K ↥(A ⊓ P)=Module.finrank K A := by
  have he := (P.mkQ.comp A.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp,Submodule.range_subtype,(quotientRestrictedKernelEquiv A P).finrank_eq] at he
  exact he

/-- The actual quotient task; no formal coordinates replace the subspaces. -/
def quotientTask (T : TaskDecomposition.Task K F) :
    TaskDecomposition.Task K (F ⧸ tripodPlane K T) where
  A i := (T.A i).map (tripodPlane K T).mkQ
  U i := (T.U i).map (tripodPlane K T).mkQ
  nested i := Submodule.map_mono (T.nested i)

/-- For a regular indecomposable, removing the full tripod does not change
any user's demand dimension. This is the injective relation-space prerequisite. -/
theorem quotient_preserves_demand_dimensions {K F : Type} [Field K]
    [AddCommGroup F] [Module K F] [FiniteDimensional K F]
    (T : TaskDecomposition.Task K F) (hT : Indecomposable T.spaces ⊤)
    (hD : ReflectionReduction.defect T.dimensionVector=0) (i : Fin 3) :
    Module.finrank K ((quotientTask T).U i)-Module.finrank K ((quotientTask T).A i)=
      Module.finrank K (T.U i)-Module.finrank K (T.A i) := by
  have hu := quotient_image_finrank (T.U i) (tripodPlane K T)
  have ha := quotient_image_finrank (T.A i) (tripodPlane K T)
  rw [regular_tripod_intersection T hT hD i] at hu
  change Module.finrank K ((T.U i).map (tripodPlane K T).mkQ)-
      Module.finrank K ((T.A i).map (tripodPlane K T).mkQ)=_
  omega

end UploadBroadcast.TripodQuotient
