import UploadBroadcast.ExtensionGenerated
import UploadBroadcast.TaskQuiverBridge

/-! Cross-intersection vanishing is preserved by actual extensions. -/
namespace UploadBroadcast.QuiverRepresentation
variable {K : Type} [Field K]

/-- The inner arrows with their canonical vertex types exposed. -/
def inwardInner (R : Rep K inwardE6) (i : Fin 3) :
    R.space (.middle i) →ₗ[K] R.space .center := R.arrow (.inner i)

/-- The outer arrows with their canonical vertex types exposed. -/
def inwardOuter (R : Rep K inwardE6) (i : Fin 3) :
    R.space (.outer i) →ₗ[K] R.space (.middle i) := R.arrow (.outer i)

def inwardInnerCoupling (R S : Rep K inwardE6) (z : ArrowMaps S R) (i : Fin 3) :
    S.space (.middle i) →ₗ[K] R.space .center := z (.inner i)

def inwardOuterCoupling (R S : Rep K inwardE6) (z : ArrowMaps S R) (i : Fin 3) :
    S.space (.outer i) →ₗ[K] R.space (.middle i) := z (.outer i)

/-- The difference of the two inward paths from the indicated middle and
outer vertices to the center. For an actual task its kernel is Ui∩Aj. -/
def crossMap (R : Rep K inwardE6) (i j : Fin 3) :
    (R.space (.middle i) × R.space (.outer j)) →ₗ[K] R.space .center :=
  (inwardInner R i).comp (LinearMap.fst K _ _)-
    (inwardInner R j).comp ((inwardOuter R j).comp (LinearMap.snd K _ _))

/-- Naturality of the two-path difference under an actual quiver morphism. -/
theorem crossMap_comm {R S : Rep K inwardE6} (f : Hom R S) (i j : Fin 3)
    (x : R.space (.middle i) × R.space (.outer j)) :
    f.map .center (crossMap R i j x)=
      crossMap S i j (f.map (.middle i) x.1,f.map (.outer j) x.2) := by
  have h₁ := f.comm_apply (.inner i) x.1
  have h₂ := f.comm_apply (.inner j) (R.arrow (.outer j) x.2)
  have h₃ := f.comm_apply (.outer j) x.2
  change f.map .center (inwardInner R i x.1)=inwardInner S i (f.map (.middle i) x.1) at h₁
  change f.map .center (inwardInner R j (inwardOuter R j x.2))=
    inwardInner S j (f.map (.middle j) (inwardOuter R j x.2)) at h₂
  change f.map (.middle j) (inwardOuter R j x.2)=inwardOuter S j (f.map (.outer j) x.2) at h₃
  change f.map .center (inwardInner R i x.1-inwardInner R j (inwardOuter R j x.2))=
    inwardInner S i (f.map (.middle i) x.1)-inwardInner S j (inwardOuter S j (f.map (.outer j) x.2))
  rw [map_sub,h₁,h₂,h₃]

/-- Injectivity of this natural path map survives actual isomorphisms. -/
theorem crossMap_injective_iso {R S : Rep K inwardE6} (e : Iso R S)
    (i j : Fin 3) (hR : Function.Injective (crossMap R i j)) :
    Function.Injective (crossMap S i j) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  have he := crossMap_comm e.symm.toHom i j x
  have hx0 : crossMap S i j x=0 := hx
  rw [hx0,map_zero] at he
  have hpre : ((e.map (.middle i)).symm x.1,(e.map (.outer j)).symm x.2)=0 := by
    apply hR
    exact he.symm.trans (map_zero _).symm
  have h₁ := congrArg (fun y => e.map (.middle i) y.1) hpre
  have h₂ := congrArg (fun y => e.map (.outer j) y.2) hpre
  change x=0
  exact Prod.ext (by simpa using h₁) (by simpa using h₂)

/-- Injectivity of the cross-path map is extension-closed. The proof first
kills the quotient coordinates, then the subobject coordinates. -/
theorem crossMap_injective_extension (R S : Rep K inwardE6) (z : ArrowMaps S R)
    (i j : Fin 3) (hR : Function.Injective (crossMap R i j))
    (hS : Function.Injective (crossMap S i j)) :
    Function.Injective (crossMap (extension R S z) i j) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  have h₂ := congrArg Prod.snd hx
  change crossMap S i j (x.1.2,x.2.2)=0 at h₂
  have hs : (x.1.2,x.2.2)=(0,0) := by
    apply hS
    change crossMap S i j (x.1.2,x.2.2)=crossMap S i j 0
    rw [map_zero]
    exact h₂
  have hsi : x.1.2=0 := congrArg Prod.fst hs
  have hsj : x.2.2=0 := congrArg Prod.snd hs
  have h₁ := congrArg Prod.fst hx
  change (inwardInner R i x.1.1+inwardInnerCoupling R S z i x.1.2)-
    (inwardInner R j (inwardOuter R j x.2.1+inwardOuterCoupling R S z j x.2.2)+
      inwardInnerCoupling R S z j (inwardOuter S j x.2.2))=0 at h₁
  simp only [hsi,hsj,map_zero,add_zero] at h₁
  have hr : (x.1.1,x.2.1)=(0,0) := by
    apply hR
    change crossMap R i j (x.1.1,x.2.1)=crossMap R i j 0
    rw [map_zero]
    exact h₁
  have hri : x.1.1=0 := congrArg (fun p : R.space (.middle i) × R.space (.outer j) => p.1) hr
  have hrj : x.2.1=0 := congrArg (fun p : R.space (.middle i) × R.space (.outer j) => p.2) hr
  change x=0
  exact Prod.ext (Prod.ext hri hsi) (Prod.ext hrj hsj)

/-- All distinct-arm cross-path maps are injective. -/
def CrossTransverse (R : Rep K inwardE6) : Prop :=
  ∀ i j : Fin 3, i≠j → Function.Injective (crossMap R i j)

/-- A zero representation satisfies every cross-injectivity condition. -/
theorem crossTransverse_zero (R : Rep K inwardE6) (hR : IsZero R) : CrossTransverse R := by
  intro i j _ x y _
  exact Prod.ext ((hR _ _).trans (hR _ _).symm) ((hR _ _).trans (hR _ _).symm)

theorem CrossTransverse.iso {R S : Rep K inwardE6} (hR : CrossTransverse R)
    (e : Iso R S) : CrossTransverse S := fun i j h => crossMap_injective_iso e i j (hR i j h)

theorem CrossTransverse.extension {R S : Rep K inwardE6} (hR : CrossTransverse R)
    (hS : CrossTransverse S) (z : ArrowMaps S R) : CrossTransverse (extension R S z) :=
  fun i j h => crossMap_injective_extension R S z i j (hR i j h) (hS i j h)

/-- Cross-transversality of every atom propagates through the entire actual
finite extension closure. -/
theorem ExtensionGenerated.crossTransverse {C : Rep K inwardE6 → Prop}
    (hC : ∀ R, C R → CrossTransverse R) {R : Rep K inwardE6}
    (hR : ExtensionGenerated C R) : CrossTransverse R := by
  induction hR with
  | zero R hz => exact crossTransverse_zero R hz
  | atom R hc => exact hC R hc
  | extension R S z _ _ ihR ihS => exact ihR.extension ihS z
  | iso e _ ih => exact ih.iso e
end UploadBroadcast.QuiverRepresentation

namespace UploadBroadcast.TaskDecomposition
open QuiverRepresentation
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

/-- For the actual nested subspace task, the quiver's natural cross-path
injectivity is exactly the requested cross-intersection vanishing. -/
theorem Task.crossMap_injective_iff (T : Task K V) (i j : Fin 3) :
    Function.Injective (crossMap T.toRep i j) ↔ Disjoint (T.U i) (T.A j) := by
  constructor
  · intro hi
    apply Submodule.disjoint_def.mpr
    intro x hU hA
    have hh : crossMap T.toRep i j (⟨x,hU⟩,⟨x,hA⟩)=crossMap T.toRep i j 0 := by
      change x-x=0-0
      simp
    have he := congrArg (fun p : T.U i × T.A j => p.1.val) (hi hh)
    exact he
  · intro hd
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    have he : x.1.val=x.2.val := sub_eq_zero.mp hx
    have hz : x.1.val=0 := Submodule.disjoint_def.mp hd _ x.1.property (he ▸ x.2.property)
    change x=0
    exact Prod.ext (Subtype.ext hz) (Subtype.ext (he.symm.trans hz))

/-- Actual cross-intersections vanish for a task generated by cross-transverse
atoms, with no additional dimension or root-shape assumption. -/
theorem Task.cross_intersections_of_generated (T : Task K V)
    {C : Rep K inwardE6 → Prop} (hC : ∀ R, C R → CrossTransverse R)
    (hT : ExtensionGenerated C T.toRep) :
    ∀ i j : Fin 3, i≠j → T.U i ⊓ T.A j=⊥ := by
  intro i j hij
  exact ((T.crossMap_injective_iff i j).mp (hT.crossTransverse hC i j hij)).eq_bot

end UploadBroadcast.TaskDecomposition
