import UploadBroadcast.ThreeSubspaceNormalFormCore
import UploadBroadcast.ResidualRowCompletion

namespace UploadBroadcast.ZeroCommonRowNormalForm
open ResidualRowCompletion
universe u v
variable {K : Type v} {F : Type u} [Field K] [AddCommGroup F] [Module K F]

/-- Only the coordinate vanishings actually used by row completion are
required. The diamond factor may be zero; arbitrary mixed/empty rows remain. -/
structure Chart (A B C : Submodule K F) where
  Q : Submodule K F
  H₁ : Submodule K Q
  H₂ : Submodule K Q
  H₃ : Submodule K F
  equiv : Rows H₁ H₂ H₃ (⊥ : Submodule K F) ≃ₗ[K] F
  first : ∀ t, equiv t ∈ A → t.1 = 0 ∧ t.2.2.2.2 = 0
  second : ∀ t, equiv t ∈ B → t.2.1 = 0 ∧ t.2.2.2.1 = 0
  third : ∀ t, equiv t ∈ C → t.2.2.1 = 0

private def reorder (Q : Submodule K F) (H₁ H₂ : Submodule K Q) (H₃ : Submodule K F) :
    Rows H₁ H₂ H₃ (⊥ : Submodule K F) ≃ₗ[K] (H₃ × (H₂ × H₁)) where
  toFun t := (t.2.2.1,(t.2.1,t.1))
  invFun t := (t.2.2,t.2.1,t.1,0,0)
  left_inv t := by
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _)))
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every zero-common triple admits the exact simultaneous row-completion
coordinate conditions, without assuming a normal form or spanning. -/
theorem exists_chart (A B C : Submodule K F) (hABC : A ⊓ B ⊓ C = ⊥) :
    Nonempty (Chart A B C) := by
  classical
  obtain ⟨Q,hPQ,hCQ,_,_,_⟩ := three_subspace_pair_split A B C hABC
  let P := A ⊓ B
  let A' := A.comap Q.subtype
  let B' := B.comap Q.subtype
  have hAB : Disjoint A' B' :=
    disjoint_restrict_of_complement A B Q hPQ.disjoint
  obtain ⟨H,hAH,hBH⟩ := exists_complement_containing A' B' hAB
  let eQ : (A' × H) ≃ₗ[K] Q := Submodule.prodEquivOfIsCompl A' H hAH
  let e : Rows H A' P (⊥ : Submodule K F) ≃ₗ[K] F :=
    (reorder Q H A' P).trans
      (((LinearEquiv.refl K P).prodCongr eQ).trans
        (Submodule.prodEquivOfIsCompl P Q hPQ))
  have he (t : Rows H A' P (⊥ : Submodule K F)) :
      e t = (t.2.2.1 : F) + ((t.2.1 : Q) : F) + ((t.1 : Q) : F) := by
    change (t.2.2.1 : F) + (((t.2.1 : Q) + (t.1 : Q)) : F) = _
    abel
  refine ⟨⟨Q,H,A',P,e,?_,?_,?_⟩⟩
  · intro t ht
    refine ⟨?_,Subsingleton.elim _ _⟩
    have hp : (t.2.2.1 : F) ∈ A := t.2.2.1.property.1
    have ha : ((t.2.1 : Q) : F) ∈ A := t.2.1.property
    have hh : ((t.1 : Q) : F) ∈ A := by
      have hz := A.sub_mem ht (A.add_mem hp ha)
      rw [he] at hz
      simpa only [add_sub_cancel_left] using hz
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hAH.disjoint (t.1 : Q) hh t.1.property
  · intro t ht
    refine ⟨?_,Subsingleton.elim _ _⟩
    have hp : (t.2.2.1 : F) ∈ B := t.2.2.1.property.2
    have hq : (t.2.1 : Q) + (t.1 : Q) ∈ B' := by
      change (((t.2.1 : Q) + (t.1 : Q)) : F) ∈ B
      have hz := B.sub_mem ht hp
      rw [he] at hz
      simpa only [Submodule.coe_add,add_assoc,add_sub_cancel_left] using hz
    have hsum := hBH hq
    have hh : (t.2.1 : Q) ∈ H := by
      have hz := H.sub_mem hsum t.1.property
      simpa only [add_sub_cancel_right] using hz
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hAH.disjoint (t.2.1 : Q) t.2.1.property hh
  · intro t ht
    have hsum : ((t.2.1 : Q) : F) + ((t.1 : Q) : F) ∈ Q :=
      Q.add_mem (t.2.1 : Q).property (t.1 : Q).property
    have hp : (t.2.2.1 : F) ∈ Q := by
      have hz := Q.sub_mem (hCQ ht) hsum
      rw [he] at hz
      (convert hz using 1; abel)
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hPQ.disjoint (t.2.2.1 : F) t.2.2.1.property hp

end UploadBroadcast.ZeroCommonRowNormalForm
