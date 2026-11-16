import UploadBroadcast.PairResidualAssembly
import UploadBroadcast.CommonTripodAssembly
import UploadBroadcast.OmniscienceTaskCode

namespace UploadBroadcast.PairOmniscienceAdapter
set_option maxHeartbeats 2000000
variable {K F C : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup C] [Module K C]
variable {T : Task K F} (s : T.ActivePairSelection)

noncomputable def coordinate (i : Three) : F →ₗ[K] T.pairKnown i :=
  (s.wholePairProjection i).codRestrict (T.pairKnown i)
    (fun x => s.wholePairProjection_range i ⟨x,rfl⟩)

@[simp] theorem coordinate_self (i : Three) (x : T.pairKnown i) : coordinate s i x = x :=
  Subtype.ext (s.wholePairProjection_on_pair i x)

@[simp] theorem coordinate_other (i j : Three) (hij : i ≠ j) (x : T.pairKnown j) :
    coordinate s i x = 0 := Subtype.ext
      (s.wholePairProjection_own i x (T.pairKnown_le j i hij x.property))

noncomputable def pairEquiv : T.pairOmniscience ≃ₗ[K]
    (T.pairKnown 0 × T.pairKnown 1 × T.pairKnown 2) where
  toFun x := (coordinate s 0 x,coordinate s 1 x,coordinate s 2 x)
  invFun x := ⟨(x.1 : F) + x.2.1 + x.2.2,
    (T.pairOmniscience).add_mem
      ((T.pairOmniscience).add_mem ((le_iSup T.pairKnown 0) x.1.property)
        ((le_iSup T.pairKnown 1) x.2.1.property))
      ((le_iSup T.pairKnown 2) x.2.2.property)⟩
  left_inv x := by
    apply Subtype.ext
    have h := s.totalPairProjection_on_omniscience x
    simpa only [Task.ActivePairSelection.totalPairProjection,LinearMap.sum_apply,
      Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,add_assoc] using h
  right_inv x := by
    apply Prod.ext
    · simp only [map_add,coordinate_self,coordinate_other s 0 1 (by decide),coordinate_other s 0 2 (by decide),add_zero]
    · apply Prod.ext
      · simp only [map_add,coordinate_self,coordinate_other s 1 0 (by decide),coordinate_other s 1 2 (by decide),zero_add,add_zero]
      · simp only [map_add,coordinate_self,coordinate_other s 2 0 (by decide),coordinate_other s 2 1 (by decide),zero_add]
  map_add' x y := by simp only [Submodule.coe_add,map_add,Prod.fst_add,Prod.snd_add]; rfl
  map_smul' a x := by simp only [Submodule.coe_smul,map_smul,Prod.smul_fst,Prod.smul_snd]; rfl

theorem side_iff_coordinate_zero (i : Three) (x : T.pairOmniscience) :
    (x : F) ∈ T.A i ↔ coordinate s i x = 0 := by
  constructor
  · intro hx
    exact Subtype.ext (s.wholePairProjection_own i x hx)
  · intro hx
    have hi : s.wholePairProjection i x = 0 := congrArg Subtype.val hx
    rw [← s.totalPairProjection_on_omniscience x]
    simp only [Task.ActivePairSelection.totalPairProjection,LinearMap.sum_apply]
    apply (T.A i).sum_mem
    intro j _
    by_cases hji : j = i
    · subst j; rw [hi]; exact (T.A i).zero_mem
    · exact T.pairKnown_le j i (Ne.symm hji) (s.wholePairProjection_range j ⟨x,rfl⟩)

/-- Pair factors and the common tripod become the canonical omniscience
coefficient space, with the original missing-user labels retained. -/
noncomputable def combinedEquiv : (T.pairOmniscience × (C × C)) ≃ₗ[K]
    OmniscienceOperational.Space C (T.pairKnown 0) (T.pairKnown 1) (T.pairKnown 2) where
  toFun x := (x.2.1,x.2.2,(pairEquiv s x.1).1,(pairEquiv s x.1).2.1,(pairEquiv s x.1).2.2)
  invFun x := ((pairEquiv s).symm (x.2.2.1,x.2.2.2.1,x.2.2.2.2),(x.1,x.2.1))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp only [Submodule.coe_add,map_add,Prod.fst_add,Prod.snd_add]; rfl
  map_smul' a x := by simp only [Submodule.coe_smul,map_smul,Prod.smul_fst,Prod.smul_snd]; rfl

section SideMembership
open OmniscienceOperational ResidualUpload

lemma mem_omega_side₀ {X₁ X₂ X₃ : Type*}
    [AddCommGroup X₁] [Module K X₁] [AddCommGroup X₂] [Module K X₂]
    [AddCommGroup X₃] [Module K X₃] (x : Space C X₁ X₂ X₃) :
    x ∈ sides (K := K) 0 ↔ x.2.1 = 0 ∧ x.2.2.1 = 0 := by
  change (∃ a, coeff₁ a = x) ↔ _
  constructor
  · rintro ⟨⟨a,b,c⟩,rfl⟩; exact ⟨rfl,rfl⟩
  · rintro ⟨h₁,h₂⟩
    refine ⟨(x.1,x.2.2.2.1,x.2.2.2.2),?_⟩
    change (x.1,0,0,x.2.2.2.1,x.2.2.2.2) = x
    rw [← h₁,← h₂]

lemma mem_omega_side₁ {X₁ X₂ X₃ : Type*}
    [AddCommGroup X₁] [Module K X₁] [AddCommGroup X₂] [Module K X₂]
    [AddCommGroup X₃] [Module K X₃] (x : Space C X₁ X₂ X₃) :
    x ∈ sides (K := K) 1 ↔ x.1 = 0 ∧ x.2.2.2.1 = 0 := by
  change (∃ a, coeff₂ a = x) ↔ _
  constructor
  · rintro ⟨⟨a,b,c⟩,rfl⟩; exact ⟨rfl,rfl⟩
  · rintro ⟨h₁,h₂⟩
    refine ⟨(x.2.1,x.2.2.1,x.2.2.2.2),?_⟩
    change (0,x.2.1,x.2.2.1,0,x.2.2.2.2) = x
    rw [← h₁,← h₂]

lemma mem_omega_side₂ {X₁ X₂ X₃ : Type*}
    [AddCommGroup X₁] [Module K X₁] [AddCommGroup X₂] [Module K X₂]
    [AddCommGroup X₃] [Module K X₃] (x : Space C X₁ X₂ X₃) :
    x ∈ sides (K := K) 2 ↔ x.1+x.2.1 = 0 ∧ x.2.2.2.2 = 0 := by
  change (∃ a, coeff₃ a = x) ↔ _
  constructor
  · rintro ⟨⟨a,b,c⟩,rfl⟩; simp [coeff₃]
  · rintro ⟨h₁,h₂⟩
    refine ⟨(x.2.1,x.2.2.1,x.2.2.2.1),?_⟩
    change (-x.2.1,x.2.1,x.2.2.1,x.2.2.2.1,0) = x
    rw [← eq_neg_of_add_eq_zero_left h₁,← h₂]

lemma mem_v (x : C × C) : x ∈ LinearMap.range (vMap (K := K)) ↔ x.2=0 := by
  constructor
  · rintro ⟨a,rfl⟩; rfl
  · intro h; exact ⟨x.1,Prod.ext rfl h.symm⟩

lemma mem_r (x : C × C) : x ∈ LinearMap.range (rMap (K := K)) ↔ x.1=0 := by
  constructor
  · rintro ⟨a,rfl⟩; rfl
  · intro h; exact ⟨x.2,Prod.ext h.symm rfl⟩

lemma mem_diff (x : C × C) : x ∈ LinearMap.range (diffMap (K := K)) ↔ x.1+x.2=0 := by
  constructor
  · rintro ⟨a,rfl⟩; simp [diffMap,vMap,rMap]
  · intro h
    refine ⟨x.2,?_⟩
    simp only [diffMap,LinearMap.sub_apply,vMap,rMap,LinearMap.inl_apply,LinearMap.inr_apply,
      Prod.mk_sub_mk,zero_sub,sub_zero]
    exact Prod.ext (eq_neg_of_add_eq_zero_left h).symm rfl

/-- All three sides match under the original-field Ω coordinate equivalence. -/
theorem combined_side_membership (i : Three) (x : T.pairOmniscience × (C × C)) :
    x.1 ∈ s.pairOmniscienceTask.A i ∧
      x.2 ∈ ![LinearMap.range (vMap (K := K)),LinearMap.range rMap,LinearMap.range diffMap] i ↔
    combinedEquiv s x ∈ sides (K := K) i := by
  rw [s.pairOmniscienceTask_side i]
  change ((x.1 : F) ∈ T.A i ∧ _) ↔ _
  rw [side_iff_coordinate_zero s i x.1]
  fin_cases i
  · change (coordinate s 0 x.1=0 ∧ x.2∈LinearMap.range (vMap (K := K))) ↔
      combinedEquiv s x ∈ sides (K := K) 0
    rw [mem_omega_side₀ (K := K) (combinedEquiv s x),mem_v (K := K)]
    exact and_comm
  · change (coordinate s 1 x.1=0 ∧ x.2∈LinearMap.range (rMap (K := K))) ↔
      combinedEquiv s x ∈ sides (K := K) 1
    rw [mem_omega_side₁ (K := K) (combinedEquiv s x),mem_r (K := K)]
    exact and_comm
  · change (coordinate s 2 x.1=0 ∧ x.2∈LinearMap.range (diffMap (K := K))) ↔
      combinedEquiv s x ∈ sides (K := K) 2
    rw [mem_omega_side₂ (K := K) (combinedEquiv s x),mem_diff (K := K)]
    exact and_comm

private theorem task_ext {E : Type*} [AddCommGroup E] [Module K E]
    {T S : Task K E} (hA : T.A = S.A) (hU : T.U = S.U) : T=S := by
  cases T; cases S; cases hA; cases hU; rfl

/-- Exact task equality, so arbitrary jointly encoded codes and their actual
costs transport through the Ω adapter. -/
theorem mapTask_combined (hactive : ∀ i, T.pairKnown i ≤ T.U i)
    (O : Task K (C × C))
    (hA : ∀ i, O.A i = ![LinearMap.range (vMap (K := K)),LinearMap.range rMap,LinearMap.range diffMap] i)
    (hU : ∀ i, O.U i = ⊤) :
    Profile.mapTask (combinedEquiv s) (Profile.directSum s.pairOmniscienceTask O) =
      OmniscienceOperational.task (K := K) (V := C)
        (X₁ := T.pairKnown 0) (X₂ := T.pairKnown 1) (X₃ := T.pairKnown 2) := by
  apply task_ext
  · funext i
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      apply (combined_side_membership s i x).mp
      exact ⟨hx.1,by simpa only [hA] using hx.2⟩
    · intro hy
      have hx := (combined_side_membership s i ((combinedEquiv s).symm y)).mpr (by simpa using hy)
      exact ⟨(combinedEquiv s).symm y,⟨hx.1,by simpa only [hA] using hx.2⟩,
        (combinedEquiv s).apply_symm_apply y⟩
  · funext i
    change ((s.pairOmniscienceTask.U i).prod (O.U i)).map (combinedEquiv s).toLinearMap = ⊤
    rw [s.pairOmniscienceTask_signal hactive i,hU,Submodule.prod_top,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (combinedEquiv s).surjective

end SideMembership
end UploadBroadcast.PairOmniscienceAdapter
