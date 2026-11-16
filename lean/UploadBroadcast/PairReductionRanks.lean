import UploadBroadcast.FullResidualAssembly

/-!
# Exact original-task ranks of the surviving active pair spaces

The kernel reduction retains exactly each selected active pair factor.
Normalization preserves the defining intersections and hence their ranks.
-/
namespace UploadBroadcast.Task
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

namespace ActivePairSelection
variable {T : Task K F} (s : T.ActivePairSelection)

theorem pairReducedTask_side (i : Three) :
    s.pairReducedTask.A i =
      (T.A i).comap (LinearMap.ker s.totalPassiveProjection).subtype := by
  ext x
  constructor
  · exact s.pairReduced_side_include i x
  · intro hx
    change x ∈ ((T.A i).map s.simultaneous.toLinearMap).map _
    rw [s.simultaneous_side]
    refine ⟨x,hx,?_⟩
    apply Subtype.ext
    change (x : F) - s.totalPassiveProjection x = x
    rw [show s.totalPassiveProjection x = 0 from x.property,sub_zero]

theorem pairReducedTask_pairKnown (i : Three) :
    s.pairReducedTask.pairKnown i =
      (T.pairKnown i).comap (LinearMap.ker s.totalPassiveProjection).subtype := by
  simp only [Task.pairKnown, s.pairReducedTask_side, Submodule.comap_iInf]

theorem pairReduced_mem_activeFactor (i : Three)
    (x : s.pairReducedTask.pairKnown i) :
    (⟨((x : LinearMap.ker s.totalPassiveProjection) : F), by
      exact (s.pairReducedTask_pairKnown i).le x.property⟩ : T.pairKnown i) ∈ s.activeFactor i := by
  classical
  let b : T.pairKnown i := ⟨((x : LinearMap.ker s.totalPassiveProjection) : F), by
    exact (s.pairReducedTask_pairKnown i).le x.property⟩
  change b ∈ s.activeFactor i
  have htotal : s.totalPassiveProjection b = 0 := x.val.property
  have hpi : s.passiveProjection i b = 0 := by
    have he : s.totalPassiveProjection b = s.passiveProjection i b := by
      simp only [totalPassiveProjection, LinearMap.sum_apply]
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact s.passiveProjection_own j b (T.pairKnown_le i j hji b.property)
      · simp
    exact he.symm.trans htotal
  have hproj : (s.passive i).linearProjOfIsCompl (s.activeFactor i)
      (s.complementary i) b = 0 := by
    rw [s.passiveProjection_apply, ← s.chart_pair i b,
      LinearEquiv.symm_apply_apply] at hpi
    have he := (s.chart i).injective (hpi.trans (s.chart i).map_zero.symm)
    exact Subtype.ext (congrArg Prod.fst he)
  exact (Submodule.linearProjOfIsCompl_apply_eq_zero_iff (s.complementary i)).mp hproj

theorem totalPassiveProjection_activeFactor (i : Three) (b : s.activeFactor i) :
    s.totalPassiveProjection (b : T.pairKnown i) = 0 := by
  classical
  simp only [totalPassiveProjection, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hji : j = i
  · subst j
    rw [s.passiveProjection_apply, ← s.chart_pair i (b : T.pairKnown i),
      LinearEquiv.symm_apply_apply,
      (Submodule.linearProjOfIsCompl_apply_eq_zero_iff (s.complementary i)).mpr b.property]
    exact (s.chart i).map_zero
  · exact s.passiveProjection_own j (b : T.pairKnown i)
      (T.pairKnown_le i j hji b.val.property)

/-- The surviving pair-known space is the actual selected active factor,
with the same ambient vectors on both sides. -/
noncomputable def pairReducedPairEquivActive (i : Three) :
    s.pairReducedTask.pairKnown i ≃ₗ[K] s.activeFactor i where
  toFun x := ⟨⟨x,by
    exact (s.pairReducedTask_pairKnown i).le x.property⟩,s.pairReduced_mem_activeFactor i x⟩
  invFun b := ⟨⟨b,s.totalPassiveProjection_activeFactor i b⟩,by
    rw [s.pairReducedTask_pairKnown]
    exact b.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The exact dimension of each pair block after passive deletion. -/
theorem pairReduced_pairKnown_finrank [FiniteDimensional K F] (i : Three) :
    Module.finrank K (s.pairReducedTask.pairKnown i) =
      Module.finrank K (s.activeFactor i) :=
  (s.pairReducedPairEquivActive i).finrank_eq

end ActivePairSelection

theorem pairReduction_pairKnown_finrank [FiniteDimensional K F]
    (T : Task K F) (i : Three) :
    Module.finrank K (T.pairReduction.pairKnown i) = T.intrinsicActivePairRank i :=
  (T.selectedPairs.pairReduced_pairKnown_finrank i).trans
    (T.selectedPairs_activeFactor_finrank i)

theorem normalized_side (T : Task K F) (i : Three) :
    T.normalized.A i = (T.A i).comap (⨆ j, T.A j).subtype := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change ((ResidualTaskAssembly.retainedProjection (⨆ j, T.A j) y :
      ↥(⨆ j, T.A j)) : F) ∈ T.A i
    have he := congrArg Subtype.val (ResidualTaskAssembly.retainedProjection_self
      (⨆ j, T.A j) ⟨y,(le_iSup T.A i) hy⟩)
    rwa [he]
  · intro hx
    exact ⟨x,hx,ResidualTaskAssembly.retainedProjection_self (⨆ j, T.A j) x⟩

theorem normalized_signal (T : Task K F) (i : Three) :
    T.normalized.U i = (T.U i).comap (⨆ j, T.A j).subtype := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change ((ResidualTaskAssembly.retainedProjection (⨆ j, T.A j) y :
      ↥(⨆ j, T.A j)) : F) ∈ T.U i
    have he := congrArg Subtype.val (ResidualTaskAssembly.retainedProjection_self
      (⨆ j, T.A j) ⟨y,T.feasible i hy⟩)
    rwa [he]
  · intro hx
    exact ⟨x,hx,ResidualTaskAssembly.retainedProjection_self (⨆ j, T.A j) x⟩

theorem normalized_pairKnown (T : Task K F) (i : Three) :
    T.normalized.pairKnown i = (T.pairKnown i).comap (⨆ j, T.A j).subtype := by
  simp only [pairKnown,T.normalized_side,Submodule.comap_iInf]

theorem normalized_commonKnown (T : Task K F) :
    T.normalized.commonKnown = T.commonKnown.comap (⨆ j, T.A j).subtype := by
  simp only [commonKnown,T.normalized_side,Submodule.comap_iInf]

/-- Normalizing the coefficient ambient space preserves every original
active-pair intersection rank. -/
theorem normalized_intrinsicActivePairRank [FiniteDimensional K F]
    (T : Task K F) (i : Three) :
    T.normalized.intrinsicActivePairRank i = T.intrinsicActivePairRank i := by
  unfold intrinsicActivePairRank
  rw [T.normalized_signal,T.normalized_pairKnown,T.normalized_commonKnown,
    ← Submodule.comap_inf]
  have ha : T.U i ⊓ T.pairKnown i ≤ ⨆ j, T.A j := inf_le_left.trans (T.feasible i)
  have hc : T.commonKnown ≤ ⨆ j, T.A j := (T.commonKnown_le 0).trans (le_iSup T.A 0)
  rw [(Submodule.comapSubtypeEquivOfLe ha).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe hc).finrank_eq]

/-- Source rank transport through both normalization and active-pair deletion. -/
theorem preResidual_pairKnown_finrank [FiniteDimensional K F]
    (T : Task K F) (i : Three) :
    Module.finrank K (T.preResidual.pairKnown i) = T.intrinsicActivePairRank i :=
  (T.normalized.pairReduction_pairKnown_finrank i).trans
    (T.normalized_intrinsicActivePairRank i)

end UploadBroadcast.Task
