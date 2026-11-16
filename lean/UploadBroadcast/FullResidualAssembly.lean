import UploadBroadcast.PairResidualAssembly
import UploadBroadcast.ResidualTaskAssembly

/-!
# Arbitrary-task extraction of pair omniscience and private/tripod coordinates

Ambient normalization, active-pair reduction, the actual pair omniscience
factor, and a canonical private/tripod chart are all selected from an arbitrary
feasible task. No normal form or rate-preservation certificate is an input.
-/
namespace UploadBroadcast
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F V W : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

namespace Task
/-- Remove coefficient directions outside the span of all side information. -/
noncomputable def normalized (T : Task K F) : Task K ↥(⨆ i, T.A i) :=
  T.imageTask (ResidualTaskAssembly.retainedProjection (⨆ i, T.A i))

noncomputable def normalizationRetraction (T : Task K F) : PassiveRetraction T T.normalized := by
  let S : Submodule K F := ⨆ i, T.A i
  let p := ResidualTaskAssembly.retainedProjection S
  let e := S.subtype
  have hp (x : S) : p x = x := ResidualTaskAssembly.retainedProjection_self S x
  have hpe : p.comp e = LinearMap.id := by
    apply LinearMap.ext
    exact hp
  have he (x : F) (hx : x ∈ S) : e (p x) = x := congrArg Subtype.val (hp ⟨x,hx⟩)
  exact passiveRetractionOfProjection T T.normalized p e hpe
    (fun i x hx => ⟨x,hx,rfl⟩)
    (by intro i x hx; obtain ⟨y,hy,rfl⟩ := hx; rwa [he y ((le_iSup T.A i) hy)])
    (fun i x hx => ⟨x,hx,rfl⟩)
    (by intro i x hx; obtain ⟨y,hy,rfl⟩ := hx; rwa [he y (T.feasible i hy)])
    (by intro i x hx; rw [he x (T.feasible i hx),sub_self]; exact (T.A i).zero_mem)

theorem normalized_spanning (T : Task K F) : T.normalized.Spanning := by
  change (⨆ i, (T.A i).map (ResidualTaskAssembly.retainedProjection (⨆ j, T.A j))) = ⊤
  rw [← Submodule.map_iSup]
  exact ResidualTaskAssembly.map_retainedProjection_top _

theorem normalized_achievableAt_eq [Finite K] [FiniteDimensional K F] (T : Task K F) (n : ℕ) :
    T.achievableAt n = T.normalized.achievableAt n := (T.normalizationRetraction).achievableAt_eq n

theorem imageTask_spanning (T : Task K F) (f : F →ₗ[K] V)
    (hT : T.Spanning) (hf : Function.Surjective f) : (T.imageTask f).Spanning := by
  change (⨆ i, (T.A i).map f) = ⊤
  rw [← Submodule.map_iSup,hT,Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hf

theorem complementaryProjection_surjective (P : F →ₗ[K] F) (hP : P.comp P = P) :
    Function.Surjective (complementaryProjection P hP) := by
  intro x
  refine ⟨x,?_⟩
  apply Subtype.ext
  change (x : F) - P x = x
  rw [show P x = 0 from x.property,sub_zero]

theorem pairReduction_spanning (T : Task K F) (hT : T.Spanning) : T.pairReduction.Spanning := by
  have hq : (T.quotientTask T.commonKnown).Spanning :=
    T.imageTask_spanning T.commonKnown.mkQ hT T.commonKnown.mkQ_surjective
  have hs : (Profile.mapTask T.selectedPairs.simultaneous (T.quotientTask T.commonKnown)).Spanning :=
    (T.quotientTask T.commonKnown).imageTask_spanning T.selectedPairs.simultaneous.toLinearMap hq
      T.selectedPairs.simultaneous.surjective
  exact (Profile.mapTask T.selectedPairs.simultaneous (T.quotientTask T.commonKnown)).imageTask_spanning
    (complementaryProjection T.selectedPairs.totalPassiveProjection T.selectedPairs.totalPassiveProjection_idempotent)
    hs (complementaryProjection_surjective _ _)

/-- The actual normalized active-pair task, selected from the original task. -/
noncomputable def preResidual (T : Task K F) := T.normalized.pairReduction

noncomputable def residualPairSelection (T : Task K F) : T.preResidual.ActivePairSelection :=
  Classical.choice (T.preResidual.exists_activePairSelection_of_commonKnown_eq_bot
    T.normalized.pairReduction_commonKnown_eq_bot)

noncomputable def pairOmniscienceFactor (T : Task K F) := T.residualPairSelection.pairOmniscienceTask
noncomputable def pairFreeResidual (T : Task K F) := T.residualPairSelection.pairResidualTask

/-- Every surviving pair coefficient belongs to every signal, and the
extracted pair factor is therefore genuinely an omniscience task. -/
theorem pairOmniscienceFactor_signal (T : Task K F) (i : Three) :
    T.pairOmniscienceFactor.U i = ⊤ :=
  T.residualPairSelection.pairOmniscienceTask_signal T.normalized.pairReduction_pairKnown_le i

theorem pairFreeResidual_disjoint (T : Task K F) :
    Disjoint (T.pairFreeResidual.A 0) (T.pairFreeResidual.A 1) ∧
    Disjoint (T.pairFreeResidual.A 0) (T.pairFreeResidual.A 2) ∧
    Disjoint (T.pairFreeResidual.A 1) (T.pairFreeResidual.A 2) :=
  T.residualPairSelection.pairResidualTask_disjoint

theorem pairFreeResidual_spanning (T : Task K F) : T.pairFreeResidual.Spanning :=
  T.residualPairSelection.pairResidualTask_spanning
    (T.normalized.pairReduction_spanning T.normalized_spanning)

/-- End-to-end pair factorization for an arbitrary feasible task. Normal form,
projection data and operational equality are conclusions of the construction. -/
theorem pair_factorization_achievableAt_eq [Finite K] [FiniteDimensional K F]
    (T : Task K F) (n : ℕ) :
    T.achievableAt n = (Profile.directSum T.pairOmniscienceFactor T.pairFreeResidual).achievableAt n :=
  (T.normalized_achievableAt_eq n).trans ((T.normalized.pairReduction_achievableAt_eq n).trans
    (T.residualPairSelection.pairResidual_achievableAt_eq T.normalized.pairReduction_pairKnown_le n))

theorem pair_factorization_costRegion_eq [Finite K] [FiniteDimensional K F] (T : Task K F) :
    T.costRegion = (Profile.directSum T.pairOmniscienceFactor T.pairFreeResidual).costRegion := by
  unfold costRegion
  simp_rw [T.pair_factorization_achievableAt_eq]

/-- Actual canonical private/tripod chart of a pair-free task. -/
structure PrivateTripodChart (T : Task K F) where
  P₁ : Submodule K (T.A 0)
  P₂ : Submodule K (T.A 1)
  P₃ : Submodule K F
  chart : ResidualUpload.Ambient P₁ P₂ P₃ ↥(T.A 2 ⊓ (T.A 0 ⊔ T.A 1)) ≃ₗ[K] F
  side₁ : (ResidualUpload.A₁ K P₁ P₂ P₃ ↥(T.A 2 ⊓ (T.A 0 ⊔ T.A 1))).map chart.toLinearMap = T.A 0
  side₂ : (ResidualUpload.A₂ K P₁ P₂ P₃ ↥(T.A 2 ⊓ (T.A 0 ⊔ T.A 1))).map chart.toLinearMap = T.A 1
  side₃ : (ResidualUpload.A₃ K P₁ P₂ P₃ ↥(T.A 2 ⊓ (T.A 0 ⊔ T.A 1))).map chart.toLinearMap = T.A 2

theorem exists_pairFreeResidual_chart (T : Task K F) : Nonempty T.pairFreeResidual.PrivateTripodChart := by
  obtain ⟨h₁,h₂,h₃⟩ := T.pairFreeResidual_disjoint
  have hs : T.pairFreeResidual.A 0 ⊔ T.pairFreeResidual.A 1 ⊔ T.pairFreeResidual.A 2 = ⊤ := by
    simpa only [Spanning,Profile.three_iSup] using T.pairFreeResidual_spanning
  obtain ⟨P₁,P₂,P₃,e,he₁,he₂,he₃⟩ :=
    ResidualTaskAssembly.exists_canonical_chart _ _ _ h₁ h₂ h₃ hs
  exact ⟨⟨P₁,P₂,P₃,e,he₁,he₂,he₃⟩⟩

noncomputable def pairFreeChart (T : Task K F) : T.pairFreeResidual.PrivateTripodChart :=
  Classical.choice T.exists_pairFreeResidual_chart

/-- Mapping back an exact subspace chart gives the original canonical space. -/
theorem map_back_chart (e : V ≃ₗ[K] F) (A : Submodule K V) (B : Submodule K F)
    (h : A.map e.toLinearMap = B) : B.map e.symm.toLinearMap = A := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    rw [← h] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    change e.symm (e z) ∈ A
    simpa only [LinearEquiv.symm_apply_apply] using hz
  · intro hx
    exact ⟨e x,by rw [← h]; exact ⟨x,hx,rfl⟩,e.symm_apply_apply x⟩

namespace PrivateTripodChart
variable {T : Task K F} (c : T.PrivateTripodChart)
noncomputable def toTask := Profile.mapTask c.chart.symm T

theorem sides :
    c.toTask.A 0 = ResidualUpload.A₁ K c.P₁ c.P₂ c.P₃ ↥(T.A 2 ⊓ (T.A 0 ⊔ T.A 1)) ∧
    c.toTask.A 1 = ResidualUpload.A₂ K c.P₁ c.P₂ c.P₃ ↥(T.A 2 ⊓ (T.A 0 ⊔ T.A 1)) ∧
    c.toTask.A 2 = ResidualUpload.A₃ K c.P₁ c.P₂ c.P₃ ↥(T.A 2 ⊓ (T.A 0 ⊔ T.A 1)) :=
  ⟨map_back_chart _ _ _ c.side₁,map_back_chart _ _ _ c.side₂,map_back_chart _ _ _ c.side₃⟩
end PrivateTripodChart

noncomputable def canonicalPairFreeResidual (T : Task K F) := T.pairFreeChart.toTask

/-- The selected residual task has the exact canonical three side spaces. -/
theorem canonicalPairFreeResidual_sides (T : Task K F) : type_of% T.pairFreeChart.sides :=
  T.pairFreeChart.sides
end Task
end UploadBroadcast

namespace UploadBroadcast
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F V W : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

private theorem task_ext_spaces {T S : Task K F} (hA : T.A = S.A) (hU : T.U = S.U) : T = S := by
  cases T
  cases S
  cases hA
  cases hU
  rfl

/-- A coordinate change on the residual factor leaves the other factor fixed. -/
theorem map_product_right (A : Submodule K F) (B : Submodule K V) (e : V ≃ₗ[K] W) :
    (A.prod B).map ((LinearEquiv.refl K F).prodCongr e).toLinearMap =
      A.prod (B.map e.toLinearMap) := by
  ext x
  constructor
  · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
    exact ⟨ha,⟨b,hb,rfl⟩⟩
  · rintro ⟨ha,⟨b,hb,he⟩⟩
    exact ⟨(x.1,b),⟨ha,hb⟩,Prod.ext rfl he⟩

theorem mapTask_directSum_right (T : Task K F) (S : Task K V) (e : V ≃ₗ[K] W) :
    Profile.mapTask ((LinearEquiv.refl K F).prodCongr e) (Profile.directSum T S) =
      Profile.directSum T (Profile.mapTask e S) := by
  apply task_ext_spaces
  · funext i
    exact map_product_right (T.A i) (S.A i) e
  · funext i
    exact map_product_right (T.U i) (S.U i) e

namespace Task.PrivateTripodChart
variable {S : Task K V} (c : S.PrivateTripodChart)
theorem rightCoordinate_achievableAt_eq [Finite K] [FiniteDimensional K F]
    [FiniteDimensional K V] (T : Task K F) (n : ℕ) :
    (Profile.directSum T S).achievableAt n = (Profile.directSum T c.toTask).achievableAt n := by
  have h := (Profile.directSum T S).coordinate_achievableAt_eq
    ((LinearEquiv.refl K F).prodCongr c.chart.symm) n
  rw [mapTask_directSum_right] at h
  exact h
end Task.PrivateTripodChart

namespace Task
/-- Every feasible task has an actual pair omniscience factor and an actual
private/tripod task, with exactly the same nonlinear region at each blocklength.
All chart, complement, correction and deletion choices are constructed. -/
theorem pair_canonical_factorization_achievableAt_eq [Finite K] [FiniteDimensional K F]
    (T : Task K F) (n : ℕ) : type_of%
      ((T.pair_factorization_achievableAt_eq n).trans
        (T.pairFreeChart.rightCoordinate_achievableAt_eq T.pairOmniscienceFactor n)) :=
  (T.pair_factorization_achievableAt_eq n).trans
    (T.pairFreeChart.rightCoordinate_achievableAt_eq T.pairOmniscienceFactor n)

theorem pair_canonical_factorization_costRegion_eq [Finite K] [FiniteDimensional K F]
    (T : Task K F) : type_of%
      (congrArg closure (Set.iUnion_congr fun n => T.pair_canonical_factorization_achievableAt_eq n)) :=
  congrArg closure (Set.iUnion_congr fun n => T.pair_canonical_factorization_achievableAt_eq n)
end Task
end UploadBroadcast
