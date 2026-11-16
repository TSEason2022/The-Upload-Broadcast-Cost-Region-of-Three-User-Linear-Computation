import UploadBroadcast.ResidualPrivateSplit
import UploadBroadcast.FullResidualAssembly
import UploadBroadcast.OperationalBounds

/-! A nonlinear upload converse from actual pair and triple signal spans.
The side-space chart is constructed, and the private-use conditions are
consequences of the signal joins. No upload-optimality hypothesis is used. -/
namespace UploadBroadcast.GeometricUploadConverse
open Module ResidualUpload ResidualTaskAssembly ResidualPrivateSplit
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

section Canonical
variable {P₁ P₂ P₃ D : Type*}
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]
  [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K D]

omit [Finite K] [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K D] in
/-- Pair spanning forces every private coordinate to occur in remote signals. -/
theorem fully_used_of_pair_spans (T : Task K (Ambient P₁ P₂ P₃ D))
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j = ⊤) :
    used₁ T = ⊤ ∧ used₂ T = ⊤ ∧ used₃ T = ⊤ := by
  have hs₁ : Function.Surjective (private₁ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D)) :=
    fun p => ⟨embed₁ (K := K) p,rfl⟩
  have hs₂ : Function.Surjective (private₂ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D)) :=
    fun p => ⟨embed₂ (K := K) p,rfl⟩
  have hs₃ : Function.Surjective (private₃ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D)) :=
    fun p => ⟨embed₃ (K := K) p,rfl⟩
  refine ⟨?_,?_,?_⟩
  · rw [used₁,←Submodule.map_sup,hp 1 2 (by decide),Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hs₁
  · rw [used₂,←Submodule.map_sup,hp 0 2 (by decide),Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hs₂
  · rw [used₃,←Submodule.map_sup,hp 0 1 (by decide),Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hs₃

/-- The Shannon converse on canonical coordinates, for arbitrary nonlinear
codes and every positive blocklength. -/
theorem canonical_code_lower {n : ℕ} {m : Three → ℕ} {s : ℕ}
    (T : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : T.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₁ : T.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : T.A 2 = A₃ K P₁ P₂ P₃ D)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j = ⊤)
    (hj : T.U 2 ⊔ (T.U 0 ⊓ T.U 1) = ⊤)
    (c : T.Code n (fun i => Fin (m i)) (Fin s)) (hn : 0 < n) :
    2 * (finrank K (Ambient P₁ P₂ P₃ D) : ℝ) -
      (finrank K (T.A 0) + finrank K (T.A 1) + finrank K (T.A 2)) ≤ c.uploadCost := by
  classical
  letI (i : Three) : MeasurableSpace (Fin (m i)) := ⊤
  letI (i : Three) : DiscreteMeasurableSpace (Fin (m i)) := ⟨fun _ => trivial⟩
  obtain ⟨hu₀,hu₁,hu₂⟩ := fully_used_of_pair_spans T hp
  let v : D →ₗ[K] Ambient P₁ P₂ P₃ D := tripod₁
  let r : D →ₗ[K] Ambient P₁ P₂ P₃ D := tripod₂
  let R : Three → Submodule K (Ambient P₁ P₂ P₃ D) :=
    ![LinearMap.range v,LinearMap.range r,LinearMap.range (r-v)]
  apply ResidualConverse.code_rank_lower_bound T c R
    (fully_used_splits T h₀ h₁ h₂ hu₀ hu₁ hu₂)
  · rw [h₀,h₁]; exact sides_disjoint₁₂
  · rw [h₀,h₂]; exact sides_disjoint₁₃
  · rw [h₁,h₂]; exact sides_disjoint₂₃
  · rintro _ ⟨d,rfl⟩
    exact Submodule.sub_mem _ (Submodule.mem_sup_right ⟨d,rfl⟩)
      (Submodule.mem_sup_left ⟨d,rfl⟩)
  · rintro _ ⟨d,rfl⟩
    have hh := Submodule.add_mem_sup
      (show v d ∈ LinearMap.range v from ⟨d,rfl⟩)
      (show (r-v) d ∈ LinearMap.range (r-v) from ⟨d,rfl⟩)
    have he : v d + (r d-v d) = r d := by abel
    simpa only [LinearMap.sub_apply,he] using hh
  · rw [hj]; exact le_top
  · rw [h₀,h₁,h₂]; exact sides_span
  · exact hn
end Canonical

/-- Actual pairwise-disjoint side spaces plus the signal spanning identities
imply the residual lower bound over the original coefficient space. -/
theorem code_lower {n : ℕ} {m : Three → ℕ} {s : ℕ}
    (T : Task K F)
    (h₀₁ : Disjoint (T.A 0) (T.A 1))
    (h₀₂ : Disjoint (T.A 0) (T.A 2))
    (h₁₂ : Disjoint (T.A 1) (T.A 2))
    (ha : T.A 0 ⊔ T.A 1 ⊔ T.A 2 = ⊤)
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j = ⊤)
    (hj : T.U 2 ⊔ (T.U 0 ⊓ T.U 1) = ⊤)
    (c : T.Code n (fun i => Fin (m i)) (Fin s)) (hn : 0 < n) :
    2 * (finrank K F : ℝ) -
      (finrank K (T.A 0) + finrank K (T.A 1) + finrank K (T.A 2)) ≤ c.uploadCost := by
  obtain ⟨P₁,P₂,P₃,e,he₀,he₁,he₂⟩ := exists_canonical_chart (T.A 0) (T.A 1) (T.A 2) h₀₁ h₀₂ h₁₂ ha
  let C : T.PrivateTripodChart := ⟨P₁,P₂,P₃,e,he₀,he₁,he₂⟩
  have hp' : ∀ i j, i ≠ j → C.toTask.U i ⊔ C.toTask.U j = ⊤ := by
    intro i j hij
    change (T.U i).map e.symm.toLinearMap ⊔ (T.U j).map e.symm.toLinearMap = ⊤
    rw [←Submodule.map_sup,hp i j hij,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.symm.surjective
  have hj' : C.toTask.U 2 ⊔ (C.toTask.U 0 ⊓ C.toTask.U 1) = ⊤ := by
    change (T.U 2).map e.symm.toLinearMap ⊔ ((T.U 0).map e.symm.toLinearMap ⊓ (T.U 1).map e.symm.toLinearMap) = ⊤
    rw [←Submodule.map_inf e.symm.toLinearMap e.symm.injective,←Submodule.map_sup,hj,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.symm.surjective
  have hmem := c.mem_achievableAt hn
  rw [(T.coordinateRetraction e.symm).achievableAt_eq n] at hmem
  obtain ⟨_,_,_,m',s',c',hu,_⟩ := hmem
  have hh := canonical_code_lower C.toTask C.sides.1 C.sides.2.1 C.sides.2.2 hp' hj' c' hn
  have hd : finrank K (Ambient P₁ P₂ P₃ ↥(T.A 2 ⊓ (T.A 0 ⊔ T.A 1))) = finrank K F := e.finrank_eq
  have hdA (i : Three) : finrank K (C.toTask.A i) = finrank K (T.A i) := e.symm.finrank_map_eq _
  rw [hd,hdA,hdA,hdA] at hh
  exact hh.trans hu

end UploadBroadcast.GeometricUploadConverse
