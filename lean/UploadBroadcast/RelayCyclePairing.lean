import UploadBroadcast.ClassifiedRelayPartition
import UploadBroadcast.PhysicalCycleRelay
import UploadBroadcast.SplitTaskCoordinates
import UploadBroadcast.ResidualComponentFactors
import UploadBroadcast.RegularRelayOptimality

/-! Distinct resonant factors and disjoint physical cycle copies are selected
from finite cardinal and actual quotient-dimension bounds. No pairing or
already-repaired task decomposition is an input. -/
namespace UploadBroadcast.RelayCyclePairing
open Module Profile EdgeExtraction EdgeDeficits GlobalMenuAssembly
open PhysicalScalarCycleChart
variable {K R V : Type*} [Field K] [Fintype R]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
attribute [local instance] Classical.propDecidable

/-- Select genuinely distinct original resonant factors. -/
theorem exists_distinct_selection (r : ℕ) (hr : r ≤ Fintype.card R) :
    Nonempty (Fin r ↪ R) :=
  Function.Embedding.nonempty_of_card_le (by simpa using hr)

abbrev Remaining {r : ℕ} (s : Fin r ↪ R) := {i : R // i ∉ Set.range s}

/-- Each selected factor is removed exactly once. -/
theorem remaining_card {r : ℕ} (s : Fin r ↪ R) :
    Fintype.card (Remaining s)=Fintype.card R-r := by
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_range,Fintype.card_fin]

/-- Partition the original Jordan coordinates into the selected distinct
factors and their literal untouched complement. -/
noncomputable def selectionCoordinates (n : R → ℕ) {r : ℕ} (s : Fin r ↪ R) :
    ResonantFiniteAssembly.Ambient (K := K) n ≃ₗ[K]
      (ResonantFiniteAssembly.Ambient (K := K) (fun t => n (s t)) ×
        ResonantFiniteAssembly.Ambient (K := K) (fun i : Remaining s => n i.val)) :=
  (FiniteProductCoordinates.partitionEquiv (K := K)
    (F := fun i => ResonantEndomorphisms.Ambient K (JordanResonance.V K (n i)))
    (fun i => i ∈ Set.range s)).trans
    ((LinearEquiv.piCongrLeft' K
      (fun i : Set.range s => ResonantEndomorphisms.Ambient K (JordanResonance.V K (n i.val)))
      (Equiv.ofInjective s s.injective).symm).prodCongr (LinearEquiv.refl K _))

omit [Fintype R] in
/-- Selection changes the actual coefficient product, not only the
resonant cardinality or its scalar rank profile. -/
theorem map_selection (n : R → ℕ) {r : ℕ} (s : Fin r ↪ R) :
    mapTask (selectionCoordinates (K := K) n s) (ResonantFiniteAssembly.task n) =
      directSum (ResonantFiniteAssembly.task (fun t => n (s t)))
        (ResonantFiniteAssembly.task (fun i : Remaining s => n i.val)) := by
  rw [selectionCoordinates,← FiniteProductCoordinates.mapTask_trans,
    FiniteProductCoordinates.map_product_partition,
    FiniteProductCoordinates.map_directSum_congr,
    FiniteProductCoordinates.map_product_reindex]
  apply congrArg₂ directSum
  · rfl
  · apply FiniteProductCoordinates.task_eq_of_spaces <;> funext i <;>
      simp [mapTask,Submodule.map_id]

/-- Original-field geometric repair of every selected positive pair, with
one shared independent physical bundle and an actual split complement. -/
theorem exists_positive_pairing (n : R → ℕ) (T : Task K V) (r : ℕ)
    (hr : r ≤ Fintype.card R) (hc : r ≤ cycleMultiplicity T (Equiv.refl _)) :
    ∃ (s : Fin r ↪ R) (v : Three → Fin r → V) (Q : Submodule K V),
      LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2) ∧
      TaskDecomposition.Split (configuration T).spaces ⊤ Q
        (⨆ a, Submodule.span K (Set.range (v a))) ∧
      ∀ t : Fin r, ∃ hg : T.LocallyGenerated (Submodule.span K (Set.range (fun a => v a t))),
        RealizesMenu (directSum (ResonantRelay.jordanTask K (n (s t)))
          (NonzeroDefectRelays.inducedTask T (Submodule.span K (Set.range (fun a => v a t))) hg))
          (3*(n (s t)+1)+4)
          (fun (_ : Unit) => firstIncrement CycleFiniteAssembly.positiveIncrement) := by
  obtain ⟨s⟩ := exists_distinct_selection r hr
  obtain ⟨v,Q,hv,hb,hQ⟩ := exists_cycle_bundle T (Equiv.refl _) r hc
  refine ⟨s,v,Q,hv,hQ,?_⟩
  intro t
  obtain ⟨hi,h₀,h₁,h₂⟩ := bundle_copy_edges T (Equiv.refl _) v hv (fun a => (hb a).1) t
  have he : reindexTask (Equiv.refl Three) T=T := rfl
  rw [he] at h₀ h₁ h₂
  exact ⟨locally_generated T _ h₀ h₁ h₂,
    PhysicalCycleRelay.positive_physical_realizes T _ hi h₀ h₁ h₂ (n (s t))⟩

/-- The reversed physical cycle uses the same original user labels. -/
theorem exists_negative_pairing (n : R → ℕ) (T : Task K V) (r : ℕ)
    (hr : r ≤ Fintype.card R) (hc : r ≤ cycleMultiplicity T (Equiv.swap 0 1)) :
    ∃ (s : Fin r ↪ R) (v : Three → Fin r → V) (Q : Submodule K V),
      LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2) ∧
      TaskDecomposition.Split (configuration T).spaces ⊤ Q
        (⨆ a, Submodule.span K (Set.range (v a))) ∧
      ∀ t : Fin r, ∃ hg : T.LocallyGenerated
          (Submodule.span K (Set.range (fun a => v ((Equiv.swap 1 2) a) t))),
        RealizesMenu (directSum (ResonantRelay.jordanTask K (n (s t)))
          (NonzeroDefectRelays.inducedTask T
            (Submodule.span K (Set.range (fun a => v ((Equiv.swap 1 2) a) t))) hg))
          (3*(n (s t)+1)+4)
          (fun (_ : Unit) => firstIncrement CycleFiniteAssembly.negativeIncrement) := by
  obtain ⟨s⟩ := exists_distinct_selection r hr
  obtain ⟨v,Q,hv,hb,hQ⟩ := exists_cycle_bundle T (Equiv.swap 0 1) r hc
  refine ⟨s,v,Q,hv,hQ,?_⟩
  intro t
  obtain ⟨hi,h₀,h₁,h₂⟩ := bundle_copy_edges T (Equiv.swap 0 1) v hv (fun a => (hb a).1) t
  have hh₀ : EdgeBlock T 1 0 2 (line (fun a => v a t) 0) := by
    constructor
    · simpa [reindexTask] using h₀.source
    · simpa [reindexTask] using h₀.target
    · simpa [reindexTask] using h₀.third_zero
    · simpa [reindexTask] using h₀.target_side_zero
  have hh₁ : EdgeBlock T 0 2 1 (line (fun a => v a t) 1) := by
    constructor
    · simpa [reindexTask] using h₁.source
    · simpa [reindexTask] using h₁.target
    · simpa [reindexTask] using h₁.third_zero
    · simpa [reindexTask] using h₁.target_side_zero
  have hh₂ : EdgeBlock T 2 1 0 (line (fun a => v a t) 2) := by
    constructor
    · simpa [reindexTask] using h₂.source
    · simpa [reindexTask] using h₂.target
    · simpa [reindexTask] using h₂.third_zero
    · simpa [reindexTask] using h₂.target_side_zero
  let w : Three → V := fun a => v ((Equiv.swap 1 2) a) t
  have hw : LinearIndependent K w := hi.comp (Equiv.swap 1 2) (Equiv.swap 1 2).injective
  have hw₀ : EdgeBlock T 1 0 2 (line w 0) := by simpa [w] using hh₀
  have hw₁ : EdgeBlock T 2 1 0 (line w 1) := by simpa [w] using hh₂
  have hw₂ : EdgeBlock T 0 2 1 (line w 2) := by simpa [w] using hh₁
  exact ⟨reverse_locally_generated T w hw₀ hw₁ hw₂,
    PhysicalCycleRelay.negative_physical_realizes T w hw hw₀ hw₁ hw₂ (n (s t))⟩

section BundleCoordinates
open FiniteProductCoordinates CycleDirectSumCoordinates PhysicalCycleCoordinates
open scoped BigOperators
variable {r : ℕ}

/-- Independent scalar cycles retain their original physical source vectors. -/
noncomputable def bundleMap (v : Three → Fin r → V) : (Fin r → Three → K) →ₗ[K] V :=
  sumMaps (fun t => coefficients (K := K) (fun a => v a t))

abbrev bundleSpan (v : Three → Fin r → V) :=
  ⨆ a, Submodule.span K (Set.range (v a))

private def bundleReindex : (Fin r → Three → K) ≃ₗ[K] (((_a : Three) × Fin r) → K) where
  toFun x z := x z.2 z.1
  invFun x t a := x ⟨a,t⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional K V] in
private theorem bundleMap_eq (v : Three → Fin r → V) :
    bundleMap (K := K) v = (Fintype.linearCombination K
      (fun x : (_a : Three) × Fin r => v x.1 x.2)).comp bundleReindex.toLinearMap := by
  ext x
  simp only [bundleMap,sumMaps_apply,coefficients,Fintype.linearCombination_apply,
    LinearMap.comp_apply,LinearEquiv.coe_coe,bundleReindex,Fintype.sum_sigma]
  exact Finset.sum_comm

omit [Fintype R] [FiniteDimensional K V] in
theorem bundleMap_injective (v : Three → Fin r → V)
    (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2)) :
    Function.Injective (bundleMap (K := K) v) := by
  rw [bundleMap_eq]
  exact hv.fintypeLinearCombination_injective.comp bundleReindex.injective

omit [Fintype R] [FiniteDimensional K V] in
theorem bundleMap_range (v : Three → Fin r → V) :
    LinearMap.range (bundleMap (K := K) v)=bundleSpan (K := K) v := by
  rw [bundleMap_eq,LinearMap.range_comp_of_range_eq_top _ bundleReindex.range,
    Fintype.range_linearCombination,Set.range_sigma_eq_iUnion_range,Submodule.span_iUnion]

/-- A genuine linear equivalence onto the whole physically extracted bundle. -/
noncomputable def bundleEquiv (v : Three → Fin r → V)
    (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2)) :
    (Fin r → Three → K) ≃ₗ[K] bundleSpan (K := K) v :=
  (LinearEquiv.ofInjective (bundleMap v) (bundleMap_injective v hv)).trans
    (LinearEquiv.ofEq _ _ (bundleMap_range v))

omit [Fintype R] [FiniteDimensional K V] in
theorem subtype_bundleEquiv (v : Three → Fin r → V)
    (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2)) :
    (bundleSpan (K := K) v).subtype.comp (bundleEquiv v hv).toLinearMap=bundleMap v := rfl

omit [FiniteDimensional K V] in
private theorem iSup_copy_lines (v : Three → Fin r → V) (a : Three) :
    (⨆ t, line (K := K) (fun a => v a t) a)=Submodule.span K (Set.range (v a)) := by
  rw [Submodule.span_range_eq_iSup]

omit [Fintype R] [FiniteDimensional K V] in
/-- All six flags of the full scalar-cycle product map onto the actual
bundle's six intersections. -/
theorem positive_bundle_image (T : Task K V) (v : Three → Fin r → V)
    (h₀ : EdgeBlock T 0 1 2 (Submodule.span K (Set.range (v 0))))
    (h₁ : EdgeBlock T 1 2 0 (Submodule.span K (Set.range (v 1))))
    (h₂ : EdgeBlock T 2 0 1 (Submodule.span K (Set.range (v 2)))) :
    (∀ i, ((FiniteRelayAssembly.task (fun _ : Fin r => cycleTask K)).A i).map
      (bundleMap v)=T.A i ⊓ bundleSpan v) ∧
    (∀ i, ((FiniteRelayAssembly.task (fun _ : Fin r => cycleTask K)).U i).map
      (bundleMap v)=T.U i ⊓ bundleSpan v) := by
  obtain ⟨ha₀,ha₁,ha₂,hu₀,hu₁,hu₂⟩ := bundle_signature T _ _ _ h₀ h₁ h₂
  have hW : bundleSpan (K := K) v =
      Submodule.span K (Set.range (v 0)) ⊔ Submodule.span K (Set.range (v 1)) ⊔
        Submodule.span K (Set.range (v 2)) := three_iSup _
  constructor
  · intro i
    change (FiniteRelayAssembly.space (fun _ : Fin r => sides K i)).map _ = _
    rw [bundleMap,image_pi_sumMaps,hW]
    fin_cases i <;> dsimp only
    · change (⨆ t, (side₀ K).map (coefficients (fun a => v a t))) = _
      simp only [map_side₀]
      exact (iSup_copy_lines v 1).trans ha₀.symm
    · change (⨆ t, (side₁ K).map (coefficients (fun a => v a t))) = _
      simp only [map_side₁]
      exact (iSup_copy_lines v 2).trans ha₁.symm
    · change (⨆ t, (side₂ K).map (coefficients (fun a => v a t))) = _
      simp only [map_side₂]
      exact (iSup_copy_lines v 0).trans ha₂.symm
  · intro i
    change (FiniteRelayAssembly.space (fun _ : Fin r => signals K i)).map _ = _
    rw [bundleMap,image_pi_sumMaps,hW]
    fin_cases i <;> dsimp only
    · change (⨆ t, (signals K 0).map (coefficients (fun a => v a t))) = _
      simp only [signal₀_eq,Submodule.map_sup,map_side₀,map_side₁]
      rw [iSup_sup_eq,iSup_copy_lines,iSup_copy_lines]
      exact hu₀.symm
    · change (⨆ t, (signals K 1).map (coefficients (fun a => v a t))) = _
      simp only [signal₁_eq,Submodule.map_sup,map_side₁,map_side₂]
      rw [iSup_sup_eq,iSup_copy_lines,iSup_copy_lines,sup_comm]
      exact hu₁.symm
    · change (⨆ t, (signals K 2).map (coefficients (fun a => v a t))) = _
      simp only [signal₂_eq,Submodule.map_sup,map_side₂,map_side₀]
      rw [iSup_sup_eq,iSup_copy_lines,iSup_copy_lines]
      exact hu₂.symm

omit [Fintype R] [FiniteDimensional K V] in
/-- The scalar-cycle product is exactly the physical bundle factor in its
actual simultaneous split, not an assumed canonical cycle chart. -/
theorem positive_bundle_chart (T : Task K V) (v : Three → Fin r → V)
    (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2))
    (h₀ : EdgeBlock T 0 1 2 (Submodule.span K (Set.range (v 0))))
    (h₁ : EdgeBlock T 1 2 0 (Submodule.span K (Set.range (v 1))))
    (h₂ : EdgeBlock T 2 0 1 (Submodule.span K (Set.range (v 2))))
    (Q : Submodule K V) (hQ : TaskDecomposition.Split (configuration T).spaces ⊤ Q (bundleSpan v)) :
    mapTask (bundleEquiv v hv) (FiniteRelayAssembly.task (fun _ : Fin r => cycleTask K)) =
      SplitTaskCoordinates.rightTask T Q (bundleSpan v) hQ := by
  obtain ⟨hA,hU⟩ := positive_bundle_image T v h₀ h₁ h₂
  obtain ⟨_,_,hRA,hRU⟩ := SplitTaskCoordinates.factor_spaces T Q (bundleSpan v) hQ
  apply task_eq_of_spaces
  · funext i
    apply Submodule.map_injective_of_injective (bundleSpan (K := K) v).subtype_injective
    change (((FiniteRelayAssembly.task (fun _ : Fin r => cycleTask K)).A i).map _).map _ = _
    rw [← Submodule.map_comp,subtype_bundleEquiv,hRA,Submodule.map_comap_subtype,inf_comm]
    exact hA i
  · funext i
    apply Submodule.map_injective_of_injective (bundleSpan (K := K) v).subtype_injective
    change (((FiniteRelayAssembly.task (fun _ : Fin r => cycleTask K)).U i).map _).map _ = _
    rw [← Submodule.map_comp,subtype_bundleEquiv,hRU,Submodule.map_comap_subtype,inf_comm]
    exact hU i
omit [Fintype R] [FiniteDimensional K V] in
/-- All six flags of the full scalar-cycle product map onto the actual
bundle's six intersections. -/
theorem negative_bundle_image (T : Task K V) (v : Three → Fin r → V)
    (h₀ : EdgeBlock T 1 0 2 (Submodule.span K (Set.range (v 0))))
    (h₁ : EdgeBlock T 2 1 0 (Submodule.span K (Set.range (v 1))))
    (h₂ : EdgeBlock T 0 2 1 (Submodule.span K (Set.range (v 2)))) :
    (∀ i, ((FiniteRelayAssembly.task (fun _ : Fin r => reverseCycleTask K)).A i).map
      (bundleMap v)=T.A i ⊓ bundleSpan v) ∧
    (∀ i, ((FiniteRelayAssembly.task (fun _ : Fin r => reverseCycleTask K)).U i).map
      (bundleMap v)=T.U i ⊓ bundleSpan v) := by
  obtain ⟨ha₀,ha₁,ha₂,hu₀,hu₁,hu₂⟩ := reverse_bundle_signature T _ _ _ h₀ h₁ h₂
  have hW : bundleSpan (K := K) v =
      Submodule.span K (Set.range (v 0)) ⊔ Submodule.span K (Set.range (v 1)) ⊔
        Submodule.span K (Set.range (v 2)) := three_iSup _
  constructor
  · intro i
    change (FiniteRelayAssembly.space (fun _ : Fin r => sides K i)).map _ = _
    rw [bundleMap,image_pi_sumMaps,hW]
    fin_cases i <;> dsimp only
    · change (⨆ t, (side₀ K).map (coefficients (fun a => v a t))) = _
      simp only [map_side₀]
      exact (iSup_copy_lines v 1).trans ha₀.symm
    · change (⨆ t, (side₁ K).map (coefficients (fun a => v a t))) = _
      simp only [map_side₁]
      exact (iSup_copy_lines v 2).trans ha₁.symm
    · change (⨆ t, (side₂ K).map (coefficients (fun a => v a t))) = _
      simp only [map_side₂]
      exact (iSup_copy_lines v 0).trans ha₂.symm
  · intro i
    change (FiniteRelayAssembly.space (fun _ : Fin r => (![signals K 2,signals K 0,signals K 1] i))).map _ = _
    rw [bundleMap,image_pi_sumMaps,hW]
    fin_cases i <;> dsimp only
    · change (⨆ t, (signals K 2).map (coefficients (fun a => v a t))) = _
      simp only [signal₂_eq,Submodule.map_sup,map_side₂,map_side₀]
      rw [iSup_sup_eq,iSup_copy_lines,iSup_copy_lines]
      exact hu₀.symm
    · change (⨆ t, (signals K 0).map (coefficients (fun a => v a t))) = _
      simp only [signal₀_eq,Submodule.map_sup,map_side₀,map_side₁]
      rw [iSup_sup_eq,iSup_copy_lines,iSup_copy_lines]
      exact hu₁.symm
    · change (⨆ t, (signals K 1).map (coefficients (fun a => v a t))) = _
      simp only [signal₁_eq,Submodule.map_sup,map_side₁,map_side₂]
      rw [iSup_sup_eq,iSup_copy_lines,iSup_copy_lines,sup_comm]
      exact hu₂.symm

omit [Fintype R] [FiniteDimensional K V] in
/-- The scalar-cycle product is exactly the physical bundle factor in its
actual simultaneous split, not an assumed canonical cycle chart. -/
theorem negative_bundle_chart (T : Task K V) (v : Three → Fin r → V)
    (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2))
    (h₀ : EdgeBlock T 1 0 2 (Submodule.span K (Set.range (v 0))))
    (h₁ : EdgeBlock T 2 1 0 (Submodule.span K (Set.range (v 1))))
    (h₂ : EdgeBlock T 0 2 1 (Submodule.span K (Set.range (v 2))))
    (Q : Submodule K V) (hQ : TaskDecomposition.Split (configuration T).spaces ⊤ Q (bundleSpan v)) :
    mapTask (bundleEquiv v hv) (FiniteRelayAssembly.task (fun _ : Fin r => reverseCycleTask K)) =
      SplitTaskCoordinates.rightTask T Q (bundleSpan v) hQ := by
  obtain ⟨hA,hU⟩ := negative_bundle_image T v h₀ h₁ h₂
  obtain ⟨_,_,hRA,hRU⟩ := SplitTaskCoordinates.factor_spaces T Q (bundleSpan v) hQ
  apply task_eq_of_spaces
  · funext i
    apply Submodule.map_injective_of_injective (bundleSpan (K := K) v).subtype_injective
    change (((FiniteRelayAssembly.task (fun _ : Fin r => reverseCycleTask K)).A i).map _).map _ = _
    rw [← Submodule.map_comp,subtype_bundleEquiv,hRA,Submodule.map_comap_subtype,inf_comm]
    exact hA i
  · funext i
    apply Submodule.map_injective_of_injective (bundleSpan (K := K) v).subtype_injective
    change (((FiniteRelayAssembly.task (fun _ : Fin r => reverseCycleTask K)).U i).map _).map _ = _
    rw [← Submodule.map_comp,subtype_bundleEquiv,hRU,Submodule.map_comap_subtype,inf_comm]
    exact hU i

omit [Fintype R] in
private theorem mapTask_refl {X : Type*} [AddCommGroup X] [Module K X] (T : Task K X) :
    mapTask (LinearEquiv.refl K X) T=T := by
  apply task_eq_of_spaces <;> funext i <;> simp [mapTask,Submodule.map_id]

omit [Fintype R] in
private theorem mapTask_symm_of_eq {X Y : Type*}
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (T : Task K X) (S : Task K Y) (e : X ≃ₗ[K] Y) (he : mapTask e T=S) :
    mapTask e.symm S=T := by
  rw [← he]
  exact ResidualRelayAssembly.mapTask_inverse T e.symm

/-- Full original-source chart into the untouched source complement and the
finite product of physically extracted scalar cycles. -/
noncomputable def bundleSplitCoordinates (T : Task K V) (v : Three → Fin r → V)
    (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2))
    (Q : Submodule K V) (hQ : TaskDecomposition.Split (configuration T).spaces ⊤ Q (bundleSpan v)) :
    V ≃ₗ[K] (Q × (Fin r → Three → K)) :=
  (SplitTaskCoordinates.splitEquiv T Q (bundleSpan v) hQ).symm.trans
    ((LinearEquiv.refl K Q).prodCongr (bundleEquiv v hv).symm)

omit [Fintype R] [FiniteDimensional K V] in
theorem positive_bundle_split_chart (T : Task K V) (v : Three → Fin r → V)
    (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2))
    (h₀ : EdgeBlock T 0 1 2 (Submodule.span K (Set.range (v 0))))
    (h₁ : EdgeBlock T 1 2 0 (Submodule.span K (Set.range (v 1))))
    (h₂ : EdgeBlock T 2 0 1 (Submodule.span K (Set.range (v 2))))
    (Q : Submodule K V) (hQ : TaskDecomposition.Split (configuration T).spaces ⊤ Q (bundleSpan v)) :
    mapTask (bundleSplitCoordinates T v hv Q hQ) T =
      directSum (SplitTaskCoordinates.leftTask T Q (bundleSpan v) hQ)
        (FiniteRelayAssembly.task (fun _ : Fin r => cycleTask K)) := by
  rw [bundleSplitCoordinates,← mapTask_trans,
    mapTask_symm_of_eq _ _ _ (SplitTaskCoordinates.map_split T Q (bundleSpan v) hQ),
    map_directSum_congr,mapTask_refl]
  rw [mapTask_symm_of_eq _ _ _ (positive_bundle_chart T v hv h₀ h₁ h₂ Q hQ)]

omit [Fintype R] [FiniteDimensional K V] in
theorem negative_bundle_split_chart (T : Task K V) (v : Three → Fin r → V)
    (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2))
    (h₀ : EdgeBlock T 1 0 2 (Submodule.span K (Set.range (v 0))))
    (h₁ : EdgeBlock T 2 1 0 (Submodule.span K (Set.range (v 1))))
    (h₂ : EdgeBlock T 0 2 1 (Submodule.span K (Set.range (v 2))))
    (Q : Submodule K V) (hQ : TaskDecomposition.Split (configuration T).spaces ⊤ Q (bundleSpan v)) :
    mapTask (bundleSplitCoordinates T v hv Q hQ) T =
      directSum (SplitTaskCoordinates.leftTask T Q (bundleSpan v) hQ)
        (FiniteRelayAssembly.task (fun _ : Fin r => reverseCycleTask K)) := by
  rw [bundleSplitCoordinates,← mapTask_trans,
    mapTask_symm_of_eq _ _ _ (SplitTaskCoordinates.map_split T Q (bundleSpan v) hQ),
    map_directSum_congr,mapTask_refl]
  rw [mapTask_symm_of_eq _ _ _ (negative_bundle_chart T v hv h₀ h₁ h₂ Q hQ)]
end BundleCoordinates

section RepairCoordinates
open FiniteProductCoordinates
variable {W X : Type*} [AddCommGroup W] [Module K W]
  [AddCommGroup X] [Module K X] {r : ℕ}

/-- Literally pair each selected Jordan coefficient factor with its own
selected scalar cycle while retaining all other coordinates exactly. -/
noncomputable def repairCoordinates (n : R → ℕ) (s : Fin r ↪ R)
    (e : V ≃ₗ[K] (X × (Fin r → Three → K))) :
    (ResonantFiniteAssembly.Ambient (K := K) n × (W × V)) ≃ₗ[K]
      ((ResonantFiniteAssembly.Ambient (K := K) (fun i : Remaining s => n i.val) × W) ×
        ((∀ t : Fin r, ResonantEndomorphisms.Ambient K (JordanResonance.V K (n (s t))) ×
          (Three → K)) × X)) :=
  (((selectionCoordinates (K := K) n s).prodCongr ((LinearEquiv.refl K W).prodCongr e)).trans
    repairRegroupEquiv).trans
    ((LinearEquiv.refl K _).prodCongr (piProdEquiv.prodCongr (LinearEquiv.refl K X)))

omit [Fintype R] [FiniteDimensional K V] in
theorem map_repair_coordinates (n : R → ℕ) (s : Fin r ↪ R)
    (M : Task K W) (Z : Task K V) (B : Task K X) (C : Task K (Three → K))
    (e : V ≃ₗ[K] (X × (Fin r → Three → K)))
    (he : mapTask e Z=directSum B (FiniteRelayAssembly.task (fun _ : Fin r => C))) :
    mapTask (repairCoordinates n s e) (directSum (ResonantFiniteAssembly.task n) (directSum M Z)) =
      directSum (directSum (ResonantFiniteAssembly.task (fun i : Remaining s => n i.val)) M)
        (directSum (FiniteRelayAssembly.task
          (fun t : Fin r => directSum (ResonantRelay.jordanTask K (n (s t))) C)) B) := by
  simp only [repairCoordinates,← mapTask_trans,map_directSum_congr,map_selection,mapTask_refl,he,
    map_repair_regroup,map_product_exchange]

omit [Fintype R] in
/-- An actually split remainder of a zero-excess active residual is again
zero-excess and has a full-rank relay preserving every profile coordinate. -/
theorem zero_remainder_menu (Z : Task K V)
    (ha : ResidualComponentAdditivity.ActiveResidual Z)
    (hz : finrank K (Z.A 0)+finrank K (Z.A 1)+finrank K (Z.A 2)=finrank K V)
    (Q B : Submodule K V) (hs : TaskDecomposition.Split (configuration Z).spaces ⊤ Q B) :
    let S := SplitTaskCoordinates.leftTask Z Q B hs
    ResidualComponentAdditivity.ActiveResidual S ∧
      (finrank K (S.A 0)+finrank K (S.A 1)+finrank K (S.A 2)=finrank K Q) ∧
      RealizesMenu S (finrank K Q) (fun (_ : Unit) (_ : Profile.Index) => 0) := by
  let e := SplitTaskCoordinates.splitEquiv Z Q B hs
  let S := SplitTaskCoordinates.leftTask Z Q B hs
  let C := SplitTaskCoordinates.rightTask Z Q B hs
  have he : mapTask e.symm Z=directSum S C :=
    mapTask_symm_of_eq _ _ _ (SplitTaskCoordinates.map_split Z Q B hs)
  have hact : ResidualComponentAdditivity.ActiveResidual (directSum S C) := he ▸ ha.map e.symm
  have hzero : finrank K ((directSum S C).A 0)+finrank K ((directSum S C).A 1)+
      finrank K ((directSum S C).A 2)=finrank K (Q × B) := by
    rw [← he]
    simp only [mapTask,e.symm.finrank_map_eq]
    rw [e.finrank_eq]
    exact hz
  have hS := hact.directSum_left S C
  have hzS := (ResidualComponentAdditivity.zero_excess_directSum_factors S C hact hzero).1
  refine ⟨hS,hzS,?_⟩
  intro _
  refine ⟨⊤,ResidualComponentAdditivity.full_relay_local S hS,
    fun _ => by simp [Task.RelayFeasible],finrank_top K Q,?_⟩
  intro p
  simpa only [add_zero] using (ResidualComponentAdditivity.full_relay_profile S hS p).le

/-- Positive orientation: construct the selected factors, scalar cycles,
physical complement and the entire re-paired task chart from cardinal and
edge quotient bounds. -/
theorem exists_positive_repair_coordinates (n : R → ℕ) (M : Task K W) (Z : Task K V)
    (r : ℕ) (hr : r ≤ Fintype.card R) (hc : r ≤ cycleMultiplicity Z (Equiv.refl _)) :
    ∃ (s : Fin r ↪ R) (v : Three → Fin r → V) (Q : Submodule K V)
      (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2))
      (hQ : TaskDecomposition.Split (configuration Z).spaces ⊤ Q (bundleSpan v)),
      mapTask (repairCoordinates n s (bundleSplitCoordinates Z v hv Q hQ))
        (directSum (ResonantFiniteAssembly.task n) (directSum M Z)) =
        directSum (directSum (ResonantFiniteAssembly.task (fun i : Remaining s => n i.val)) M)
          (directSum (FiniteRelayAssembly.task (fun t : Fin r =>
            directSum (ResonantRelay.jordanTask K (n (s t))) (CycleDirectSumCoordinates.cycleTask K)))
            (SplitTaskCoordinates.leftTask Z Q (bundleSpan v) hQ)) ∧
      (∀ t : Fin r, RealizesMenu
        (directSum (ResonantRelay.jordanTask K (n (s t))) (CycleDirectSumCoordinates.cycleTask K))
        (3*(n (s t)+1)+4) (fun (_ : Unit) => firstIncrement CycleFiniteAssembly.positiveIncrement)) ∧
      Fintype.card (Remaining s)=Fintype.card R-r := by
  obtain ⟨s⟩ := exists_distinct_selection r hr
  obtain ⟨v,Q,hv,hb,hQ⟩ := exists_cycle_bundle Z (Equiv.refl _) r hc
  have h₀ : EdgeBlock Z 0 1 2 (Submodule.span K (Set.range (v 0))) := by
    simpa [cyclicPerm] using (hb 0).1
  have h₁ : EdgeBlock Z 1 2 0 (Submodule.span K (Set.range (v 1))) := by
    simpa [cyclicPerm] using (hb 1).1
  have h₂ : EdgeBlock Z 2 0 1 (Submodule.span K (Set.range (v 2))) := by
    simpa [cyclicPerm] using (hb 2).1
  refine ⟨s,v,Q,hv,hQ,?_,fun t => PhysicalCycleRelay.positive_directSum_realizes K (n (s t)),
    remaining_card s⟩
  exact map_repair_coordinates n s M Z _ _ _ (positive_bundle_split_chart Z v hv h₀ h₁ h₂ Q hQ)

/-- Reverse orientation: the same construction uses physically reversed
edges and leaves exactly the unselected original Jordan factors. -/
theorem exists_negative_repair_coordinates (n : R → ℕ) (M : Task K W) (Z : Task K V)
    (r : ℕ) (hr : r ≤ Fintype.card R) (hc : r ≤ cycleMultiplicity Z (Equiv.swap 0 1)) :
    ∃ (s : Fin r ↪ R) (v : Three → Fin r → V) (Q : Submodule K V)
      (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2))
      (hQ : TaskDecomposition.Split (configuration Z).spaces ⊤ Q (bundleSpan v)),
      mapTask (repairCoordinates n s (bundleSplitCoordinates Z v hv Q hQ))
        (directSum (ResonantFiniteAssembly.task n) (directSum M Z)) =
        directSum (directSum (ResonantFiniteAssembly.task (fun i : Remaining s => n i.val)) M)
          (directSum (FiniteRelayAssembly.task (fun t : Fin r =>
            directSum (ResonantRelay.jordanTask K (n (s t))) (CycleDirectSumCoordinates.reverseCycleTask K)))
            (SplitTaskCoordinates.leftTask Z Q (bundleSpan v) hQ)) ∧
      (∀ t : Fin r, RealizesMenu
        (directSum (ResonantRelay.jordanTask K (n (s t))) (CycleDirectSumCoordinates.reverseCycleTask K))
        (3*(n (s t)+1)+4) (fun (_ : Unit) => firstIncrement CycleFiniteAssembly.negativeIncrement)) ∧
      Fintype.card (Remaining s)=Fintype.card R-r := by
  obtain ⟨s⟩ := exists_distinct_selection r hr
  obtain ⟨v,Q,hv,hb,hQ⟩ := exists_cycle_bundle Z (Equiv.swap 0 1) r hc
  let w : Three → Fin r → V := fun a => v ((Equiv.swap 1 2) a)
  have hw : LinearIndependent K (fun x : (_a : Three) × Fin r => w x.1 x.2) := by
    apply hv.comp (fun x : (_a : Three) × Fin r => ⟨(Equiv.swap 1 2) x.1,x.2⟩)
    intro x y h
    have hfst : x.1=y.1 := (Equiv.swap 1 2).injective (congrArg Sigma.fst h)
    have hsnd : x.2=y.2 := by
      simpa only using congrArg (fun z : (_a : Three) × Fin r => z.2) h
    cases x with | mk a t =>
      cases y with | mk b u =>
        dsimp only at hfst hsnd
        cases hfst
        cases hsnd
        rfl
  have hW : bundleSpan (K := K) w=bundleSpan (K := K) v :=
    Equiv.iSup_comp (g := fun a => Submodule.span K (Set.range (v a))) (Equiv.swap 1 2)
  have hQw : TaskDecomposition.Split (configuration Z).spaces ⊤ Q (bundleSpan w) := by
    rw [hW]
    exact hQ
  have h₀ : EdgeBlock Z 1 0 2 (Submodule.span K (Set.range (w 0))) := by
    simpa [w,cyclicPerm] using (hb 0).1
  have h₁ : EdgeBlock Z 2 1 0 (Submodule.span K (Set.range (w 1))) := by
    simpa [w,cyclicPerm] using (hb 2).1
  have h₂ : EdgeBlock Z 0 2 1 (Submodule.span K (Set.range (w 2))) := by
    simpa [w,cyclicPerm] using (hb 1).1
  refine ⟨s,w,Q,hw,hQw,?_,fun t => PhysicalCycleRelay.negative_directSum_realizes K (n (s t)),
    remaining_card s⟩
  exact map_repair_coordinates n s M Z _ _ _ (negative_bundle_split_chart Z w hw h₀ h₁ h₂ Q hQw)

end RepairCoordinates

section FixedBlocks
open scoped BigOperators
variable {r : ℕ}

/-- The total positive-repair charge, with all second entries unchanged. -/
def positiveDelta (r : ℕ) : Profile.Index → ℝ
  | .inl j => if j=1 then r else 0
  | .inr _ => 0

/-- The total reverse-repair charge, with all second entries unchanged. -/
def negativeDelta (r : ℕ) : Profile.Index → ℝ
  | .inl j => if j=3 then r else 0
  | .inr _ => 0

omit [Fintype R] in
theorem positive_fixed_block_realizes (n : R → ℕ) (s : Fin r ↪ R) (Z : Task K V)
    (ha : ResidualComponentAdditivity.ActiveResidual Z)
    (hz : finrank K (Z.A 0)+finrank K (Z.A 1)+finrank K (Z.A 2)=finrank K V)
    (Q B : Submodule K V) (hs : TaskDecomposition.Split (configuration Z).spaces ⊤ Q B) :
    RealizesMenu (directSum (FiniteRelayAssembly.task (fun t : Fin r =>
      directSum (ResonantRelay.jordanTask K (n (s t))) (CycleDirectSumCoordinates.cycleTask K)))
        (SplitTaskCoordinates.leftTask Z Q B hs))
      ((∑ t : Fin r, (3*(n (s t)+1)+4))+finrank K Q)
      (fun (_ : Unit) => positiveDelta r) := by
  have hcycles := finite_fixed_realizes
    (fun t : Fin r => directSum (ResonantRelay.jordanTask K (n (s t))) (CycleDirectSumCoordinates.cycleTask K))
    (fun t => 3*(n (s t)+1)+4) (fun _ => firstIncrement CycleFiniteAssembly.positiveIncrement)
    (fun t => PhysicalCycleRelay.positive_directSum_realizes K (n (s t)))
  have hQ := (zero_remainder_menu Z ha hz Q B hs).2.2
  have hprod := product_fixed_realizes _ _ _ _ _ _ hcycles hQ
  have he : (fun (_ : Unit) p => (∑ _t : Fin r, firstIncrement CycleFiniteAssembly.positiveIncrement p)+0)=
      (fun (_ : Unit) => positiveDelta r) := by
    funext u p
    cases p with
    | inl j => by_cases hj : j=1 <;> simp [positiveDelta,firstIncrement,CycleFiniteAssembly.positiveIncrement,hj]
    | inr j => simp [positiveDelta,firstIncrement]
  rw [he] at hprod
  exact hprod

omit [Fintype R] in
theorem negative_fixed_block_realizes (n : R → ℕ) (s : Fin r ↪ R) (Z : Task K V)
    (ha : ResidualComponentAdditivity.ActiveResidual Z)
    (hz : finrank K (Z.A 0)+finrank K (Z.A 1)+finrank K (Z.A 2)=finrank K V)
    (Q B : Submodule K V) (hs : TaskDecomposition.Split (configuration Z).spaces ⊤ Q B) :
    RealizesMenu (directSum (FiniteRelayAssembly.task (fun t : Fin r =>
      directSum (ResonantRelay.jordanTask K (n (s t))) (CycleDirectSumCoordinates.reverseCycleTask K)))
        (SplitTaskCoordinates.leftTask Z Q B hs))
      ((∑ t : Fin r, (3*(n (s t)+1)+4))+finrank K Q)
      (fun (_ : Unit) => negativeDelta r) := by
  have hcycles := finite_fixed_realizes
    (fun t : Fin r => directSum (ResonantRelay.jordanTask K (n (s t))) (CycleDirectSumCoordinates.reverseCycleTask K))
    (fun t => 3*(n (s t)+1)+4) (fun _ => firstIncrement CycleFiniteAssembly.negativeIncrement)
    (fun t => PhysicalCycleRelay.negative_directSum_realizes K (n (s t)))
  have hQ := (zero_remainder_menu Z ha hz Q B hs).2.2
  have hprod := product_fixed_realizes _ _ _ _ _ _ hcycles hQ
  have he : (fun (_ : Unit) p => (∑ _t : Fin r, firstIncrement CycleFiniteAssembly.negativeIncrement p)+0)=
      (fun (_ : Unit) => negativeDelta r) := by
    funext u p
    cases p with
    | inl j => by_cases hj : j=3 <;> simp [negativeDelta,firstIncrement,CycleFiniteAssembly.negativeIncrement,hj]
    | inr j => simp [negativeDelta,firstIncrement]
  rw [he] at hprod
  exact hprod
end FixedBlocks

section RankAccounting
open scoped BigOperators

/-- Selected original factors and their untouched complement account for
each summand exactly once, even when the Jordan sizes differ. -/
theorem selected_add_remaining {r : ℕ} (s : Fin r ↪ R) {A : Type*} [AddCommMonoid A]
    (f : R → A) :
    (∑ t : Fin r, f (s t))+(∑ i : Remaining s, f i.val)=∑ i : R, f i := by
  letI : Fintype (Set.range s) := Subtype.fintype _
  have hselected := (Equiv.ofInjective s s.injective).sum_comp
    (fun i : Set.range s => f i.val)
  have hpartition := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ Set.range s) f
  exact (congrArg (fun x => x+(∑ i : Remaining s, f i.val)) hselected).trans hpartition

omit [Fintype R] in
/-- Three independent physical coordinates are removed for each scalar
cycle, so the untouched actual source dimension is known exactly. -/
theorem remainder_dimension {r : ℕ} (Z : Task K V) (v : Three → Fin r → V)
    (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2))
    (Q : Submodule K V) (hQ : TaskDecomposition.Split (configuration Z).spaces ⊤ Q (bundleSpan v)) :
    finrank K Q+3*r=finrank K V := by
  have hd := (SplitTaskCoordinates.splitEquiv Z Q (bundleSpan v) hQ).finrank_eq
  rw [Module.finrank_prod,cycle_bundle_finrank v hv] at hd
  exact hd

/-- Repaired pairs add the three cycle coordinates to their original
Jordan relay size; no upload rank is charged twice or discarded. -/
theorem repaired_rank_total (n : R → ℕ) {r : ℕ} (s : Fin r ↪ R) (Z : Task K V)
    (v : Three → Fin r → V)
    (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2))
    (Q : Submodule K V) (hQ : TaskDecomposition.Split (configuration Z).spaces ⊤ Q (bundleSpan v))
    (d : ℕ) :
    ((∑ i : Remaining s, (3*(n i.val+1)+1))+d)+
      ((∑ t : Fin r, (3*(n (s t)+1)+4))+finrank K Q) =
      ((∑ i : R, (3*(n i+1)+1))+d)+finrank K V := by
  have hsum := selected_add_remaining s (fun i => 3*(n i+1)+1)
  have hdim := remainder_dimension Z v hv Q hQ
  have hcost : (∑ t : Fin r, (3*(n (s t)+1)+4))=
      (∑ t : Fin r, (3*(n (s t)+1)+1))+3*r := by
    simp_rw [show ∀ t : Fin r, 3*(n (s t)+1)+4=(3*(n (s t)+1)+1)+3 by intro; omega]
    simp [Finset.sum_add_distrib,Nat.mul_comm]
  omega

/-- The exact original residual upload value before any cycle pairing. -/
theorem original_rank_uploadValue {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (n : R → ℕ) (M : Task K W) (Z : Task K V) (d : ℕ)
    (hM : ResidualComponentAdditivity.uploadValue M=(d : ℝ))
    (hz : finrank K (Z.A 0)+finrank K (Z.A 1)+finrank K (Z.A 2)=finrank K V) :
    ResidualComponentAdditivity.uploadValue
      (directSum (ResonantFiniteAssembly.task n) (directSum M Z)) =
      ((((∑ i : R, (3*(n i+1)+1))+d)+finrank K V : ℕ) : ℝ) := by
  have hJ : ResidualComponentAdditivity.uploadValue (ResonantFiniteAssembly.task (K := K) n)=
      ((∑ i : R, (3*(n i+1)+1)) : ℕ) := by
    rw [ResidualComponentAdditivity.uploadValue_product]
    simp only [RegularRelayOptimality.jordan_uploadValue,Nat.cast_sum]
  have hZ : ResidualComponentAdditivity.uploadValue Z=(finrank K V : ℝ) := by
    have hz' : (finrank K (Z.A 0) : ℝ)+finrank K (Z.A 1)+finrank K (Z.A 2)=finrank K V :=
      by exact_mod_cast hz
    unfold ResidualComponentAdditivity.uploadValue
    rw [hz']
    ring
  have hadd : ResidualComponentAdditivity.uploadValue
      (directSum (ResonantFiniteAssembly.task (K := K) n) (directSum M Z))=
      ResidualComponentAdditivity.uploadValue (ResonantFiniteAssembly.task (K := K) n)+
        ResidualComponentAdditivity.uploadValue M+ResidualComponentAdditivity.uploadValue Z := by
    unfold ResidualComponentAdditivity.uploadValue
    simp only [directSum,Profile.finrank_submodule_prod,Module.finrank_prod,Nat.cast_add]
    ring
  rw [hadd,hJ,hM,hZ]
  simp only [Nat.cast_add]

/-- The assembled rank is exactly the original residual upload expression.
The only menu-side input is its already computed local dimension sum; Jordan
and physical-cycle contributions are derived here from their coefficients. -/
theorem repaired_rank_uploadValue {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (n : R → ℕ) {r : ℕ} (s : Fin r ↪ R)
    (M : Task K W) (Z : Task K V) (d : ℕ)
    (hM : ResidualComponentAdditivity.uploadValue M=(d : ℝ))
    (hz : finrank K (Z.A 0)+finrank K (Z.A 1)+finrank K (Z.A 2)=finrank K V)
    (v : Three → Fin r → V)
    (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2))
    (Q : Submodule K V) (hQ : TaskDecomposition.Split (configuration Z).spaces ⊤ Q (bundleSpan v)) :
    (((((∑ i : Remaining s, (3*(n i.val+1)+1))+d)+
      ((∑ t : Fin r, (3*(n (s t)+1)+4))+finrank K Q)) : ℕ) : ℝ) =
      ResidualComponentAdditivity.uploadValue
        (directSum (ResonantFiniteAssembly.task n) (directSum M Z)) := by
  rw [repaired_rank_total n s Z v hv Q hQ d]
  exact (original_rank_uploadValue n M Z d hM hz).symm
end RankAccounting

end UploadBroadcast.RelayCyclePairing
