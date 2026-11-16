import UploadBroadcast.ResidualComponentClassification
import UploadBroadcast.FiniteProductCoordinates
import UploadBroadcast.ResonantFiniteAssembly
import UploadBroadcast.ResidualComponentFactors
import UploadBroadcast.PositiveExcessNoEdges

/-! An actual finite active-residual decomposition is partitioned by its
computed dimensions and defect. The regular factors receive constructed
Jordan charts; all other positive factors retain their original coefficients
and their concrete classified arm order. -/
namespace UploadBroadcast.ClassifiedRelayPartition
open Module Profile ResidualComponentAdditivity ActiveComponentClassification
open FiniteProductCoordinates
attribute [local instance] Classical.propDecidable
variable {K I : Type} [Field K] [Finite K]
  {F : I → Type} [∀ i, AddCommGroup (F i)] [∀ i, Module K (F i)]
  [∀ i, FiniteDimensional K (F i)]

/-- Zero excess is tested on the original component dimensions. -/
def ZeroExcess (T : ∀ i, Task K (F i)) (i : I) : Prop :=
  finrank K ((T i).A 0)+finrank K ((T i).A 1)+finrank K ((T i).A 2)=finrank K (F i)

/-- The actual positive regular components, without any family oracle. -/
def IsResonant (T : ∀ i, Task K (F i)) (i : I) : Prop :=
  ¬ZeroExcess T i ∧
    ReflectionReduction.defect (EdgeExtraction.configuration (T i)).dimensionVector=0

abbrev ResonantIndex (T : ∀ i, Task K (F i)) := {i // IsResonant T i}
abbrev OtherIndex (T : ∀ i, Task K (F i)) := {i // ¬IsResonant T i}
abbrev MenuIndex (T : ∀ i, Task K (F i)) := {i : OtherIndex T // ¬ZeroExcess T i.val}
abbrev ZeroIndex (T : ∀ i, Task K (F i)) := {i : OtherIndex T // ¬¬ZeroExcess T i.val}

abbrev MenuAmbient (T : ∀ i, Task K (F i)) := ∀ i : MenuIndex T, F i.val.val
abbrev ZeroAmbient (T : ∀ i, Task K (F i)) := ∀ i : ZeroIndex T, F i.val.val
abbrev menuTask (T : ∀ i, Task K (F i)) :=
  FiniteRelayAssembly.task (fun i : MenuIndex T => T i.val.val)
abbrev zeroTask (T : ∀ i, Task K (F i)) :=
  FiniteRelayAssembly.task (fun i : ZeroIndex T => T i.val.val)

/-- A positive nonregular component carries one of the full menus or one of
both genuine tripod boundaries. The permutation is part of the output. -/
def MenuAssignment {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Task K V) : Prop :=
  ∃ k : Fin 6,
    (∃ (g : NonzeroDefectProfile.Family) (n : ℕ), 1 ≤ n ∧
      NonzeroFamilyRanks.Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) g n) ∨
    NonzeroFamilyRanks.Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) .T1 0 ∨
    NonzeroFamilyRanks.Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) .T2 0

omit [Finite K] in
theorem positive_of_not_zero (T : ∀ i, Task K (F i))
    (ha : ∀ i, ActiveResidual (T i)) (i : I) (hi : ¬ZeroExcess T i) :
    finrank K (F i) < finrank K ((T i).A 0)+finrank K ((T i).A 1)+finrank K ((T i).A 2) := by
  have hn := ResidualComponentClassification.nonnegative_excess (T i) (ha i)
  unfold ZeroExcess at hi
  omega

theorem resonant_charts (T : ∀ i, Task K (F i))
    (ha : ∀ i, ActiveResidual (T i))
    (hi : ∀ i, TaskDecomposition.Indecomposable (EdgeExtraction.configuration (T i)).spaces ⊤) :
    ∀ i : ResonantIndex T, ∃ (n : ℕ)
      (e : F i.val ≃ₗ[K] ResonantEndomorphisms.Ambient K (JordanResonance.V K n)),
      mapTask e (T i.val)=ResonantRelay.jordanTask K n := by
  intro i
  exact regular_assignment (T i.val) (hi i.val) i.property.2
    (by simpa only [Task.Spanning,three_iSup] using (ha i.val).spanning)
    (positive_of_not_zero T ha i.val i.property.1)
    (exists_nontrivial_demand _ (ha i.val) (hi i.val).1)

omit [Finite K] in
theorem menu_assignments (T : ∀ i, Task K (F i))
    (ha : ∀ i, ActiveResidual (T i))
    (hi : ∀ i, TaskDecomposition.Indecomposable (EdgeExtraction.configuration (T i)).spaces ⊤) :
    ∀ i : MenuIndex T, MenuAssignment (T i.val.val) := by
  intro i
  have hp := positive_of_not_zero T ha i.val.val i.property
  have hd : ReflectionReduction.defect
      (EdgeExtraction.configuration (T i.val.val)).dimensionVector ≠ 0 := by
    intro hz
    exact i.val.property ⟨i.property,hz⟩
  exact active_nonzero_defect_assignment (T i.val.val) (hi i.val.val) hd hp
    (exists_nontrivial_demand _ (ha i.val.val) (hi i.val.val).1)
    (exists_nonfull_signal _ (ha i.val.val) hp)

omit [Finite K] [∀ i, FiniteDimensional K (F i)] in
theorem zero_assignments (T : ∀ i, Task K (F i)) :
    ∀ i : ZeroIndex T, ZeroExcess T i.val.val := by
  classical
  intro i
  exact Classical.not_not.mp i.property

omit [Finite K] [∀ i, FiniteDimensional K (F i)] in
/-- The untouched zero-excess product retains intrinsic residual activity. -/
theorem zero_task_active (T : ∀ i, Task K (F i)) (ha : ∀ i, ActiveResidual (T i)) :
    ActiveResidual (zeroTask T) := ActiveResidual.product _ (fun i => ha i.val.val)

omit [Finite K] in
/-- Zero excess adds exactly on the actual retained coefficient factors. -/
theorem zero_task_excess [Fintype I] (T : ∀ i, Task K (F i)) :
    finrank K ((zeroTask T).A 0)+finrank K ((zeroTask T).A 1)+finrank K ((zeroTask T).A 2)=
      finrank K (ZeroAmbient T) :=
  zero_excess_product _ (zero_assignments T)

omit [Finite K] in
/-- The positive classified menu factors cannot consume any physical edge
capacity. Every cycle used later therefore lies in the zero-excess product. -/
theorem menu_task_has_no_edges [Fintype I] (T : ∀ i, Task K (F i))
    (ha : ∀ i, ActiveResidual (T i))
    (hi : ∀ i, TaskDecomposition.Indecomposable (EdgeExtraction.configuration (T i)).spaces ⊤)
    (a b c : Three) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    EdgeExtraction.multiplicity (menuTask T) a b c=0 :=
  PositiveExcessNoEdges.positive_finite_task_has_no_edges _
    (fun i => hi i.val.val) (fun i => positive_of_not_zero T ha i.val.val i.property) a b c hab hac hbc

/-- The classified factors form an actual coefficient chart of the original
product. Every index is selected from the original finite component family;
no prescribed typed partition is assumed. -/
theorem exists_classified_product_coordinates (T : ∀ i, Task K (F i))
    (ha : ∀ i, ActiveResidual (T i))
    (hi : ∀ i, TaskDecomposition.Indecomposable (EdgeExtraction.configuration (T i)).spaces ⊤) :
    ∃ (n : ResonantIndex T → ℕ)
      (e : (∀ i, F i) ≃ₗ[K]
        (ResonantFiniteAssembly.Ambient (K := K) n × (MenuAmbient T × ZeroAmbient T))),
      mapTask e (FiniteRelayAssembly.task T) =
        directSum (ResonantFiniteAssembly.task n) (directSum (menuTask T) (zeroTask T)) ∧
      (∀ i : MenuIndex T, MenuAssignment (T i.val.val)) ∧
      (∀ i : ZeroIndex T, ZeroExcess T i.val.val) := by
  classical
  choose n c hc using resonant_charts T ha hi
  let e₁ := partitionEquiv (K := K) (F := F) (IsResonant T)
  let e₂ := partitionEquiv (K := K) (F := fun i : OtherIndex T => F i.val)
    (fun i : OtherIndex T => ¬ZeroExcess T i.val)
  let e₃ := (LinearEquiv.piCongrRight c).prodCongr e₂
  refine ⟨n,e₁.trans e₃,?_,menu_assignments T ha hi,zero_assignments T⟩
  rw [← mapTask_trans, map_product_partition, map_directSum_congr,
    map_product_congr,map_product_partition]
  simp only [hc]

section OriginalTask
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Starting only from an intrinsic active residual, first construct its
finite indecomposable decomposition and then its classified product chart. -/
theorem exists_original_classified_coordinates (S : Task K V) (hS : ActiveResidual S) :
    ∃ (m : ℕ) (P : Fin m → Submodule K V) (c : (∀ i, P i) ≃ₗ[K] V),
      let T := FiniteComponentCoordinates.componentTask S P c
      ∃ (n : ResonantIndex T → ℕ)
        (e : V ≃ₗ[K]
          (ResonantFiniteAssembly.Ambient (K := K) n × (MenuAmbient T × ZeroAmbient T))),
        mapTask e S =
          directSum (ResonantFiniteAssembly.task n) (directSum (menuTask T) (zeroTask T)) ∧
        (∀ i : MenuIndex T, MenuAssignment (T i.val.val)) ∧
        (∀ i : ZeroIndex T, ZeroExcess T i.val.val) ∧
        (∀ i, ActiveResidual (T i)) ∧
        (∀ i, TaskDecomposition.Indecomposable (EdgeExtraction.configuration (T i)).spaces ⊤) := by
  obtain ⟨m,P,c,hc,hi,hA,hU,ha,hu,hui,hus,hd⟩ :=
    exists_indecomposable_residual_decomposition S hS
  obtain ⟨n,e,he,hm,hz⟩ := exists_classified_product_coordinates
    (FiniteComponentCoordinates.componentTask S P c) ha hi
  refine ⟨m,P,c,n,c.symm.trans e,?_,hm,hz,ha,hi⟩
  have hback : mapTask c.symm S =
      FiniteRelayAssembly.task (FiniteComponentCoordinates.componentTask S P c) := by
    conv_lhs => rw [← hc]
    exact ResidualRelayAssembly.mapTask_inverse _ c.symm
  exact (mapTask_trans S c.symm e).symm.trans ((congrArg (mapTask e) hback).trans he)
end OriginalTask

end UploadBroadcast.ClassifiedRelayPartition
