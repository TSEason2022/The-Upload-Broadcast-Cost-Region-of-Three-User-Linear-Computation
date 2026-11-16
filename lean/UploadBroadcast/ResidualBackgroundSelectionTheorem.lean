import UploadBroadcast.ResidualBackgroundSelection
import UploadBroadcast.ClassifiedRelayPartition
import UploadBroadcast.ClassifiedComponentRanks
import UploadBroadcast.ClassifiedResidualRelaySelection

namespace UploadBroadcast.ResidualBackgroundSelectionTheorem
open Module Profile ResidualComponentAdditivity ClassifiedRelayPartition ClassifiedComponentMenus
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 8192
variable {K V W : Type} [Field K] [Finite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Unconditional active-residual relay selection with the entire omniscience
profile kept in the budget. Every decomposition, family assignment, capacity,
physical cycle and actual relay is constructed from the original task. -/
theorem exists_optimal_relay (S : Task K V) (hS : ActiveResidual S) (O : Task K W)
    (hO : ∀ i, O.U i=⊤) (D : ℤ) (hD : rankBound (directSum S O) ≤ (D : ℝ)) :
    ∃ P : Submodule K V, ∃ hg : S.LocallyGenerated P,
      S.RelayFeasible P ∧ (finrank K P : ℝ)=S.uploadOptimum ∧
      ∀ r, entry (S.inducedRelay P hg) r+entry O r ≤ (D : ℝ) := by
  classical
  obtain ⟨m,B,c,nR,e,he,hassign,hzero,ha,hi⟩ := exists_original_classified_coordinates S hS
  let T := FiniteComponentCoordinates.componentTask S B c
  let TM : (i : MenuIndex T) → Task K (B i.val.val) := fun i => T i.val.val
  let Z := zeroTask T
  have hclass : mapTask e S=ClassifiedResidualRelaySelection.residualTask nR TM Z := he
  have hlabels (i : MenuIndex T) : ∃ (g : NonzeroDefectProfile.Family) (n : ℕ) (p : Fin 6),
      Legal g n ∧ NonzeroFamilyRanks.Dimensions (reindexTask (R2PermutedMenus.pathPerm p) (TM i)) g n := by
    obtain ⟨p,h⟩ := hassign i
    rcases h with ⟨g,n,hn,hd⟩ | hd | hd
    · exact ⟨g,n,p,Or.inl hn,hd⟩
    · exact ⟨.T1,0,p,Or.inr ⟨rfl,Or.inl rfl⟩,hd⟩
    · exact ⟨.T2,0,p,Or.inr ⟨rfl,Or.inr rfl⟩,hd⟩
  choose g n p hn hdims using hlabels
  have hTM : ∀ i : MenuIndex T,
      TaskDecomposition.Indecomposable (EdgeExtraction.configuration (TM i)).spaces ⊤ := fun i => hi i.val.val
  have hM : ∀ i j k : Three, i≠j → i≠k → j≠k →
      EdgeExtraction.multiplicity (FiniteRelayAssembly.task TM) i j k=0 :=
    menu_task_has_no_edges T ha hi
  have hZa : ActiveResidual Z := zero_task_active T ha
  have hZz : finrank K (Z.A 0)+finrank K (Z.A 1)+finrank K (Z.A 2)=finrank K (ZeroAmbient T) :=
    zero_task_excess T
  have hentry (r : Index) : entry (ClassifiedResidualRelaySelection.residualTask nR TM Z) r=entry S r := by
    rw [← hclass,entry_mapTask]
  have hD' : rankBound (directSum (ClassifiedResidualRelaySelection.residualTask nR TM Z) O) ≤ (D : ℝ) := by
    simpa only [rankBound,entry_directSum,hentry] using hD
  obtain ⟨P,hl,hf,hd,hprof⟩ := ClassifiedResidualRelaySelection.exists_relay
    nR TM Z O hTM g n p hn hdims hM hZa hZz hO D hD'
  let d : ℕ := ((∑ i, (3*(nR i+1)+1))+(∑ i, relayRank (g i) (n i)))+finrank K (ZeroAmbient T)
  have hMd : uploadValue (FiniteRelayAssembly.task TM)=((∑ i, relayRank (g i) (n i) : ℕ) : ℝ) :=
    ClassifiedComponentRanks.finite_product_uploadValue TM g n p hn hdims
  have htotal : uploadValue (ClassifiedResidualRelaySelection.residualTask nR TM Z)=(d : ℝ) :=
    RelayCyclePairing.original_rank_uploadValue nR (FiniteRelayAssembly.task TM) Z _ hMd hZz
  have hU : (d : ℝ)=S.uploadOptimum := by
    rw [minimum_upload S hS]
    have hh := uploadValue_map S e
    rw [hclass] at hh
    exact htotal.symm.trans hh
  have hback : mapTask e.symm (ClassifiedResidualRelaySelection.residualTask nR TM Z)=S := by
    rw [← hclass]
    exact ResidualRelayAssembly.mapTask_inverse S e.symm
  have hconstructed : ∃ P : Submodule K _,
      ∃ hg : (ClassifiedResidualRelaySelection.residualTask nR TM Z).LocallyGenerated P,
      (ClassifiedResidualRelaySelection.residualTask nR TM Z).RelayFeasible P ∧ finrank K P=d ∧
      ∀ r, entry ((ClassifiedResidualRelaySelection.residualTask nR TM Z).inducedRelay P hg) r ≤
        (D : ℝ)-entry O r := by
    refine ⟨P,hl,hf,hd,?_⟩
    intro r
    have hh := hprof r
    linarith only [hh]
  obtain ⟨P',hl',hf',hd',hp'⟩ := RelayCoordinateTransport.transport_exists
    (ClassifiedResidualRelaySelection.residualTask nR TM Z) S e.symm hback d
      (fun r => (D : ℝ)-entry O r) hconstructed
  refine ⟨P',hl',hf',?_,?_⟩
  · rw [hd']
    exact hU
  · intro r
    have hh := hp' r
    change entry (S.inducedRelay P' hl') r ≤ (D : ℝ)-entry O r at hh
    linarith only [hh]

/-- The residual geometric input needed by canonical and original-task
endpoint assembly is now a theorem over every original finite field. -/
theorem residual_background_selection (K : Type) [Field K] [Finite K] :
    UploadBroadcast.ResidualBackgroundSelection K := by
  intro V W _ _ _ _ _ _ S hS O hO D hD
  exact exists_optimal_relay S hS O hO D hD

end UploadBroadcast.ResidualBackgroundSelectionTheorem
