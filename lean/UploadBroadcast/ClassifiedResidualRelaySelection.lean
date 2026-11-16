import UploadBroadcast.ClassifiedComponentMenus
import UploadBroadcast.OrientedRelayPairing
import UploadBroadcast.OrientationSlackCounts
import UploadBroadcast.RepairedGlobalMenuAssembly

namespace UploadBroadcast.ClassifiedResidualRelaySelection
open Module Profile GlobalMenuAssembly OrientationRepairAllocation
open RelayCyclePairing OrientedRelayPairing ClassifiedComponentMenus
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K I R V W : Type} {F : I → Type}
  [Field K] [Finite K] [Fintype I] [Fintype R]
  [∀ t, AddCommGroup (F t)] [∀ t, Module K (F t)] [∀ t, FiniteDimensional K (F t)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

abbrev residualTask (nR : R → ℕ) (T : (t : I) → Task K (F t)) (Z : Task K V) :=
  directSum (ResonantFiniteAssembly.task (K := K) nR) (directSum (FiniteRelayAssembly.task T) Z)

/-- Assemble and pull back one physically chosen repair orientation. This
helper assumes only a repair count and genuine physical edge capacity, never
a relay or a target induced profile. -/
theorem of_oriented_count (nR : R → ℕ) (T : (t : I) → Task K (F t)) (Z : Task K V) (O : Task K W)
    (hT : ∀ t, TaskDecomposition.Indecomposable (EdgeExtraction.configuration (T t)).spaces ⊤)
    (g : I → NonzeroDefectProfile.Family) (n : I → ℕ) (p : I → Fin 6)
    (hn : ∀ t, Legal (g t) (n t))
    (hdims : ∀ t, NonzeroFamilyRanks.Dimensions (reindexTask (R2PermutedMenus.pathPerm (p t)) (T t)) (g t) (n t))
    (hZ : ResidualComponentAdditivity.ActiveResidual Z)
    (hz : finrank K (Z.A 0)+finrank K (Z.A 1)+finrank K (Z.A 2)=finrank K V)
    (D : ℤ) (c : Fin 6 → ℤ) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ j, (Fintype.card R : ℤ)+(∑ t, ActualComponentCapacities.charge (g t) (n t) (p t) j) ≤
      c (BinaryMenuAllocation.pairLeft j)+c (BinaryMenuAllocation.pairRight j))
    (hfirst : ∀ j, entry (directSum (residualTask nR T Z) O) (.inl j)+(c j : ℝ)=D)
    (hsecond : ∀ r : Three × Three, entry (directSum (residualTask nR T Z) O) (.inr r) ≤ D)
    (b : Bool) (r : ℕ) (hr : r ≤ Fintype.card R)
    (hcycle : r ≤ EdgeDeficits.cycleMultiplicity Z (userOrder b))
    (hpos : positiveCount (Fintype.card R) c = if b then 0 else (r : ℤ))
    (hneg : negativeCount (Fintype.card R) c = if b then (r : ℤ) else 0) :
    ∃ P : Submodule K (ResonantFiniteAssembly.Ambient (K := K) nR × ((∀ t, F t) × V)),
      ∃ hg : (residualTask nR T Z).LocallyGenerated P,
      (residualTask nR T Z).RelayFeasible P ∧
      finrank K P=((∑ t, (3*(nR t+1)+1))+(∑ t, relayRank (g t) (n t)))+finrank K V ∧
      ∀ ν, entry ((residualTask nR T Z).inducedRelay P hg) ν+entry O ν ≤ D := by
  classical
  obtain ⟨s,v,Q,hv,hQ,he,hcard⟩ := exists_coordinates b nR (FiniteRelayAssembly.task T) Z r hr hcycle
  let E := repairCoordinates (W := ∀ t, F t) nR s (bundleSplitCoordinates Z v hv Q hQ)
  let fixed := directSum (FiniteRelayAssembly.task (fun t : Fin r =>
    directSum (ResonantRelay.jordanTask K (nR (s t))) (OrientedRelayPairing.cycleTask K b)))
    (SplitTaskCoordinates.leftTask Z Q (bundleSpan v) hQ)
  let newTask := directSum (directSum (ResonantFiniteAssembly.task (fun i : Remaining s => nR i.val))
    (FiniteRelayAssembly.task T)) fixed
  have hchart : mapTask E (residualTask nR T Z)=newTask := he
  have hentry (ν : Index) : entry newTask ν=entry (residualTask nR T Z) ν := by
    rw [← hchart,entry_mapTask]
  have hfmenu : RealizesMenu fixed ((∑ t : Fin r, (3*(nR (s t)+1)+4))+finrank K Q)
      (fun (_ : Unit) => delta b r) := fixed_realizes b nR s Z hZ hz Q (bundleSpan v) hQ
  have hcount : (Fintype.card (Remaining s) : ℤ)=
      (Fintype.card R : ℤ)-positiveCount (Fintype.card R) c-negativeCount (Fintype.card R) c := by
    rw [hpos,hneg,hcard,Int.ofNat_sub hr]
    cases b <;> simp
  have hδfirst (j : Fin 6) : delta b r (.inl j)=
      (if j=1 then (positiveCount (Fintype.card R) c : ℝ) else 0)+
      (if j=3 then (negativeCount (Fintype.card R) c : ℝ) else 0) := by
    rw [hpos,hneg]
    cases b <;> simp [delta,positiveDelta,negativeDelta]
  have hδsecond (ν : Three × Three) : delta b r (.inr ν)=0 := by
    cases b <;> rfl
  obtain ⟨P,hl,hf,hd,hprof⟩ := RepairedGlobalMenuAssembly.construct_repaired_relay_profile_budget
    (fun i : Remaining s => nR i.val) T fixed (fun _ => Fin 6)
    (fun t => relayRank (g t) (n t)) ((∑ t : Fin r, (3*(nR (s t)+1)+4))+finrank K Q)
    (fun t => ClassifiedComponentMenus.menu (g t) (n t) (p t))
    (fun t => ActualComponentCapacities.charge (g t) (n t) (p t))
    (fun t j => ActualComponentCapacities.charge_nonneg (g t) (n t) (p t) j)
    (fun t => ClassifiedComponentMenus.menu_fits (g t) (n t) (hn t) (p t))
    (fun t => ClassifiedComponentMenus.realizes_menu (T t) (hT t) (g t) (n t) (hn t) (p t) (hdims t))
    (delta b r) hfmenu (Fintype.card R) (Nat.cast_nonneg _) c hc hp hcount hδfirst hδsecond
    (fun ν => (D : ℝ)-entry O ν)
    (by
      intro j
      change entry newTask (.inl j)+(c j : ℝ) ≤ (D : ℝ)-entry O (.inl j)
      rw [hentry]
      have hh := hfirst j
      rw [entry_directSum] at hh
      linarith only [hh])
    (by
      intro ν
      change entry newTask (.inr ν) ≤ (D : ℝ)-entry O (.inr ν)
      rw [hentry]
      have hh := hsecond ν
      rw [entry_directSum] at hh
      linarith only [hh])
  have hd' : finrank K P=((∑ t, (3*(nR t+1)+1))+(∑ t, relayRank (g t) (n t)))+finrank K V :=
    hd.trans (repaired_rank_total nR s Z v hv Q hQ (∑ t, relayRank (g t) (n t)))
  have hback : mapTask E.symm newTask=residualTask nR T Z := by
    rw [← hchart]
    exact ResidualRelayAssembly.mapTask_inverse _ E.symm
  obtain ⟨P',hl',hf',hd',hp'⟩ := RelayCoordinateTransport.transport_exists newTask (residualTask nR T Z)
    E.symm hback _ (fun ν => (D : ℝ)-entry O ν) ⟨P,hl,hf,hd',hprof⟩
  refine ⟨P',hl',hf',hd',?_⟩
  intro ν
  have hh := hp' ν
  dsimp only at hh
  linarith only [hh]

/-- Full actual selection on the classified residual product at an integer
budget. Component charges, orientation repair counts, physical cycle supply,
menu choices and all fifteen final bounds are derived from the original task. -/
theorem exists_relay (nR : R → ℕ) (T : (t : I) → Task K (F t)) (Z : Task K V) (O : Task K W)
    (hT : ∀ t, TaskDecomposition.Indecomposable (EdgeExtraction.configuration (T t)).spaces ⊤)
    (g : I → NonzeroDefectProfile.Family) (n : I → ℕ) (p : I → Fin 6)
    (hn : ∀ t, Legal (g t) (n t))
    (hdims : ∀ t, NonzeroFamilyRanks.Dimensions (reindexTask (R2PermutedMenus.pathPerm (p t)) (T t)) (g t) (n t))
    (hM : ∀ i j k : Three, i≠j → i≠k → j≠k →
      EdgeExtraction.multiplicity (FiniteRelayAssembly.task T) i j k=0)
    (hZ : ResidualComponentAdditivity.ActiveResidual Z)
    (hz : finrank K (Z.A 0)+finrank K (Z.A 1)+finrank K (Z.A 2)=finrank K V)
    (hO : ∀ i, O.U i=⊤) (D : ℤ)
    (hD : rankBound (directSum (residualTask nR T Z) O) ≤ (D : ℝ)) :
    ∃ P : Submodule K (ResonantFiniteAssembly.Ambient (K := K) nR × ((∀ t, F t) × V)),
      ∃ hg : (residualTask nR T Z).LocallyGenerated P,
      (residualTask nR T Z).RelayFeasible P ∧
      finrank K P=((∑ t, (3*(nR t+1)+1))+(∑ t, relayRank (g t) (n t)))+finrank K V ∧
      ∀ ν, entry ((residualTask nR T Z).inducedRelay P hg) ν+entry O ν ≤ D := by
  classical
  have he (ν : Index) : entry (ActualComponentCapacities.fullTask nR T (directSum Z O)) ν =
      entry (directSum (residualTask nR T Z) O) ν := by
    simp only [ActualComponentCapacities.fullTask,residualTask,entry_directSum]
    ring
  have hD' : rankBound (ActualComponentCapacities.fullTask nR T (directSum Z O)) ≤ (D : ℝ) := by
    simpa only [rankBound,he] using hD
  obtain ⟨c,hc,hfirst,hp,hsecond⟩ := ActualComponentCapacities.actual_integer_capacities
    nR T (directSum Z O) hT g n p hn hdims D hD'
  have hfirst' (j : Fin 6) : entry (directSum (residualTask nR T Z) O) (.inl j)+(c j : ℝ)=D := by
    simpa only [he] using hfirst j
  have hsecond' (ν : Three × Three) : entry (directSum (residualTask nR T Z) O) (.inr ν) ≤ D := by
    simpa only [he] using hsecond ν
  have hqsum := ActualComponentCapacities.totalCharge_nonneg g n p
  obtain ⟨ha,hb,hbound,hone,_,_,_,_⟩ := repaired_capacities (Fintype.card R)
    (ActualComponentCapacities.totalCharge g n p) c (Nat.cast_nonneg _) hqsum hc hp
      (sum_capacity (Fintype.card R) (ActualComponentCapacities.totalCharge g n p) c hqsum hp)
  obtain ⟨hcycP,hcycN⟩ := OrientationSlackCounts.counts_le_cycles nR (FiniteRelayAssembly.task T) Z O
    hM hO D hD c hfirst'
  by_cases ha0 : positiveCount (Fintype.card R) c=0
  · have hrI := Int.toNat_of_nonneg hb
    have hr : (negativeCount (Fintype.card R) c).toNat ≤ Fintype.card R := by omega
    exact of_oriented_count nR T Z O hT g n p hn hdims hZ hz D c hc hp hfirst' hsecond'
      true (negativeCount (Fintype.card R) c).toNat hr hcycN ha0 hrI.symm
  · have hb0 : negativeCount (Fintype.card R) c=0 := hone.resolve_left ha0
    have hrI := Int.toNat_of_nonneg ha
    have hr : (positiveCount (Fintype.card R) c).toNat ≤ Fintype.card R := by omega
    exact of_oriented_count nR T Z O hT g n p hn hdims hZ hz D c hc hp hfirst' hsecond'
      false (positiveCount (Fintype.card R) c).toNat hr hcycP hrI.symm hb0

end UploadBroadcast.ClassifiedResidualRelaySelection
