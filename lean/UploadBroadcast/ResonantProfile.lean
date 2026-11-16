import UploadBroadcast.ResonantRelay
import UploadBroadcast.CycleProfile

/-! All fifteen LCBC rank entries of the original resonant relay menus. -/
namespace UploadBroadcast.ResonantRelay
open ResonantEndomorphisms
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
variable (K X : Type*) [Field K] [AddCommGroup X] [Module K X]
variable (J : X →ₗ[K] X) (h : X →ₗ[K] K)

def pairMap (b : Fin 3) : X →ₗ[K] Ambient K X where
  toFun w := ![(w,w,w,0,0),(w,w+J w,w+J w,h w,0),(w,w+J w,w,0,h w)] b
  map_add' := by intro x y; fin_cases b <;> simp [add_add_add_comm]
  map_smul' := by intro a w; fin_cases b <;> simp [smul_add]

@[simp] theorem pairMap_injective (b : Fin 3) : Function.Injective (pairMap K X J h b) := by
  intro x y heq
  have he := congrArg (fun p : Ambient K X => p.1) heq
  fin_cases b <;> simpa [pairMap] using he

def pairSpace (b : Fin 3) : Submodule K (Ambient K X) := LinearMap.range (pairMap K X J h b)

theorem pair₁₂_eq : signal K X J h 0 ⊓ signal K X J h 1 = pairSpace K X J h 0 := by
  ext p
  constructor
  · rintro ⟨hp,hq⟩
    change p.2.1 = p.2.2.1 ∧ p.2.2.2.2 = 0 at hp
    change p.1 = p.2.2.1 ∧ p.2.2.2.1 = 0 at hq
    refine ⟨p.1, ?_⟩
    change (p.1,p.1,p.1,0,0) = p
    exact Prod.ext rfl (Prod.ext (hq.1.trans hp.1.symm) (Prod.ext hq.1 (Prod.ext hq.2.symm hp.2.symm)))
  · rintro ⟨w,rfl⟩
    simp [pairMap,signal,total₁,total₂]

theorem pair₁₃_eq : signal K X J h 0 ⊓ signal K X J h 2 = pairSpace K X J h 1 := by
  ext p
  constructor
  · rintro ⟨hp,hq⟩
    change p.2.1 = p.2.2.1 ∧ p.2.2.2.2 = 0 at hp
    change p.2.1 = p.1 + J p.1 ∧ p.2.2.2.1 + p.2.2.2.2 = h p.1 at hq
    have hv : p.2.2.2.1 = h p.1 := by simpa [hp.2] using hq.2
    refine ⟨p.1, ?_⟩
    change (p.1,p.1+J p.1,p.1+J p.1,h p.1,0) = p
    exact Prod.ext rfl (Prod.ext hq.1.symm (Prod.ext (hq.1.symm.trans hp.1) (Prod.ext hv.symm hp.2.symm)))
  · rintro ⟨w,rfl⟩
    simp [pairMap,signal,total₁,total₃]

theorem pair₂₃_eq : signal K X J h 1 ⊓ signal K X J h 2 = pairSpace K X J h 2 := by
  ext p
  constructor
  · rintro ⟨hp,hq⟩
    change p.1 = p.2.2.1 ∧ p.2.2.2.1 = 0 at hp
    change p.2.1 = p.1 + J p.1 ∧ p.2.2.2.1 + p.2.2.2.2 = h p.1 at hq
    have hr : p.2.2.2.2 = h p.1 := by simpa [hp.2] using hq.2
    refine ⟨p.1, ?_⟩
    change (p.1,p.1+J p.1,p.1,0,h p.1) = p
    exact Prod.ext rfl (Prod.ext hq.1.symm (Prod.ext hp.1 (Prod.ext hp.2.symm hr.symm)))
  · rintro ⟨w,rfl⟩
    simp [pairMap,signal,total₂,total₃]

theorem triple_eq_bot (hjoint : ∀ w : X, J w = 0 → h w = 0 → w = 0) :
    signal K X J h 0 ⊓ signal K X J h 1 ⊓ signal K X J h 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rintro p ⟨⟨hp,hq⟩,hr⟩
  change p.2.1 = p.2.2.1 ∧ p.2.2.2.2 = 0 at hp
  change p.1 = p.2.2.1 ∧ p.2.2.2.1 = 0 at hq
  change p.2.1 = p.1 + J p.1 ∧ p.2.2.2.1 + p.2.2.2.2 = h p.1 at hr
  have hj : J p.1 = 0 := by have he := hr.1; rw [hp.1, ← hq.1] at he; exact (add_eq_left.mp he.symm)
  have hh : h p.1 = 0 := by rw [← hr.2,hq.2,hp.2]; simp
  have hw := hjoint p.1 hj hh
  change p = 0
  refine Prod.ext hw ?_
  exact Prod.ext (hp.1.trans (hq.1.symm.trans hw)) (Prod.ext (hq.1.symm.trans hw) (Prod.ext hq.2 hp.2))

def demandMap : Fin 3 → (X →ₗ[K] Ambient K X) := ![demand₁ K X,demand₂ K X,demand₃ K X J h]

theorem signal_eq_side_sup_demand (i : Fin 3) : signal K X J h i =
    side K X i ⊔ LinearMap.range (demandMap K X J h i) := by
  fin_cases i
  · exact total₁_eq_side_sup_demand K X
  · exact total₂_eq_side_sup_demand K X
  · exact total₃_eq_side_sup_demand K X J h

theorem demand_injective (i : Fin 3) : Function.Injective (demandMap K X J h i) := by
  intro x y heq
  fin_cases i
  · simpa [demandMap,demand₁,E₂,E₃] using congrArg (fun p : Ambient K X => p.2.1) heq
  · simpa [demandMap,demand₂,demand₃,E₁,E₃] using congrArg (fun p : Ambient K X => p.1) heq
  · simpa [demandMap,demand₂,demand₃,E₁,E₃] using congrArg (fun p : Ambient K X => p.1) heq

theorem side_demand_disjoint (i : Fin 3) : side K X i ⊓ LinearMap.range (demandMap K X J h i) = ⊥ := by
  apply le_antisymm _ bot_le
  rintro p ⟨hp,⟨w,rfl⟩⟩
  have hw : w = 0 := by
    fin_cases i <;> simp [side,side₁,side₂,side₃,demandMap,demand₁,demand₂,demand₃,E₁,E₂,E₃] at hp <;> first | exact hp | exact hp.1
  subst w
  simp

variable [FiniteDimensional K X]
theorem demand_condRank (i : Fin 3) : condRank (signal K X J h i) (side K X i) = Module.finrank K X := by
  have hd := condRank_add_intersection (LinearMap.range (demandMap K X J h i)) (side K X i)
  rw [side_demand_disjoint, LinearMap.finrank_range_of_inj (demand_injective K X J h i)] at hd
  simp only [finrank_bot,add_zero] at hd
  rw [signal_eq_side_sup_demand]
  unfold condRank at *
  rw [← sup_assoc,sup_idem]
  exact hd

theorem induced_demand_condRank (m i : Fin 3) :
    condRank ((inducedTask K X J h m).U i) ((inducedTask K X J h m).A i) = Module.finrank K X := by
  change condRank (signal K X J h i ⊓ relay K X h m) (side K X i ⊓ relay K X h m) = _
  rw [relay_condRank _ _ _ (side_le_signal K X J h i) (relay_feasible K X J h m i), demand_condRank]

/-- The six incidences, written without relying on a claimed source pair-space formula. -/
def incident : Fin 3 → Fin 3 → Prop := fun b i =>
  (b=0 ∧ (i=0 ∨ i=1)) ∨ (b=1 ∧ (i=0 ∨ i=2)) ∨ (b=2 ∧ (i=1 ∨ i=2))

theorem side_pair_disjoint (hA : Function.Injective ((LinearMap.id : X →ₗ[K] X) + J))
    (b i : Fin 3) (hi : incident b i) : side K X i ⊓ pairSpace K X J h b = ⊥ := by
  apply le_antisymm _ bot_le
  rintro p ⟨hp,⟨w,rfl⟩⟩
  have hw : w = 0 := by
    fin_cases b <;> fin_cases i <;> simp [incident] at hi <;>
      simp [side,side₁,side₂,side₃,pairMap] at hp
    · exact hp
    · exact hp
    · exact hA (show ((LinearMap.id : X →ₗ[K] X) + J) w = ((LinearMap.id : X →ₗ[K] X) + J) 0 by simpa using hp)
    · exact hp.1
    · exact hp
    · exact hp.1
  subst w
  simp

theorem pair_condRank (hA : Function.Injective ((LinearMap.id : X →ₗ[K] X) + J))
    (b i : Fin 3) (hi : incident b i) : condRank (pairSpace K X J h b) (side K X i) = Module.finrank K X := by
  have hd := condRank_add_intersection (pairSpace K X J h b) (side K X i)
  rw [side_pair_disjoint K X J h hA b i hi] at hd
  simpa [pairSpace,LinearMap.finrank_range_of_inj (pairMap_injective K X J h b)] using hd


theorem pair_le_signal (b i : Fin 3) (hi : incident b i) : pairSpace K X J h b ≤ signal K X J h i := by
  rintro p ⟨w,rfl⟩
  fin_cases b <;> fin_cases i <;> simp [incident] at hi <;>
    simp [pairMap,signal,total₁,total₂,total₃]

theorem signal_le_side_pair (hA : Function.Surjective ((LinearMap.id : X →ₗ[K] X) + J))
    (b i : Fin 3) (hi : incident b i) : signal K X J h i ≤ side K X i ⊔ pairSpace K X J h b := by
  intro p hp
  have add_pair (w : X) (hw : p - pairMap K X J h b w ∈ side K X i) :
      p ∈ side K X i ⊔ pairSpace K X J h b :=
    Submodule.mem_sup.mpr ⟨_,hw,_,⟨w,rfl⟩,sub_add_cancel _ _⟩
  fin_cases b <;> fin_cases i <;> simp [incident] at hi
  · apply add_pair p.2.1
    change p.2.1 = p.2.2.1 ∧ p.2.2.2.2 = 0 at hp
    simp [pairMap,side,side₁,hp.1,hp.2]
  · apply add_pair p.1
    change p.1 = p.2.2.1 ∧ p.2.2.2.1 = 0 at hp
    simp [pairMap,side,side₂,hp.1,hp.2]
  · obtain ⟨w,hw⟩ := hA p.2.1
    change w + J w = p.2.1 at hw
    apply add_pair w
    change p.2.1 = p.2.2.1 ∧ p.2.2.2.2 = 0 at hp
    simp [pairMap,side,side₁,hw,hp.1,hp.2]
  · apply add_pair p.1
    change p.2.1 = p.1+J p.1 ∧ p.2.2.2.1+p.2.2.2.2 = h p.1 at hp
    simp [pairMap,side,side₃,hp.1]
    linear_combination hp.2
  · apply add_pair p.1
    change p.1 = p.2.2.1 ∧ p.2.2.2.1 = 0 at hp
    simp [pairMap,side,side₂,hp.1,hp.2]
  · apply add_pair p.1
    change p.2.1 = p.1+J p.1 ∧ p.2.2.2.1+p.2.2.2.2 = h p.1 at hp
    simp [pairMap,side,side₃,hp.1]
    linear_combination hp.2

def lostPair : Fin 3 → Fin 3 := ![2,1,0]

theorem pair_le_relay (m b : Fin 3) (hb : b ≠ lostPair m) : pairSpace K X J h b ≤ relay K X h m := by
  rintro p ⟨w,rfl⟩
  rw [relay_eq_kernel]
  fin_cases m <;> fin_cases b <;> simp [lostPair] at hb <;>
    simp [LinearMap.mem_ker,relayForm,pairMap]

/-- One unchanged incident pair suffices at each user for each menu. -/
def retainedPair : Fin 3 → Fin 3 → Fin 3 := ![![0,0,1],![0,2,2],![1,2,1]]

theorem retainedPair_incident (m i : Fin 3) : incident (retainedPair m i) i := by
  fin_cases m <;> fin_cases i <;> simp [retainedPair,incident]

theorem retainedPair_unchanged (m i : Fin 3) : retainedPair m i ≠ lostPair m := by
  fin_cases m <;> fin_cases i <;> decide

def incidentPairs (U : Fin 3 → Submodule K (Ambient K X)) (i : Fin 3) : Submodule K (Ambient K X) :=
  (U i ⊓ U (i+1)) ⊔ (U i ⊓ U (i+2))

theorem pair_le_incidentPairs (b i : Fin 3) (hi : incident b i) :
    pairSpace K X J h b ≤ incidentPairs K X (signal K X J h) i := by
  fin_cases b <;> fin_cases i <;> simp [incident] at hi
  all_goals simp only [incidentPairs]
  · change _ ≤ (signal K X J h 0 ⊓ signal K X J h 1) ⊔ (signal K X J h 0 ⊓ signal K X J h 2)
    rw [pair₁₂_eq]; exact le_sup_left
  · change _ ≤ (signal K X J h 1 ⊓ signal K X J h 2) ⊔ (signal K X J h 1 ⊓ signal K X J h 0)
    rw [inf_comm (signal K X J h 1) (signal K X J h 0), pair₁₂_eq]; exact le_sup_right
  · change _ ≤ (signal K X J h 0 ⊓ signal K X J h 1) ⊔ (signal K X J h 0 ⊓ signal K X J h 2)
    rw [pair₁₃_eq]; exact le_sup_right
  · change _ ≤ (signal K X J h 2 ⊓ signal K X J h 0) ⊔ (signal K X J h 2 ⊓ signal K X J h 1)
    rw [inf_comm (signal K X J h 2) (signal K X J h 0), pair₁₃_eq]; exact le_sup_left
  · change _ ≤ (signal K X J h 1 ⊓ signal K X J h 2) ⊔ (signal K X J h 1 ⊓ signal K X J h 0)
    rw [pair₂₃_eq]; exact le_sup_left
  · change _ ≤ (signal K X J h 2 ⊓ signal K X J h 0) ⊔ (signal K X J h 2 ⊓ signal K X J h 1)
    rw [inf_comm (signal K X J h 2) (signal K X J h 1), pair₂₃_eq]; exact le_sup_right

theorem signal_eq_side_retained (hA : Function.Surjective ((LinearMap.id : X →ₗ[K] X) + J)) (m i : Fin 3) :
    signal K X J h i = side K X i ⊔ pairSpace K X J h (retainedPair m i) :=
  le_antisymm (signal_le_side_pair K X J h hA _ _ (retainedPair_incident m i))
    (sup_le (side_le_signal K X J h i) (pair_le_signal K X J h _ _ (retainedPair_incident m i)))

theorem induced_signal_eq_side_retained (hA : Function.Surjective ((LinearMap.id : X →ₗ[K] X) + J)) (m i : Fin 3) :
    (inducedTask K X J h m).U i = (inducedTask K X J h m).A i ⊔ pairSpace K X J h (retainedPair m i) := by
  change signal K X J h i ⊓ _ = (side K X i ⊓ _) ⊔ _
  rw [signal_eq_side_retained K X J h hA m i,sup_comm,
    sup_inf_assoc_of_le _ (pair_le_relay K X J h m _ (retainedPair_unchanged m i)),sup_comm]

theorem induced_pair₁₂_eq (m : Fin 3) : (inducedTask K X J h m).U 0 ⊓ (inducedTask K X J h m).U 1 = pairSpace K X J h 0 ⊓ relay K X h m := by
  change (_ ⊓ _) ⊓ (_ ⊓ _) = _
  rw [inf_inf_inf_comm,inf_idem,pair₁₂_eq]
theorem induced_pair₁₃_eq (m : Fin 3) : (inducedTask K X J h m).U 0 ⊓ (inducedTask K X J h m).U 2 = pairSpace K X J h 1 ⊓ relay K X h m := by
  change (_ ⊓ _) ⊓ (_ ⊓ _) = _
  rw [inf_inf_inf_comm,inf_idem,pair₁₃_eq]
theorem induced_pair₂₃_eq (m : Fin 3) : (inducedTask K X J h m).U 1 ⊓ (inducedTask K X J h m).U 2 = pairSpace K X J h 2 ⊓ relay K X h m := by
  change (_ ⊓ _) ⊓ (_ ⊓ _) = _
  rw [inf_inf_inf_comm,inf_idem,pair₂₃_eq]

theorem pair_le_induced_incidentPairs (m b i : Fin 3) (hi : incident b i) :
    pairSpace K X J h b ⊓ relay K X h m ≤ incidentPairs K X (inducedTask K X J h m).U i := by
  fin_cases b <;> fin_cases i <;> simp [incident] at hi
  all_goals simp only [incidentPairs]
  · change _ ≤ ((inducedTask K X J h m).U 0 ⊓ (inducedTask K X J h m).U 1) ⊔ ((inducedTask K X J h m).U 0 ⊓ (inducedTask K X J h m).U 2)
    rw [induced_pair₁₂_eq]; exact le_sup_left
  · change _ ≤ ((inducedTask K X J h m).U 1 ⊓ (inducedTask K X J h m).U 2) ⊔ ((inducedTask K X J h m).U 1 ⊓ (inducedTask K X J h m).U 0)
    rw [inf_comm ((inducedTask K X J h m).U 1) ((inducedTask K X J h m).U 0), induced_pair₁₂_eq]; exact le_sup_right
  · change _ ≤ ((inducedTask K X J h m).U 0 ⊓ (inducedTask K X J h m).U 1) ⊔ ((inducedTask K X J h m).U 0 ⊓ (inducedTask K X J h m).U 2)
    rw [induced_pair₁₃_eq]; exact le_sup_right
  · change _ ≤ ((inducedTask K X J h m).U 2 ⊓ (inducedTask K X J h m).U 0) ⊔ ((inducedTask K X J h m).U 2 ⊓ (inducedTask K X J h m).U 1)
    rw [inf_comm ((inducedTask K X J h m).U 2) ((inducedTask K X J h m).U 0), induced_pair₁₃_eq]; exact le_sup_left
  · change _ ≤ ((inducedTask K X J h m).U 1 ⊓ (inducedTask K X J h m).U 2) ⊔ ((inducedTask K X J h m).U 1 ⊓ (inducedTask K X J h m).U 0)
    rw [induced_pair₂₃_eq]; exact le_sup_left
  · change _ ≤ ((inducedTask K X J h m).U 2 ⊓ (inducedTask K X J h m).U 0) ⊔ ((inducedTask K X J h m).U 2 ⊓ (inducedTask K X J h m).U 1)
    rw [inf_comm ((inducedTask K X J h m).U 2) ((inducedTask K X J h m).U 1), induced_pair₂₃_eq]; exact le_sup_right

theorem retained_le_induced_incidentPairs (m i : Fin 3) :
    pairSpace K X J h (retainedPair m i) ≤ incidentPairs K X (inducedTask K X J h m).U i := by
  have he := pair_le_induced_incidentPairs K X J h m _ i (retainedPair_incident m i)
  rw [inf_eq_left.mpr (pair_le_relay K X J h m _ (retainedPair_unchanged m i))] at he
  exact he


theorem full_pairSum_condRank (hA : Function.Surjective ((LinearMap.id : X →ₗ[K] X) + J)) (i : Fin 3) :
    condRank (incidentPairs K X (signal K X J h) i) (side K X i) = Module.finrank K X := by
  rw [CycleRepair.condRank_of_quotient_spanning K _ _ (pairSpace K X J h (retainedPair 0 i)) _
    (signal_eq_side_retained K X J h hA 0 i).symm
    (pair_le_incidentPairs K X J h _ _ (retainedPair_incident 0 i))
    (sup_le inf_le_left inf_le_left)]
  exact demand_condRank K X J h i

theorem full_branch_condRank (hA : Function.Surjective ((LinearMap.id : X →ₗ[K] X) + J)) (i : Fin 3) :
    condRank (signal K X J h i ⊓ (signal K X J h (i+1) ⊔ signal K X J h (i+2))) (side K X i) = Module.finrank K X := by
  rw [CycleRepair.condRank_of_quotient_spanning K _ _ (pairSpace K X J h (retainedPair 0 i)) _
    (signal_eq_side_retained K X J h hA 0 i).symm
    ((pair_le_incidentPairs K X J h _ _ (retainedPair_incident 0 i)).trans
      (CycleRepair.incidentPairs_le_branch K _ i)) inf_le_left]
  exact demand_condRank K X J h i

theorem induced_pairSum_condRank (hA : Function.Surjective ((LinearMap.id : X →ₗ[K] X) + J)) (m i : Fin 3) :
    condRank (incidentPairs K X (inducedTask K X J h m).U i) ((inducedTask K X J h m).A i) = Module.finrank K X := by
  rw [CycleRepair.condRank_of_quotient_spanning K _ _ (pairSpace K X J h (retainedPair m i)) _
    (induced_signal_eq_side_retained K X J h hA m i).symm
    (retained_le_induced_incidentPairs K X J h m i) (sup_le inf_le_left inf_le_left)]
  exact induced_demand_condRank K X J h m i

theorem induced_branch_condRank (hA : Function.Surjective ((LinearMap.id : X →ₗ[K] X) + J)) (m i : Fin 3) :
    condRank ((inducedTask K X J h m).U i ⊓ ((inducedTask K X J h m).U (i+1) ⊔ (inducedTask K X J h m).U (i+2)))
      ((inducedTask K X J h m).A i) = Module.finrank K X := by
  rw [CycleRepair.condRank_of_quotient_spanning K _ _ (pairSpace K X J h (retainedPair m i)) _
    (induced_signal_eq_side_retained K X J h hA m i).symm
    ((retained_le_induced_incidentPairs K X J h m i).trans (CycleRepair.incidentPairs_le_branch K _ i)) inf_le_left]
  exact induced_demand_condRank K X J h m i

theorem full_totalDemand : Profile.totalDemand (task K X J h) = 3 * Module.finrank K X :=
  CycleRepair.totalDemand_of_condRanks K _ _ (demand_condRank K X J h)

theorem induced_totalDemand (m : Fin 3) : Profile.totalDemand (inducedTask K X J h m) = 3 * Module.finrank K X :=
  CycleRepair.totalDemand_of_condRanks K _ _ (induced_demand_condRank K X J h m)

theorem induced_triple_eq_bot (hjoint : ∀ w : X, J w = 0 → h w = 0 → w = 0) (m : Fin 3) :
    (inducedTask K X J h m).U 0 ⊓ (inducedTask K X J h m).U 1 ⊓ (inducedTask K X J h m).U 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← triple_eq_bot K X J h hjoint]
  exact inf_le_inf (inf_le_inf inf_le_left inf_le_left) inf_le_left

theorem full_secondProfile (hA : Function.Surjective ((LinearMap.id : X →ₗ[K] X) + J))
    (hjoint : ∀ w : X, J w = 0 → h w = 0 → w = 0) (i l : Fin 3) :
    2 * Profile.entry (task K X J h) (.inr (i,l)) = 3 * (Module.finrank K X : ℝ) :=
  CycleRepair.secondProfile_formula K (task K X J h) _ (full_totalDemand K X J h)
    (triple_eq_bot K X J h hjoint) (full_pairSum_condRank K X J h hA) (full_branch_condRank K X J h hA) i l

theorem induced_secondProfile (hA : Function.Surjective ((LinearMap.id : X →ₗ[K] X) + J))
    (hjoint : ∀ w : X, J w = 0 → h w = 0 → w = 0) (m i l : Fin 3) :
    2 * Profile.entry (inducedTask K X J h m) (.inr (i,l)) = 3 * (Module.finrank K X : ℝ) :=
  CycleRepair.secondProfile_formula K (inducedTask K X J h m) _ (induced_totalDemand K X J h m)
    (induced_triple_eq_bot K X J h hjoint m) (induced_pairSum_condRank K X J h hA m) (induced_branch_condRank K X J h hA m) i l

theorem pair_restriction_rank (hh : Function.Surjective h) (m b : Fin 3) :
    Module.finrank K (LinearMap.range ((relayForm K X h m).comp (pairSpace K X J h b).subtype)) =
      if b = lostPair m then 1 else 0 := by
  have heq : LinearMap.range ((relayForm K X h m).comp (pairSpace K X J h b).subtype) =
      LinearMap.range ((relayForm K X h m).comp (pairMap K X J h b)) := by
    rw [LinearMap.range_comp,Submodule.range_subtype,pairSpace,LinearMap.range_comp]
  rw [heq]
  have hz (f : X →ₗ[K] K) (hf : f = 0) : Module.finrank K (LinearMap.range f) = 0 := by simp [hf]
  have ho (f : X →ₗ[K] K) (hf : Function.Surjective f) : Module.finrank K (LinearMap.range f) = 1 := by
    rw [LinearMap.range_eq_top.mpr hf]
    simp
  fin_cases m <;> fin_cases b <;> simp only [lostPair,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  · apply hz; ext w; simp [relayForm,pairMap]
  · apply hz; ext w; simp [relayForm,pairMap]
  · apply ho; intro t; obtain ⟨w,hw⟩ := hh t; exact ⟨w,by simpa [relayForm,pairMap] using hw⟩
  · apply hz; ext w; simp [relayForm,pairMap]
  · apply ho; intro t; obtain ⟨w,hw⟩ := hh t; exact ⟨w,by simpa [relayForm,pairMap] using hw⟩
  · apply hz; ext w; simp [relayForm,pairMap]
  · apply ho; intro t; obtain ⟨w,hw⟩ := hh (-t); exact ⟨w,by simp [relayForm,pairMap,hw]⟩
  · apply hz; ext w; simp [relayForm,pairMap]
  · apply hz; ext w; simp [relayForm,pairMap]

/-- The source pair spaces have exactly the private-block dimension. -/
theorem pair_finrank (b : Fin 3) : Module.finrank K (pairSpace K X J h b) = Module.finrank K X :=
  LinearMap.finrank_range_of_inj (pairMap_injective K X J h b)

/-- Exactly one pair loses one dimension in each relay menu. -/
theorem restricted_pair_finrank (hh : Function.Surjective h) (m b : Fin 3) :
    Module.finrank K ↥(pairSpace K X J h b ⊓ relay K X h m) =
      Module.finrank K X - if b = lostPair m then 1 else 0 := by
  have he := restriction_rank_add_kernel (relayForm K X h m) (pairSpace K X J h b)
  rw [← relay_eq_kernel,pair_restriction_rank K X J h hh m b,pair_finrank] at he
  omega

theorem induced_pair_condRank (hA : Function.Injective ((LinearMap.id : X →ₗ[K] X) + J))
    (hh : Function.Surjective h) (m b i : Fin 3) (hi : incident b i) :
    (condRank (pairSpace K X J h b ⊓ relay K X h m) (side K X i ⊓ relay K X h m) : ℝ) =
      (Module.finrank K X : ℝ) - if b = lostPair m then 1 else 0 := by
  have he := kernel_condRank_loss (relayForm K X h m) (pairSpace K X J h b) (side K X i)
  rw [← relay_eq_kernel, pair_condRank K X J h hA b i hi,
    pair_restriction_rank K X J h hh m b, side_pair_disjoint K X J h hA b i hi] at he
  have hz : LinearMap.range ((relayForm K X h m).comp (⊥ : Submodule K (Ambient K X)).subtype) = ⊥ := by
    simp [LinearMap.range_comp]
  rw [hz] at he
  simp only [finrank_bot,Int.natCast_zero,sub_zero] at he
  by_cases hb : b = lostPair m
  · subst b
    simp only [ite_true,Int.natCast_one] at he ⊢
    have he' : (Module.finrank K X : ℝ) - condRank (pairSpace K X J h (lostPair m) ⊓ relay K X h m) (side K X i ⊓ relay K X h m) = 1 := by exact_mod_cast he
    linarith
  · simp only [hb,ite_false,Int.natCast_zero] at he ⊢
    have he' : (Module.finrank K X : ℝ) - condRank (pairSpace K X J h b ⊓ relay K X h m) (side K X i ⊓ relay K X h m) = 0 := by exact_mod_cast he
    linarith


/-- Pair index used by each of the six source-order first-family entries. -/
def entryPair : Fin 6 → Fin 3 := ![0,1,0,2,1,2]

theorem ordered_branch_rank (T : Task K (Ambient K X)) (d : ℕ)
    (hb : ∀ i : Fin 3, condRank (T.U i ⊓ (T.U (i+1) ⊔ T.U (i+2))) (T.A i) = d)
    (r : Fin 6) :
    condRank (T.U (Profile.firstOrder r).2.2 ⊓
      (T.U (Profile.firstOrder r).1 ⊔ T.U (Profile.firstOrder r).2.1)) (T.A (Profile.firstOrder r).2.2) = d := by
  have b0 := hb 0
  have b1 := hb 1
  have b2 := hb 2
  change condRank (T.U 0 ⊓ (T.U 1 ⊔ T.U 2)) (T.A 0) = d at b0
  change condRank (T.U 1 ⊓ (T.U 2 ⊔ T.U 0)) (T.A 1) = d at b1
  change condRank (T.U 2 ⊓ (T.U 0 ⊔ T.U 1)) (T.A 2) = d at b2
  fin_cases r
  · exact b2
  · change condRank (T.U 1 ⊓ (T.U 0 ⊔ T.U 2)) (T.A 1) = d
    simpa only [sup_comm] using b1
  · change condRank (T.U 2 ⊓ (T.U 1 ⊔ T.U 0)) (T.A 2) = d
    simpa only [sup_comm] using b2
  · exact b0
  · exact b1
  · change condRank (T.U 0 ⊓ (T.U 2 ⊔ T.U 1)) (T.A 0) = d
    simpa only [sup_comm] using b0

theorem firstProfile_formula (T : Task K (Ambient K X)) (d : ℕ)
    (ht : Profile.totalDemand T = 3*d)
    (hb : ∀ i : Fin 3, condRank (T.U i ⊓ (T.U (i+1) ⊔ T.U (i+2))) (T.A i) = d)
    (r : Fin 6) : Profile.entry T (.inl r) = 2*(d : ℝ) -
      condRank (T.U (Profile.firstOrder r).1 ⊓ T.U (Profile.firstOrder r).2.1) (T.A (Profile.firstOrder r).2.1) :=
  CycleRepair.firstEntry_formula K T d ht _ _ _ (ordered_branch_rank K X T d hb r)

theorem full_ordered_pairRank (hA : Function.Injective ((LinearMap.id : X →ₗ[K] X) + J)) (r : Fin 6) :
    (condRank ((task K X J h).U (Profile.firstOrder r).1 ⊓ (task K X J h).U (Profile.firstOrder r).2.1)
      ((task K X J h).A (Profile.firstOrder r).2.1) : ℝ) = (Module.finrank K X : ℝ) := by
  fin_cases r
  · change (condRank (signal K X J h 0 ⊓ signal K X J h 1) (side K X 1) : ℝ) = _
    rw [pair₁₂_eq]
    exact_mod_cast pair_condRank K X J h hA 0 1 (by simp [incident])
  · change (condRank (signal K X J h 0 ⊓ signal K X J h 2) (side K X 2) : ℝ) = _
    rw [pair₁₃_eq]
    exact_mod_cast pair_condRank K X J h hA 1 2 (by simp [incident])
  · change (condRank (signal K X J h 1 ⊓ signal K X J h 0) (side K X 0) : ℝ) = _
    rw [inf_comm (signal K X J h 1) (signal K X J h 0)]
    rw [pair₁₂_eq]
    exact_mod_cast pair_condRank K X J h hA 0 0 (by simp [incident])
  · change (condRank (signal K X J h 1 ⊓ signal K X J h 2) (side K X 2) : ℝ) = _
    rw [pair₂₃_eq]
    exact_mod_cast pair_condRank K X J h hA 2 2 (by simp [incident])
  · change (condRank (signal K X J h 2 ⊓ signal K X J h 0) (side K X 0) : ℝ) = _
    rw [inf_comm (signal K X J h 2) (signal K X J h 0)]
    rw [pair₁₃_eq]
    exact_mod_cast pair_condRank K X J h hA 1 0 (by simp [incident])
  · change (condRank (signal K X J h 2 ⊓ signal K X J h 1) (side K X 1) : ℝ) = _
    rw [inf_comm (signal K X J h 2) (signal K X J h 1)]
    rw [pair₂₃_eq]
    exact_mod_cast pair_condRank K X J h hA 2 1 (by simp [incident])

theorem full_firstProfile (hA : Function.Bijective ((LinearMap.id : X →ₗ[K] X) + J)) (r : Fin 6) :
    Profile.entry (task K X J h) (.inl r) = (Module.finrank K X : ℝ) := by
  rw [firstProfile_formula K X _ _ (full_totalDemand K X J h) (full_branch_condRank K X J h hA.2),
    full_ordered_pairRank K X J h hA.1]
  ring

theorem induced_ordered_pairRank (hA : Function.Injective ((LinearMap.id : X →ₗ[K] X) + J))
    (hh : Function.Surjective h) (m : Fin 3) (r : Fin 6) :
    (condRank ((inducedTask K X J h m).U (Profile.firstOrder r).1 ⊓ (inducedTask K X J h m).U (Profile.firstOrder r).2.1)
      ((inducedTask K X J h m).A (Profile.firstOrder r).2.1) : ℝ) =
        (Module.finrank K X : ℝ) - if entryPair r = lostPair m then 1 else 0 := by
  fin_cases r
  · change (condRank ((inducedTask K X J h m).U 0 ⊓ (inducedTask K X J h m).U 1) (side K X 1 ⊓ relay K X h m) : ℝ) = (Module.finrank K X : ℝ) - if (0:Fin 3) = lostPair m then 1 else 0
    rw [induced_pair₁₂_eq]
    exact induced_pair_condRank K X J h hA hh m 0 1 (by simp [incident])
  · change (condRank ((inducedTask K X J h m).U 0 ⊓ (inducedTask K X J h m).U 2) (side K X 2 ⊓ relay K X h m) : ℝ) = (Module.finrank K X : ℝ) - if (1:Fin 3) = lostPair m then 1 else 0
    rw [induced_pair₁₃_eq]
    exact induced_pair_condRank K X J h hA hh m 1 2 (by simp [incident])
  · change (condRank ((inducedTask K X J h m).U 1 ⊓ (inducedTask K X J h m).U 0) (side K X 0 ⊓ relay K X h m) : ℝ) = (Module.finrank K X : ℝ) - if (0:Fin 3) = lostPair m then 1 else 0
    rw [inf_comm ((inducedTask K X J h m).U 1) ((inducedTask K X J h m).U 0)]
    rw [induced_pair₁₂_eq]
    exact induced_pair_condRank K X J h hA hh m 0 0 (by simp [incident])
  · change (condRank ((inducedTask K X J h m).U 1 ⊓ (inducedTask K X J h m).U 2) (side K X 2 ⊓ relay K X h m) : ℝ) = (Module.finrank K X : ℝ) - if (2:Fin 3) = lostPair m then 1 else 0
    rw [induced_pair₂₃_eq]
    exact induced_pair_condRank K X J h hA hh m 2 2 (by simp [incident])
  · change (condRank ((inducedTask K X J h m).U 2 ⊓ (inducedTask K X J h m).U 0) (side K X 0 ⊓ relay K X h m) : ℝ) = (Module.finrank K X : ℝ) - if (1:Fin 3) = lostPair m then 1 else 0
    rw [inf_comm ((inducedTask K X J h m).U 2) ((inducedTask K X J h m).U 0)]
    rw [induced_pair₁₃_eq]
    exact induced_pair_condRank K X J h hA hh m 1 0 (by simp [incident])
  · change (condRank ((inducedTask K X J h m).U 2 ⊓ (inducedTask K X J h m).U 1) (side K X 1 ⊓ relay K X h m) : ℝ) = (Module.finrank K X : ℝ) - if (2:Fin 3) = lostPair m then 1 else 0
    rw [inf_comm ((inducedTask K X J h m).U 2) ((inducedTask K X J h m).U 1)]
    rw [induced_pair₂₃_eq]
    exact induced_pair_condRank K X J h hA hh m 2 1 (by simp [incident])

theorem induced_firstProfile (hA : Function.Bijective ((LinearMap.id : X →ₗ[K] X) + J))
    (hh : Function.Surjective h) (m : Fin 3) (r : Fin 6) :
    Profile.entry (inducedTask K X J h m) (.inl r) =
      (Module.finrank K X : ℝ) + if entryPair r = lostPair m then 1 else 0 := by
  rw [firstProfile_formula K X _ _ (induced_totalDemand K X J h m) (induced_branch_condRank K X J h hA.2 m),
    induced_ordered_pairRank K X J h hA.1 hh]
  ring

/-- Exactly e₄+e₆, e₂+e₅, e₁+e₃, in relay order V,R,T. -/
def increment : Fin 3 → Fin 6 → ℝ := ![![0,0,0,1,0,1],![0,1,0,0,1,0],![1,0,1,0,0,0]]

theorem increment_eq (m : Fin 3) (r : Fin 6) :
    increment m r = if entryPair r = lostPair m then 1 else 0 := by
  fin_cases m <;> fin_cases r <;> norm_num [increment,entryPair,lostPair,Fin.ext_iff]

theorem exact_menu_increments (hA : Function.Bijective ((LinearMap.id : X →ₗ[K] X) + J))
    (hh : Function.Surjective h) (m : Fin 3) (r : Fin 6) :
    Profile.entry (inducedTask K X J h m) (.inl r) - Profile.entry (task K X J h) (.inl r) = increment m r := by
  rw [induced_firstProfile K X J h hA hh,full_firstProfile K X J h hA,increment_eq]
  ring


section Jordan
variable (K : Type*) [Field K] (n : ℕ)

/-- Parameter n means the manuscript's positive block size n+1. -/
abbrev jordanTask := task K (JordanResonance.V K n) (JordanResonance.shift K n) (JordanResonance.head K n)
abbrev jordanInducedTask (m : Fin 3) := inducedTask K (JordanResonance.V K n) (JordanResonance.shift K n) (JordanResonance.head K n) m
abbrev jordanRelay (m : Fin 3) := relay K (JordanResonance.V K n) (JordanResonance.head K n) m

theorem jordan_joint (w : JordanResonance.V K n) (hw : JordanResonance.shift K n w = 0)
    (hh : JordanResonance.head K n w = 0) : w = 0 := by
  apply JordanResonance.fixed_head_eq_zero K n w _ hh
  change w + JordanResonance.shift K n w = w
  rw [hw,add_zero]

theorem jordan_bijective : Function.Bijective
    ((LinearMap.id : JordanResonance.V K n →ₗ[K] JordanResonance.V K n) + JordanResonance.shift K n) :=
  ⟨JordanResonance.automorphism_injective K n,JordanResonance.automorphism_surjective K n⟩

theorem jordan_menu_construction (m : Fin 3) :
    (jordanTask K n).LocallyGenerated (jordanRelay K n m) ∧
    (jordanTask K n).RelayFeasible (jordanRelay K n m) ∧
    Module.finrank K (jordanRelay K n m) = 3*(n+1)+1 := by
  refine ⟨relay_locally_generated K _ _ m,relay_feasible K _ _ _ m,?_⟩
  simpa [JordanResonance.V,Module.finrank_pi] using relay_finrank K (JordanResonance.V K n) (JordanResonance.head K n) m

theorem jordan_full_firstProfile (r : Fin 6) :
    Profile.entry (jordanTask K n) (.inl r) = (n : ℝ)+1 := by
  simpa [JordanResonance.V,Module.finrank_pi] using
    full_firstProfile K _ _ _ (jordan_bijective K n) r

theorem jordan_full_secondProfile (i l : Fin 3) :
    2 * Profile.entry (jordanTask K n) (.inr (i,l)) = 3*((n : ℝ)+1) := by
  simpa [JordanResonance.V,Module.finrank_pi] using
    full_secondProfile K _ _ _ (jordan_bijective K n).2 (jordan_joint K n) i l

theorem jordan_induced_firstProfile (m : Fin 3) (r : Fin 6) :
    Profile.entry (jordanInducedTask K n m) (.inl r) = (n : ℝ)+1 + increment m r := by
  rw [increment_eq]
  simpa [JordanResonance.V,Module.finrank_pi] using
    induced_firstProfile K _ _ _ (jordan_bijective K n) (JordanResonance.head_surjective K n) m r

theorem jordan_induced_secondProfile (m i l : Fin 3) :
    2 * Profile.entry (jordanInducedTask K n m) (.inr (i,l)) = 3*((n : ℝ)+1) := by
  simpa [JordanResonance.V,Module.finrank_pi] using
    induced_secondProfile K _ _ _ (jordan_bijective K n).2 (jordan_joint K n) m i l

/-- Original manuscript indexing, valid over every field, including characteristic two. -/
theorem every_positive_length (hn : 0 < n) (m : Fin 3) :
    (jordanTask K (n-1)).LocallyGenerated (jordanRelay K (n-1) m) ∧
    (jordanTask K (n-1)).RelayFeasible (jordanRelay K (n-1) m) ∧
    Module.finrank K (jordanRelay K (n-1) m) = 3*n+1 ∧
    (∀ r : Fin 6, Profile.entry (jordanTask K (n-1)) (.inl r) = (n : ℝ)) ∧
    (∀ i l : Fin 3, 2 * Profile.entry (jordanTask K (n-1)) (.inr (i,l)) = 3*(n : ℝ)) ∧
    (∀ r : Fin 6, Profile.entry (jordanInducedTask K (n-1) m) (.inl r) = (n : ℝ) + increment m r) ∧
    (∀ i l : Fin 3, 2 * Profile.entry (jordanInducedTask K (n-1) m) (.inr (i,l)) = 3*(n : ℝ)) := by
  have hn' : n-1+1 = n := Nat.sub_add_cancel hn
  have hr : ((n-1 : ℕ) : ℝ)+1 = n := by exact_mod_cast hn'
  obtain ⟨hl,hf,hd⟩ := jordan_menu_construction K (n-1) m
  refine ⟨hl,hf,by simpa only [hn'] using hd,?_,?_,?_,?_⟩
  · intro r; simpa only [hr] using jordan_full_firstProfile K (n-1) r
  · intro i l; simpa only [hr] using jordan_full_secondProfile K (n-1) i l
  · intro r; simpa only [hr] using jordan_induced_firstProfile K (n-1) m r
  · intro i l; simpa only [hr] using jordan_induced_secondProfile K (n-1) m i l

end Jordan
end UploadBroadcast.ResonantRelay
