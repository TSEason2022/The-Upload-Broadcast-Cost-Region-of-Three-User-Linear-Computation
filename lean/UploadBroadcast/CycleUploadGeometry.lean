import UploadBroadcast.CycleDirectSumCoordinates
import UploadBroadcast.ResidualComponentAdditivity
import UploadBroadcast.RelayLinearComposition

/-! Operational optimality for the literal scalar demand-cycle repairs.
The converse is proved from their original coefficient geometry. -/
namespace UploadBroadcast.CycleUploadOptimality
open Module CycleRepair ResidualComponentAdditivity
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable (K : Type*) [Field K] (n : ℕ)

private theorem actual_task_ext {F : Type*} [AddCommGroup F] [Module K F]
    {T S : Task K F} (ha : T.A=S.A) (hu : T.U=S.U) : T=S := by
  cases T
  cases S
  cases ha
  cases hu
  rfl

private theorem sideMap_injective (i : Three) : Function.Injective (sideMap K n i) := by
  intro a b h
  apply Prod.ext
  · fin_cases i
    · exact congrArg (fun p : Ambient K n => p.1 0) h
    · exact congrArg (fun p : Ambient K n => p.1 1) h
    · exact congrArg (fun p : Ambient K n => p.1 2) h
  · apply Prod.ext
    · fin_cases i
      · exact congrArg (fun p : Ambient K n => p.2 0) h
      · exact congrArg (fun p : Ambient K n => p.2 1) h
      · exact congrArg (fun p : Ambient K n => p.2 1) h
    · fin_cases i
      · exact congrArg (fun p : Ambient K n => p.2 4) h
      · exact congrArg (fun p : Ambient K n => p.2 3) h
      · exact congrArg (fun p : Ambient K n => p.2 2) h

theorem side_finrank (i : Three) : finrank K (side K n i)=n+2 := by
  rw [side,LinearMap.finrank_range_of_inj (sideMap_injective K n i)]
  simp [Vec,Module.finrank_pi]

theorem sides_disjoint (i j : Three) (hij : i≠j) :
    Disjoint (side K n i) (side K n j) := by
  have h01 : Disjoint (side K n 0) (side K n 1) := by
    rw [disjoint_iff]
    apply eq_bot_iff.mpr
    intro p hp
    have ha := (side₁_mem K n p).mp hp.1
    have hb := (side₂_mem K n p).mp hp.2
    clear hp
    change p=0
    apply Prod.ext <;> funext k <;> fin_cases k <;> simp_all
  have h02 : Disjoint (side K n 0) (side K n 2) := by
    rw [disjoint_iff]
    apply eq_bot_iff.mpr
    intro p hp
    have ha := (side₁_mem K n p).mp hp.1
    have hb := (side₃_mem K n p).mp hp.2
    clear hp
    change p=0
    apply Prod.ext <;> funext k <;> fin_cases k <;> simp_all
  have h12 : Disjoint (side K n 1) (side K n 2) := by
    rw [disjoint_iff]
    apply eq_bot_iff.mpr
    intro p hp
    have ha := (side₂_mem K n p).mp hp.1
    have hb := (side₃_mem K n p).mp hp.2
    clear hp
    change p=0
    apply Prod.ext <;> funext k <;> fin_cases k <;> simp_all
  fin_cases i <;> fin_cases j <;> first
    | contradiction | exact h01 | exact h02 | exact h12
    | exact h01.symm | exact h02.symm | exact h12.symm

variable (A : Vec K n →ₗ[K] Vec K n) (H : Vec K n →ₗ[K] K)

theorem signal_finrank (i : Three) : finrank K (signal K n A H i)=2*n+3 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (side K n i)
    (LinearMap.range (demandMap K n A H i))
  rw [side_demand_disjoint,finrank_bot,add_zero,side_finrank,demandMap_finrank] at h
  change finrank K ↥(side K n i ⊔ LinearMap.range (demandMap K n A H i))=2*n+3
  omega

theorem pair_spanning (i j : Three) (hij : i≠j) :
    signal K n A H i ⊔ signal K n A H j=⊤ := by
  have hf : finrank K (Ambient K n)=3*n+5 := by
    simp [Ambient,Vec,Module.finrank_pi,Module.finrank_pi_fintype]
  have h01 : finrank K ↥(signal K n A H 0 ⊓ signal K n A H 1)=n+1 := by
    rw [pair₁₂_eq,pairMap_finrank]
  have h02 : finrank K ↥(signal K n A H 0 ⊓ signal K n A H 2)=n+1 := by
    rw [pair₁₃_eq,pairMap_finrank]
  have h12 : finrank K ↥(signal K n A H 1 ⊓ signal K n A H 2)=n+1 := by
    rw [pair₂₃_eq,pairMap_finrank]
  have hp : finrank K ↥(signal K n A H i ⊓ signal K n A H j)=n+1 := by
    fin_cases i <;> fin_cases j <;> try contradiction
    · exact h01
    · exact h02
    · rw [inf_comm]; exact h01
    · exact h12
    · rw [inf_comm]; exact h02
    · rw [inf_comm]; exact h12
  apply Submodule.eq_top_of_finrank_eq
  have hh := Submodule.finrank_sup_add_finrank_inf_eq (signal K n A H i) (signal K n A H j)
  rw [signal_finrank,signal_finrank,hp] at hh
  omega

/-- The single scalar tripod row has an explicit signed zero-private witness. -/
theorem tripod_bridge (w : Vec K n) (hw : A w=w) (hh : H w=1) :
    side K n 0 ⊓ (side K n 1 ⊔ side K n 2) ≤
      signal K n A H 2 ⊔ (signal K n A H 0 ⊓ signal K n A H 1) := by
  intro p hp
  have hp0 := (side₁_mem K n p).mp hp.1
  obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp hp.2
  have ha' := (side₂_mem K n a).mp ha
  have hb' := (side₃_mem K n b).mp hb
  have hprivate : p.1 0=0 := by
    have he' := congrArg (fun p : Ambient K n => p.1 0) he
    simpa [ha'.1,hb'.1] using he'.symm
  have hz : p.2 4=0 := by
    have he' := congrArg (fun p : Ambient K n => p.2 4) he
    simpa [ha'.2.2.2.2,hb'.2.2.2.2] using he'.symm
  let v := (p.2 0) • w
  let q : Ambient K n := (![v,v,v],![0,0,0,0,0])
  have hv : A v=v := by simp [v,hw]
  have hH : H v=p.2 0 := by simp [v,hh]
  have hq : q ∈ signal K n A H 0 ⊓ signal K n A H 1 := by
    constructor
    · apply (signal₁_mem K n A H q).mpr; simp [q]
    · apply (signal₂_mem K n A H q).mpr; simp [q]
  have hu : p+q ∈ signal K n A H 2 := by
    rw [signal₃_mem]
    simp [q,hprivate,hp0.1,hp0.2.1,hp0.2.2.1,hp0.2.2.2.1,hp0.2.2.2.2,hz,hv,hH]
  have hh' := (signal K n A H 2 ⊔ (signal K n A H 0 ⊓ signal K n A H 1)).sub_mem
    (Submodule.mem_sup_left hu) (Submodule.mem_sup_right hq)
  simpa only [add_sub_cancel_right] using hh'

/-- All activity hypotheses are consequences of the explicit cycle geometry. -/
theorem task_active (w : Vec K n) (hw : A w=w) (hh : H w=1)
    (hjoint : ∀ v : Vec K n, A v=v → H v=0 → v=0) :
    ActiveResidual (task K n A H) := by
  constructor
  · exact sides_disjoint K n 0 1 (by decide)
  · exact sides_disjoint K n 0 2 (by decide)
  · exact sides_disjoint K n 1 2 (by decide)
  · simpa only [Profile.three_iSup] using side_spanning K n
  · exact pair_spanning K n A H
  · exact tripod_bridge K n A H w hw hh
  · unfold commonSeed
    change (side K n 0 ⊓ (signal K n A H 0 ⊓ signal K n A H 1 ⊓ signal K n A H 2)) ⊓ _=⊥
    rw [triple_eq_bot K n A H hjoint,inf_bot_eq,bot_inf_eq]

theorem task_uploadValue : uploadValue (task K n A H)=(3*n+4 : ℕ) := by
  unfold uploadValue
  change 2*(finrank K (Ambient K n) : ℝ)-
    (finrank K (side K n 0)+finrank K (side K n 1)+finrank K (side K n 2))=_
  have hf : finrank K (Ambient K n)=3*n+5 := by
    simp [Ambient,Vec,Module.finrank_pi,Module.finrank_pi_fintype]
  rw [hf,side_finrank,side_finrank,side_finrank]
  push_cast
  ring

end UploadBroadcast.CycleUploadOptimality
