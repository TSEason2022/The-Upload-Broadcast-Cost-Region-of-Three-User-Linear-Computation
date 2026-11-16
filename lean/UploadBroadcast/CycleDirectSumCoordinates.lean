import UploadBroadcast.CycleTheorem
import UploadBroadcast.CycleReverseTheorem
import UploadBroadcast.ResonantProfile
import UploadBroadcast.ProfileTransport

namespace UploadBroadcast.CycleDirectSumCoordinates
open CycleRepair
variable (K : Type*) [Field K]

def side₀ : Submodule K (Three → K) where
  carrier := {x | x 0=0 ∧ x 2=0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simp_all
  smul_mem' := by intro a b hb; simp_all

def side₁ : Submodule K (Three → K) where
  carrier := {x | x 0=0 ∧ x 1=0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simp_all
  smul_mem' := by intro a b hb; simp_all

def side₂ : Submodule K (Three → K) where
  carrier := {x | x 1=0 ∧ x 2=0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simp_all
  smul_mem' := by intro a b hb; simp_all

def sides : Three → Submodule K (Three → K) := ![side₀ K,side₁ K,side₂ K]
def signals (i : Three) : Submodule K (Three → K) := LinearMap.ker (LinearMap.proj i)

theorem sides_span : (⨆ i, sides K i)=⊤ := by
  apply top_unique
  intro x _
  have he : x = ![0,x 1,0]+![0,0,x 2]+![x 0,0,0] := by
    funext i; fin_cases i <;> simp
  rw [he]
  exact Submodule.add_mem _ (Submodule.add_mem _
    ((le_iSup (sides K) 0) (by change _=0 ∧ _=0; simp))
    ((le_iSup (sides K) 1) (by change _=0 ∧ _=0; simp)))
    ((le_iSup (sides K) 2) (by change _=0 ∧ _=0; simp))

/-- Scalar directed cycle, edge order third-user 0,1,2. -/
def cycleTask : Task K (Three → K) where
  A := sides K
  U := signals K
  side_le_signal i := by
    intro x hx
    fin_cases i
    · exact hx.1
    · exact hx.2
    · exact hx.2
  feasible i := by rw [sides_span]; exact le_top

variable (n : ℕ)

/-- Pure coordinate regrouping between a resonant block plus three directed
edges and the manuscript's positive-cycle repair coordinates. -/
def coordinates :
    (ResonantEndomorphisms.Ambient K (Vec K n) × (Three → K)) ≃ₗ[K] Ambient K n where
  toFun p := (![p.1.1,p.1.2.1,p.1.2.2.1],
    ![p.1.2.2.2.1,p.1.2.2.2.2,p.2 0,p.2 2,p.2 1])
  invFun p := ((p.1 0,p.1 1,p.1 2,p.2 0,p.2 1),![p.2 2,p.2 4,p.2 3])
  left_inv p := by
    apply Prod.ext
    · rfl
    · funext i; fin_cases i <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  map_add' p q := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  map_smul' a p := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl

theorem side₀_mem (p : Ambient K n) : p ∈ side K n 0 ↔
    p.1 1=0 ∧ p.1 2=0 ∧ p.2 1=0 ∧ p.2 2=0 ∧ p.2 3=0 := by
  constructor
  · rintro ⟨x,rfl⟩
    simp [sideMap]
  · rintro ⟨h₁,h₂,hR,hx,hy⟩
    refine ⟨(p.1 0,p.2 0,p.2 4),?_⟩
    apply Prod.ext
    · funext i; fin_cases i <;> simp [sideMap,h₁,h₂]
    · funext i; fin_cases i <;> simp [sideMap,hR,hx,hy]

theorem side₁_mem (p : Ambient K n) : p ∈ side K n 1 ↔
    p.1 0=0 ∧ p.1 2=0 ∧ p.2 0=0 ∧ p.2 2=0 ∧ p.2 4=0 := by
  constructor
  · rintro ⟨x,rfl⟩
    simp [sideMap]
  · rintro ⟨h₀,h₂,hV,hx,hz⟩
    refine ⟨(p.1 1,p.2 1,p.2 3),?_⟩
    apply Prod.ext
    · funext i; fin_cases i <;> simp [sideMap,h₀,h₂]
    · funext i; fin_cases i <;> simp [sideMap,hV,hx,hz]

theorem side₂_mem (p : Ambient K n) : p ∈ side K n 2 ↔
    p.1 0=0 ∧ p.1 1=0 ∧ p.2 0+p.2 1=0 ∧ p.2 3=0 ∧ p.2 4=0 := by
  constructor
  · rintro ⟨x,rfl⟩
    simp [sideMap]
  · rintro ⟨h₀,h₁,hVR,hy,hz⟩
    refine ⟨(p.1 2,p.2 1,p.2 2),?_⟩
    apply Prod.ext
    · funext i; fin_cases i <;> simp [sideMap,h₀,h₁]
    · funext i; fin_cases i <;> simp [sideMap,hy,hz]
      exact neg_eq_iff_add_eq_zero.mpr (by simpa only [add_comm] using hVR)

/-- The canonical positive repair really is the direct sum of the original
resonant task and a physical positive demand cycle. -/
theorem map_directSum (J : Vec K n →ₗ[K] Vec K n) (h : Vec K n →ₗ[K] K) :
    Profile.mapTask (coordinates K n)
      (Profile.directSum (ResonantRelay.task K (Vec K n) J h) (cycleTask K)) =
      CycleRepair.task K n (LinearMap.id+J) h := by
  have ha : (Profile.mapTask (coordinates K n)
      (Profile.directSum (ResonantRelay.task K (Vec K n) J h) (cycleTask K))).A =
      (CycleRepair.task K n (LinearMap.id+J) h).A := by
    funext i
    ext p
    change p ∈ ((ResonantRelay.side K (Vec K n) i).prod (sides K i)).map
      (coordinates K n).toLinearMap ↔ p ∈ side K n i
    rw [Submodule.mem_map_equiv]
    fin_cases i
    · change _ ↔ p ∈ side K n 0
      rw [side₀_mem K n p]
      change ((_ = 0 ∧ _ = 0 ∧ _ = 0) ∧ (_ = 0 ∧ _ = 0)) ↔ _
      simp only [coordinates]
      tauto
    · change _ ↔ p ∈ side K n 1
      rw [side₁_mem K n p]
      change ((_ = 0 ∧ _ = 0 ∧ _ = 0) ∧ (_ = 0 ∧ _ = 0)) ↔ _
      simp only [coordinates]
      tauto
    · change _ ↔ p ∈ side K n 2
      rw [side₂_mem K n p]
      change ((_ = 0 ∧ _ = 0 ∧ _ + _ = 0) ∧ (_ = 0 ∧ _ = 0)) ↔ _
      simp only [coordinates]
      tauto
  have hu : (Profile.mapTask (coordinates K n)
      (Profile.directSum (ResonantRelay.task K (Vec K n) J h) (cycleTask K))).U =
      (CycleRepair.task K n (LinearMap.id+J) h).U := by
    funext i
    ext p
    change p ∈ ((ResonantRelay.signal K (Vec K n) J h i).prod (signals K i)).map
      (coordinates K n).toLinearMap ↔ p ∈ signal K n (LinearMap.id+J) h i
    rw [Submodule.mem_map_equiv]
    fin_cases i
    · change _ ↔ p ∈ signal K n (LinearMap.id+J) h 0
      rw [signal₁_mem K n (LinearMap.id+J) h p]
      change ((_ = _ ∧ _ = 0) ∧ _ = 0) ↔ _
      simp [coordinates,and_assoc]
    · change _ ↔ p ∈ signal K n (LinearMap.id+J) h 1
      rw [signal₂_mem K n (LinearMap.id+J) h p]
      change ((_ = _ ∧ _ = 0) ∧ _ = 0) ↔ _
      simp [coordinates,and_assoc]
    · change _ ↔ p ∈ signal K n (LinearMap.id+J) h 2
      rw [signal₃_mem K n (LinearMap.id+J) h p]
      change ((_ = _ + _ ∧ _ + _ = _) ∧ _ = 0) ↔ _
      simp [coordinates,and_assoc]
  cases h₁ : Profile.mapTask (coordinates K n)
      (Profile.directSum (ResonantRelay.task K (Vec K n) J h) (cycleTask K))
  cases h₂ : CycleRepair.task K n (LinearMap.id+J) h
  simp_all only [Task.mk.injEq]

/-- The opposite directed cycle, on the same source-side coordinates. -/
def reverseCycleTask : Task K (Three → K) where
  A := sides K
  U := ![signals K 2,signals K 0,signals K 1]
  side_le_signal i := by
    intro x hx
    fin_cases i
    · exact hx.2
    · exact hx.1
    · exact hx.1
  feasible i := by rw [sides_span]; exact le_top

/-- Public membership signature for the literal reverse-cycle demand rows. -/
theorem reverse_signal_membership (A : Vec K n →ₗ[K] Vec K n)
    (H : Vec K n →ₗ[K] K) (i : Three) (p : Ambient K n) :
    p ∈ reverseSignal K n A H i ↔
      (![p.1 1 = p.1 2 ∧ p.2 1 = 0 ∧ p.2 3 = 0,
         p.1 0 = p.1 2 ∧ p.2 0 = 0 ∧ p.2 2 = 0,
         p.1 1 = A (p.1 0) ∧ p.2 0 + p.2 1 = H (p.1 0) ∧ p.2 4 = 0] i) := by
  constructor
  · intro hp
    obtain ⟨a,⟨oa,rfl⟩,b,⟨ob,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hp
    fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail,sideMap,reverseDemandMap]
  · intro hp
    fin_cases i
    · refine Submodule.mem_sup.mpr ⟨sideMap K n 0 (p.1 0,p.2 0,p.2 4),⟨_,rfl⟩,
        reverseDemandMap K n A H 0 (p.1 1,p.2 2),⟨_,rfl⟩,?_⟩
      simp only [Matrix.cons_val_zero] at hp
      apply Prod.ext <;> funext j <;> fin_cases j <;>
        simp [Matrix.vecHead,Matrix.vecTail,sideMap,reverseDemandMap,hp.1,hp.2.1,hp.2.2]
    · refine Submodule.mem_sup.mpr ⟨sideMap K n 1 (p.1 1,p.2 1,p.2 3),⟨_,rfl⟩,
        reverseDemandMap K n A H 1 (p.1 0,p.2 4),⟨_,rfl⟩,?_⟩
      simp only [Matrix.cons_val_one,Matrix.cons_val_zero] at hp
      apply Prod.ext <;> funext j <;> fin_cases j <;>
        simp [Matrix.vecHead,Matrix.vecTail,sideMap,reverseDemandMap,hp.1,hp.2.1,hp.2.2]
    · refine Submodule.mem_sup.mpr ⟨sideMap K n 2 (p.1 2,p.2 1,p.2 2),⟨_,rfl⟩,
        reverseDemandMap K n A H 2 (p.1 0,p.2 3),⟨_,rfl⟩,?_⟩
      simp only [Matrix.cons_val_two,Matrix.cons_val_one,Matrix.cons_val_zero] at hp
      apply Prod.ext
      · funext j; fin_cases j <;> simp [Matrix.vecHead,Matrix.vecTail,sideMap,reverseDemandMap,hp.1]
      · funext j; fin_cases j <;> simp [Matrix.vecHead,Matrix.vecTail,sideMap,reverseDemandMap,hp.2.2]
        linear_combination -hp.2.1

/-- Exact coordinate identity for the reverse demand cycle with the original
resonant block, without an assumed symmetry or inverse-Jordan classification. -/
theorem map_reverseDirectSum (J : Vec K n →ₗ[K] Vec K n) (h : Vec K n →ₗ[K] K) :
    Profile.mapTask (coordinates K n)
      (Profile.directSum (ResonantRelay.task K (Vec K n) J h) (reverseCycleTask K)) =
      CycleRepair.reverseTask K n (LinearMap.id+J) h := by
  have ha : (Profile.mapTask (coordinates K n)
      (Profile.directSum (ResonantRelay.task K (Vec K n) J h) (reverseCycleTask K))).A =
      (CycleRepair.reverseTask K n (LinearMap.id+J) h).A := by
    have hh := congrArg (fun T : Task K (Ambient K n) => T.A) (map_directSum K n J h)
    exact hh
  have hu : (Profile.mapTask (coordinates K n)
      (Profile.directSum (ResonantRelay.task K (Vec K n) J h) (reverseCycleTask K))).U =
      (CycleRepair.reverseTask K n (LinearMap.id+J) h).U := by
    funext i
    ext p
    change p ∈ ((ResonantRelay.signal K (Vec K n) J h i).prod
      (![signals K 2,signals K 0,signals K 1] i)).map
      (coordinates K n).toLinearMap ↔ p ∈ reverseSignal K n (LinearMap.id+J) h i
    rw [Submodule.mem_map_equiv,reverse_signal_membership]
    fin_cases i <;>
      simp [ResonantRelay.signal,ResonantEndomorphisms.total₁,ResonantEndomorphisms.total₂,
        ResonantEndomorphisms.total₃,signals,coordinates,and_assoc]
  cases h₁ : Profile.mapTask (coordinates K n)
      (Profile.directSum (ResonantRelay.task K (Vec K n) J h) (reverseCycleTask K))
  cases h₂ : CycleRepair.reverseTask K n (LinearMap.id+J) h
  simp_all only [Task.mk.injEq]

end UploadBroadcast.CycleDirectSumCoordinates
