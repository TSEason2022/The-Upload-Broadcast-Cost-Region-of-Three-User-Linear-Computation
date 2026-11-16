import UploadBroadcast.CycleRepair
import UploadBroadcast.Profile
import UploadBroadcast.LinearAlgebra
import UploadBroadcast.RankLoss

/-! Exact subspace computations for the demand-cycle repair construction. -/
set_option maxHeartbeats 800000

namespace UploadBroadcast.CycleRepair
variable (K : Type*) [Field K] (n : ℕ)
variable (A : Vec K n →ₗ[K] Vec K n) (H : Vec K n →ₗ[K] K)

theorem signal₁_mem (p : Ambient K n) :
    p ∈ signal K n A H 0 ↔ p.1 1 = p.1 2 ∧ p.2 1 = 0 ∧ p.2 2 = 0 := by
  constructor
  · intro hp
    obtain ⟨a, ⟨oa, rfl⟩, b, ⟨ob, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hp
    simp [Matrix.vecHead, Matrix.vecTail, sideMap, demandMap]
  · rintro ⟨hvec, hr, hx⟩
    refine Submodule.mem_sup.mpr ⟨sideMap K n 0 (p.1 0, p.2 0, p.2 4),
      ⟨_, rfl⟩, demandMap K n A H 0 (p.1 1, p.2 3), ⟨_, rfl⟩, ?_⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, demandMap, hvec]
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, demandMap, hr, hx]

theorem signal₂_mem (p : Ambient K n) :
    p ∈ signal K n A H 1 ↔ p.1 0 = p.1 2 ∧ p.2 0 = 0 ∧ p.2 4 = 0 := by
  constructor
  · intro hp
    obtain ⟨a, ⟨oa, rfl⟩, b, ⟨ob, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hp
    simp [Matrix.vecHead, Matrix.vecTail, sideMap, demandMap]
  · rintro ⟨hvec, hv, hz⟩
    refine Submodule.mem_sup.mpr ⟨sideMap K n 1 (p.1 1, p.2 1, p.2 3),
      ⟨_, rfl⟩, demandMap K n A H 1 (p.1 0, p.2 2), ⟨_, rfl⟩, ?_⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, demandMap, hvec]
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, demandMap, hv, hz]

theorem signal₃_mem (p : Ambient K n) :
    p ∈ signal K n A H 2 ↔ p.1 1 = A (p.1 0) ∧ p.2 0 + p.2 1 = H (p.1 0) ∧ p.2 3 = 0 := by
  constructor
  · intro hp
    obtain ⟨a, ⟨oa, rfl⟩, b, ⟨ob, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hp
    simp [Matrix.vecHead, Matrix.vecTail, sideMap, demandMap]
  · rintro ⟨hvec, hvr, hy⟩
    refine Submodule.mem_sup.mpr ⟨sideMap K n 2 (p.1 2, p.2 1, p.2 2),
      ⟨_, rfl⟩, demandMap K n A H 2 (p.1 0, p.2 4), ⟨_, rfl⟩, ?_⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, demandMap, hvec]
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, demandMap, hy]
      linear_combination -hvr

/-- Pair-space parametrizations in the order 12, 13, 23. -/
def pairMap (i : Fin 3) : (Vec K n × K) →ₗ[K] Ambient K n where
  toFun o := (![![o.1, o.1, o.1], ![o.1, A o.1, A o.1], ![o.1, A o.1, o.1]] i,
    ![![0, 0, 0, o.2, 0], ![H o.1, 0, 0, 0, o.2], ![0, H o.1, o.2, 0, 0]] i)
  map_add' := by
    intro p q
    apply Prod.ext
    · funext j
      fin_cases i <;> fin_cases j <;> simp
    · funext j
      fin_cases i <;> fin_cases j <;> simp
  map_smul' := by
    intro c p
    apply Prod.ext
    · funext j
      fin_cases i <;> fin_cases j <;> simp
    · funext j
      fin_cases i <;> fin_cases j <;> simp

theorem pairMap_injective (i : Fin 3) : Function.Injective (pairMap K n A H i) := by
  intro p q heq
  apply Prod.ext
  · have h := congrArg (fun v : Ambient K n => v.1 0) heq
    fin_cases i <;> simpa [pairMap] using h
  · have h := congrArg (fun v : Ambient K n => v.2) heq
    fin_cases i
    · exact congrFun h 3
    · exact congrFun h 4
    · exact congrFun h 2

theorem pairMap_finrank (i : Fin 3) :
    Module.finrank K (LinearMap.range (pairMap K n A H i)) = n + 1 := by
  rw [LinearMap.finrank_range_of_inj (pairMap_injective K n A H i)]
  simp [Vec, Module.finrank_prod, Module.finrank_pi]

theorem pair₁₂_eq : signal K n A H 0 ⊓ signal K n A H 1 =
    LinearMap.range (pairMap K n A H 0) := by
  ext p
  constructor
  · rintro ⟨hp₁, hp₂⟩
    obtain ⟨hv₁, hr, hx⟩ := (signal₁_mem K n A H p).mp hp₁
    obtain ⟨hv₂, hv, hz⟩ := (signal₂_mem K n A H p).mp hp₂
    refine ⟨(p.1 0, p.2 3), ?_⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, pairMap, hv₁, hv₂]
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, pairMap, hr, hx, hv, hz]
  · rintro ⟨o, rfl⟩
    constructor
    · apply (signal₁_mem K n A H _).mpr
      simp [Matrix.vecHead, Matrix.vecTail, pairMap]
    · apply (signal₂_mem K n A H _).mpr
      simp [Matrix.vecHead, Matrix.vecTail, pairMap]

theorem pair₁₃_eq : signal K n A H 0 ⊓ signal K n A H 2 =
    LinearMap.range (pairMap K n A H 1) := by
  ext p
  constructor
  · rintro ⟨hp₁, hp₃⟩
    obtain ⟨hv₁, hr, hx⟩ := (signal₁_mem K n A H p).mp hp₁
    obtain ⟨hv₃, hvr, hy⟩ := (signal₃_mem K n A H p).mp hp₃
    have hv : p.2 0 = H (p.1 0) := by simpa [hr] using hvr
    refine ⟨(p.1 0, p.2 4), ?_⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, pairMap, ← hv₃, hv₁]
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, pairMap, hr, hx, hv, hy]
  · rintro ⟨o, rfl⟩
    constructor
    · apply (signal₁_mem K n A H _).mpr
      simp [Matrix.vecHead, Matrix.vecTail, pairMap]
    · apply (signal₃_mem K n A H _).mpr
      simp [Matrix.vecHead, Matrix.vecTail, pairMap]

theorem pair₂₃_eq : signal K n A H 1 ⊓ signal K n A H 2 =
    LinearMap.range (pairMap K n A H 2) := by
  ext p
  constructor
  · rintro ⟨hp₂, hp₃⟩
    obtain ⟨hv₂, hv, hz⟩ := (signal₂_mem K n A H p).mp hp₂
    obtain ⟨hv₃, hvr, hy⟩ := (signal₃_mem K n A H p).mp hp₃
    have hr : p.2 1 = H (p.1 0) := by simpa [hv] using hvr
    refine ⟨(p.1 0, p.2 2), ?_⟩
    apply Prod.ext
    · funext i
      fin_cases i
      · rfl
      · exact hv₃.symm
      · exact hv₂
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, pairMap, hr, hz, hv, hy]
  · rintro ⟨o, rfl⟩
    constructor
    · apply (signal₂_mem K n A H _).mpr
      simp [Matrix.vecHead, Matrix.vecTail, pairMap]
    · apply (signal₃_mem K n A H _).mpr
      simp [Matrix.vecHead, Matrix.vecTail, pairMap]

/-- The precise resonant hypothesis used to eliminate the triple intersection. -/
theorem triple_eq_bot
    (hjoint : ∀ w : Vec K n, A w = w → H w = 0 → w = 0) :
    (signal K n A H 0 ⊓ signal K n A H 1) ⊓ signal K n A H 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rintro p ⟨⟨hp₁, hp₂⟩, hp₃⟩
  obtain ⟨hv₁, hr, hx⟩ := (signal₁_mem K n A H p).mp hp₁
  obtain ⟨hv₂, hv, hz⟩ := (signal₂_mem K n A H p).mp hp₂
  obtain ⟨hv₃, hvr, hy⟩ := (signal₃_mem K n A H p).mp hp₃
  have hw : p.1 0 = 0 := hjoint _ (by rw [← hv₃, hv₁, ← hv₂])
    (by rw [← hvr, hv, hr]; simp)
  change p = 0
  apply Prod.ext
  · funext i
    fin_cases i
    · exact hw
    · exact hv₁.trans (hv₂.symm.trans hw)
    · exact hv₂.symm.trans hw
  · funext i
    fin_cases i <;> simp [hr, hx, hv, hz, hy]

theorem side₁_mem (p : Ambient K n) :
    p ∈ side K n 0 ↔ p.1 1 = 0 ∧ p.1 2 = 0 ∧ p.2 1 = 0 ∧ p.2 2 = 0 ∧ p.2 3 = 0 := by
  constructor
  · rintro ⟨o, rfl⟩
    simp [Matrix.vecHead, Matrix.vecTail, sideMap]
  · rintro ⟨h₁, h₂, hr, hx, hy⟩
    refine ⟨(p.1 0, p.2 0, p.2 4), ?_⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, h₁, h₂]
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, hr, hx, hy]

theorem side₂_mem (p : Ambient K n) :
    p ∈ side K n 1 ↔ p.1 0 = 0 ∧ p.1 2 = 0 ∧ p.2 0 = 0 ∧ p.2 2 = 0 ∧ p.2 4 = 0 := by
  constructor
  · rintro ⟨o, rfl⟩
    simp [Matrix.vecHead, Matrix.vecTail, sideMap]
  · rintro ⟨h₁, h₂, hv, hx, hz⟩
    refine ⟨(p.1 1, p.2 1, p.2 3), ?_⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, h₁, h₂]
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, hv, hx, hz]

theorem side₃_mem (p : Ambient K n) :
    p ∈ side K n 2 ↔ p.1 0 = 0 ∧ p.1 1 = 0 ∧ p.2 0 + p.2 1 = 0 ∧ p.2 3 = 0 ∧ p.2 4 = 0 := by
  constructor
  · rintro ⟨o, rfl⟩
    simp [Matrix.vecHead, Matrix.vecTail, sideMap]
  · rintro ⟨h₁, h₂, hvr, hy, hz⟩
    refine ⟨(p.1 2, p.2 1, p.2 2), ?_⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, h₁, h₂]
    · funext i
      fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, sideMap, hy, hz]
      linear_combination -hvr

def scalarMap (j : Fin 5) : K →ₗ[K] Ambient K n where
  toFun t := (0, fun i => if i = j then t else 0)
  map_add' := by
    intro p q
    apply Prod.ext
    · simp
    · funext i
      by_cases hij : i = j <;> simp [hij]
  map_smul' := by
    intro c p
    apply Prod.ext
    · simp
    · funext i
      by_cases hij : i = j <;> simp [hij]

theorem scalarMap_injective (j : Fin 5) : Function.Injective (scalarMap K n j) := by
  intro p q hpq
  simpa [scalarMap] using congrArg (fun v : Ambient K n => v.2 j) hpq

theorem scalarMap_finrank (j : Fin 5) : Module.finrank K (LinearMap.range (scalarMap K n j)) = 1 := by
  rw [LinearMap.finrank_range_of_inj (scalarMap_injective K n j)]
  simp

def pairScalarIndex : Fin 3 → Fin 5 := ![3, 4, 2]

theorem pairMap_zero_scalar (i : Fin 3) (t : K) :
    pairMap K n A H i (0, t) = scalarMap K n (pairScalarIndex i) t := by
  apply Prod.ext
  · funext j
    fin_cases i <;> fin_cases j <;> simp [Matrix.vecHead, Matrix.vecTail, pairMap, scalarMap]
  · funext j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecHead, Matrix.vecTail, pairMap, scalarMap, pairScalarIndex]

/-- The three side/pair intersections that contain the cycle coordinate. -/
theorem side₁_pair₁₃ (hA : Function.Injective A) :
    side K n 0 ⊓ LinearMap.range (pairMap K n A H 1) =
      LinearMap.range (scalarMap K n 4) := by
  ext p
  constructor
  · rintro ⟨ha, ⟨⟨w, t⟩, rfl⟩⟩
    have hh := (side₁_mem K n _).mp ha
    have haw : A w = 0 := by simpa [pairMap] using hh.1
    have hw : w = 0 := hA (haw.trans A.map_zero.symm)
    subst w
    exact ⟨t, (pairMap_zero_scalar K n A H 1 t).symm⟩
  · rintro ⟨t, rfl⟩
    constructor
    · apply (side₁_mem K n _).mpr
      simp [Matrix.vecHead, Matrix.vecTail, scalarMap]
    · exact ⟨(0, t), pairMap_zero_scalar K n A H 1 t⟩

theorem side₂_pair₁₂ :
    side K n 1 ⊓ LinearMap.range (pairMap K n A H 0) =
      LinearMap.range (scalarMap K n 3) := by
  ext p
  constructor
  · rintro ⟨ha, ⟨⟨w, t⟩, rfl⟩⟩
    have hh := (side₂_mem K n _).mp ha
    have hw : w = 0 := by simpa [pairMap] using hh.1
    subst w
    exact ⟨t, (pairMap_zero_scalar K n A H 0 t).symm⟩
  · rintro ⟨t, rfl⟩
    constructor
    · apply (side₂_mem K n _).mpr
      simp [Matrix.vecHead, Matrix.vecTail, scalarMap]
    · exact ⟨(0, t), pairMap_zero_scalar K n A H 0 t⟩

theorem side₃_pair₂₃ :
    side K n 2 ⊓ LinearMap.range (pairMap K n A H 2) =
      LinearMap.range (scalarMap K n 2) := by
  ext p
  constructor
  · rintro ⟨ha, ⟨⟨w, t⟩, rfl⟩⟩
    have hh := (side₃_mem K n _).mp ha
    have hw : w = 0 := by simpa [pairMap] using hh.1
    subst w
    exact ⟨t, (pairMap_zero_scalar K n A H 2 t).symm⟩
  · rintro ⟨t, rfl⟩
    constructor
    · apply (side₃_mem K n _).mpr
      simp [Matrix.vecHead, Matrix.vecTail, scalarMap]
    · exact ⟨(0, t), pairMap_zero_scalar K n A H 2 t⟩

/-- The other three incident side/pair intersections are zero. -/
theorem side₁_pair₁₂ : side K n 0 ⊓ LinearMap.range (pairMap K n A H 0) = ⊥ := by
  apply le_antisymm _ bot_le
  rintro p ⟨ha, ⟨⟨w, t⟩, rfl⟩⟩
  have hh := (side₁_mem K n _).mp ha
  have hw : w = 0 := by simpa [pairMap] using hh.1
  have ht : t = 0 := by simpa [pairMap] using hh.2.2.2.2
  subst w; subst t
  simp

theorem side₃_pair₁₃ : side K n 2 ⊓ LinearMap.range (pairMap K n A H 1) = ⊥ := by
  apply le_antisymm _ bot_le
  rintro p ⟨ha, ⟨⟨w, t⟩, rfl⟩⟩
  have hh := (side₃_mem K n _).mp ha
  have hw : w = 0 := by simpa [pairMap] using hh.1
  have ht : t = 0 := by simpa [pairMap] using hh.2.2.2.2
  subst w; subst t
  simp

theorem side₂_pair₂₃ : side K n 1 ⊓ LinearMap.range (pairMap K n A H 2) = ⊥ := by
  apply le_antisymm _ bot_le
  rintro p ⟨ha, ⟨⟨w, t⟩, rfl⟩⟩
  have hh := (side₂_mem K n _).mp ha
  have hw : w = 0 := by simpa [pairMap] using hh.1
  have ht : t = 0 := by simpa [pairMap] using hh.2.2.2.1
  subst w; subst t
  simp

theorem pair_condRanks (hA : Function.Injective A) :
    condRank (LinearMap.range (pairMap K n A H 0)) (side K n 0) = n + 1 ∧
    condRank (LinearMap.range (pairMap K n A H 0)) (side K n 1) = n ∧
    condRank (LinearMap.range (pairMap K n A H 1)) (side K n 0) = n ∧
    condRank (LinearMap.range (pairMap K n A H 1)) (side K n 2) = n + 1 ∧
    condRank (LinearMap.range (pairMap K n A H 2)) (side K n 1) = n + 1 ∧
    condRank (LinearMap.range (pairMap K n A H 2)) (side K n 2) = n := by
  have h₁ := condRank_add_intersection (LinearMap.range (pairMap K n A H 0)) (side K n 0)
  have h₂ := condRank_add_intersection (LinearMap.range (pairMap K n A H 0)) (side K n 1)
  have h₃ := condRank_add_intersection (LinearMap.range (pairMap K n A H 1)) (side K n 0)
  have h₄ := condRank_add_intersection (LinearMap.range (pairMap K n A H 1)) (side K n 2)
  have h₅ := condRank_add_intersection (LinearMap.range (pairMap K n A H 2)) (side K n 1)
  have h₆ := condRank_add_intersection (LinearMap.range (pairMap K n A H 2)) (side K n 2)
  rw [side₁_pair₁₂, pairMap_finrank] at h₁
  rw [side₂_pair₁₂, scalarMap_finrank, pairMap_finrank] at h₂
  rw [side₁_pair₁₃ K n A H hA, scalarMap_finrank, pairMap_finrank] at h₃
  rw [side₃_pair₁₃, pairMap_finrank] at h₄
  rw [side₂_pair₂₃, pairMap_finrank] at h₅
  rw [side₃_pair₂₃, scalarMap_finrank, pairMap_finrank] at h₆
  simp only [finrank_bot, add_zero] at h₁ h₄ h₅
  exact ⟨h₁, by omega, by omega, h₄, h₅, by omega⟩

theorem demandMap_injective (i : Fin 3) : Function.Injective (demandMap K n A H i) := by
  intro p q heq
  apply Prod.ext
  · fin_cases i
    · exact congrArg (fun v : Ambient K n => v.1 1) heq
    · exact congrArg (fun v : Ambient K n => v.1 0) heq
    · exact congrArg (fun v : Ambient K n => v.1 0) heq
  · fin_cases i
    · exact congrArg (fun v : Ambient K n => v.2 3) heq
    · exact congrArg (fun v : Ambient K n => v.2 2) heq
    · exact congrArg (fun v : Ambient K n => v.2 4) heq

theorem demandMap_finrank (i : Fin 3) :
    Module.finrank K (LinearMap.range (demandMap K n A H i)) = n + 1 := by
  rw [LinearMap.finrank_range_of_inj (demandMap_injective K n A H i)]
  simp [Vec, Module.finrank_prod, Module.finrank_pi]

theorem side_demand_disjoint (i : Fin 3) :
    side K n i ⊓ LinearMap.range (demandMap K n A H i) = ⊥ := by
  apply le_antisymm _ bot_le
  rintro p ⟨ha, ⟨⟨w, t⟩, rfl⟩⟩
  fin_cases i
  · have hh := (side₁_mem K n _).mp ha
    have hw : w = 0 := by simpa [demandMap] using hh.1
    have ht : t = 0 := by simpa [demandMap] using hh.2.2.2.2
    subst w; subst t; simp
  · have hh := (side₂_mem K n _).mp ha
    have hw : w = 0 := by simpa [demandMap] using hh.1
    have ht : t = 0 := by simpa [demandMap] using hh.2.2.2.1
    subst w; subst t; simp
  · have hh := (side₃_mem K n _).mp ha
    have hw : w = 0 := by simpa [demandMap] using hh.1
    have ht : t = 0 := by simpa [demandMap] using hh.2.2.2.2
    subst w; subst t; simp

theorem demand_condRank (i : Fin 3) : condRank (signal K n A H i) (side K n i) = n + 1 := by
  have hd := condRank_add_intersection (LinearMap.range (demandMap K n A H i)) (side K n i)
  rw [side_demand_disjoint, demandMap_finrank] at hd
  simp only [finrank_bot, add_zero] at hd
  unfold condRank signal
  rw [← sup_assoc, sup_idem]
  exact hd

theorem induced_demand_condRank (i : Fin 3) :
    condRank (signal K n A H i ⊓ LinearMap.range (relayMap K n))
      (side K n i ⊓ LinearMap.range (relayMap K n)) = n + 1 := by
  rw [relay_condRank (side K n i) (signal K n A H i) (LinearMap.range (relayMap K n))
    le_sup_left (relay_feasible K n A H i), demand_condRank]

theorem range_restrict_range {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : Ambient K n →ₗ[K] W) (g : V →ₗ[K] Ambient K n) :
    LinearMap.range (f.comp (LinearMap.range g).subtype) = LinearMap.range (f.comp g) := by
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.range_comp]

theorem pair_restriction_rank (i : Fin 3) :
    Module.finrank K (LinearMap.range ((relayForm K n).comp (LinearMap.range (pairMap K n A H i)).subtype)) =
      if i = 1 then 1 else 0 := by
  rw [range_restrict_range]
  fin_cases i
  · have heq : (relayForm K n).comp (pairMap K n A H 0) = 0 := by
      apply LinearMap.ext
      intro o
      simp [relayForm, pairMap]
    simp [heq]
  · have hsurj : Function.Surjective ((relayForm K n).comp (pairMap K n A H 1)) := by
      intro t
      refine ⟨(0, t), ?_⟩
      simp [relayForm, pairMap]
    change Module.finrank K (LinearMap.range ((relayForm K n).comp (pairMap K n A H 1))) = 1
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp
  · have heq : (relayForm K n).comp (pairMap K n A H 2) = 0 := by
      apply LinearMap.ext
      intro o
      simp [relayForm, pairMap]
    simp [heq]

theorem scalar_restriction_rank (j : Fin 5) :
    Module.finrank K (LinearMap.range ((relayForm K n).comp (LinearMap.range (scalarMap K n j)).subtype)) =
      if j = 0 ∨ j = 4 then 1 else 0 := by
  rw [range_restrict_range]
  by_cases hj : j = 0 ∨ j = 4
  · have hsurj : Function.Surjective ((relayForm K n).comp (scalarMap K n j)) := by
      intro t
      refine ⟨t, ?_⟩
      rcases hj with rfl | rfl <;> simp [relayForm, scalarMap]
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp [hj]
  · have heq : (relayForm K n).comp (scalarMap K n j) = 0 := by
      apply LinearMap.ext
      intro t
      simp [relayForm, scalarMap, Ne.symm (fun h => hj (Or.inl h)), Ne.symm (fun h => hj (Or.inr h))]
    simp [heq, hj]

/-- All six incident conditional pair ranks after positive-cycle repair. -/
theorem induced_pair_condRanks (hA : Function.Injective A) :
    condRank (LinearMap.range (pairMap K n A H 0) ⊓ LinearMap.range (relayMap K n))
      (side K n 0 ⊓ LinearMap.range (relayMap K n)) = n + 1 ∧
    condRank (LinearMap.range (pairMap K n A H 0) ⊓ LinearMap.range (relayMap K n))
      (side K n 1 ⊓ LinearMap.range (relayMap K n)) = n ∧
    condRank (LinearMap.range (pairMap K n A H 1) ⊓ LinearMap.range (relayMap K n))
      (side K n 0 ⊓ LinearMap.range (relayMap K n)) = n ∧
    condRank (LinearMap.range (pairMap K n A H 1) ⊓ LinearMap.range (relayMap K n))
      (side K n 2 ⊓ LinearMap.range (relayMap K n)) = n ∧
    condRank (LinearMap.range (pairMap K n A H 2) ⊓ LinearMap.range (relayMap K n))
      (side K n 1 ⊓ LinearMap.range (relayMap K n)) = n + 1 ∧
    condRank (LinearMap.range (pairMap K n A H 2) ⊓ LinearMap.range (relayMap K n))
      (side K n 2 ⊓ LinearMap.range (relayMap K n)) = n := by
  obtain ⟨f₁, f₂, f₃, f₄, f₅, f₆⟩ := pair_condRanks K n A H hA
  have h₁ := kernel_condRank_loss (relayForm K n) (LinearMap.range (pairMap K n A H 0)) (side K n 0)
  have h₂ := kernel_condRank_loss (relayForm K n) (LinearMap.range (pairMap K n A H 0)) (side K n 1)
  have h₃ := kernel_condRank_loss (relayForm K n) (LinearMap.range (pairMap K n A H 1)) (side K n 0)
  have h₄ := kernel_condRank_loss (relayForm K n) (LinearMap.range (pairMap K n A H 1)) (side K n 2)
  have h₅ := kernel_condRank_loss (relayForm K n) (LinearMap.range (pairMap K n A H 2)) (side K n 1)
  have h₆ := kernel_condRank_loss (relayForm K n) (LinearMap.range (pairMap K n A H 2)) (side K n 2)
  rw [side₁_pair₁₂, pair_restriction_rank, f₁] at h₁
  rw [side₂_pair₁₂, pair_restriction_rank, scalar_restriction_rank, f₂] at h₂
  rw [side₁_pair₁₃ K n A H hA, pair_restriction_rank, scalar_restriction_rank, f₃] at h₃
  rw [side₃_pair₁₃, pair_restriction_rank, f₄] at h₄
  rw [side₂_pair₂₃, pair_restriction_rank, f₅] at h₅
  rw [side₃_pair₂₃, pair_restriction_rank, scalar_restriction_rank, f₆] at h₆
  simp only [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_bot, finrank_bot,
    Fin.reduceEq, if_true, if_false, Nat.cast_zero, Nat.cast_one,
    or_self, false_or, or_true, true_or] at h₁ h₂ h₃ h₄ h₅ h₆
  have hbot : Module.finrank K (LinearMap.range ((relayForm K n).comp
      (⊥ : Submodule K (Ambient K n)).subtype)) = 0 := by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_bot]
    simp
  rw [hbot] at h₁ h₄ h₅
  simp only [relay_range_eq_kernel]
  omega

/-- Sum of the two incident pair subspaces, already restricted to the relay. -/
def repairedPairs (i : Fin 3) : Submodule K (Ambient K n) :=
  ![(LinearMap.range (pairMap K n A H 0) ⊓ LinearMap.range (relayMap K n)) ⊔
      (LinearMap.range (pairMap K n A H 1) ⊓ LinearMap.range (relayMap K n)),
    (LinearMap.range (pairMap K n A H 0) ⊓ LinearMap.range (relayMap K n)) ⊔
      (LinearMap.range (pairMap K n A H 2) ⊓ LinearMap.range (relayMap K n)),
    (LinearMap.range (pairMap K n A H 1) ⊓ LinearMap.range (relayMap K n)) ⊔
      (LinearMap.range (pairMap K n A H 2) ⊓ LinearMap.range (relayMap K n))] i

theorem repairedPairs_le_signal (i : Fin 3) : repairedPairs K n A H i ≤ signal K n A H i := by
  fin_cases i
  · change (_ ⊓ _) ⊔ (_ ⊓ _) ≤ _
    rw [← pair₁₂_eq, ← pair₁₃_eq]
    exact sup_le (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_left)
  · change (_ ⊓ _) ⊔ (_ ⊓ _) ≤ _
    rw [← pair₁₂_eq, ← pair₂₃_eq]
    exact sup_le (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)
  · change (_ ⊓ _) ⊔ (_ ⊓ _) ≤ _
    rw [← pair₁₃_eq, ← pair₂₃_eq]
    exact sup_le (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_right)

theorem repairedPairs_le_relay (i : Fin 3) :
    repairedPairs K n A H i ≤ LinearMap.range (relayMap K n) := by
  fin_cases i <;> exact sup_le inf_le_right inf_le_right

theorem demand_le_side_repairedPairs (hH : Function.Surjective H) (i : Fin 3) :
    LinearMap.range (demandMap K n A H i) ≤ side K n i ⊔ repairedPairs K n A H i := by
  rintro p ⟨⟨w, t⟩, rfl⟩
  fin_cases i
  · let b := pairMap K n A H 0 (w, t)
    have hb : b ∈ repairedPairs K n A H 0 := by
      apply Submodule.mem_sup_left
      constructor
      · exact ⟨(w, t), rfl⟩
      · rw [relay_range_eq_kernel]
        simp [b, pairMap, relayForm, LinearMap.mem_ker]
    refine Submodule.mem_sup.mpr ⟨sideMap K n 0 (-w, 0, 0), ⟨_, rfl⟩, b, hb, ?_⟩
    apply Prod.ext
    · funext j
      fin_cases j <;> simp [Matrix.vecHead, Matrix.vecTail, b, sideMap, pairMap, demandMap]
    · funext j
      fin_cases j <;> simp [Matrix.vecHead, Matrix.vecTail, b, sideMap, pairMap, demandMap]
  · let b := pairMap K n A H 2 (w, t)
    have hb : b ∈ repairedPairs K n A H 1 := by
      apply Submodule.mem_sup_right
      constructor
      · exact ⟨(w, t), rfl⟩
      · rw [relay_range_eq_kernel]
        simp [b, pairMap, relayForm, LinearMap.mem_ker]
    refine Submodule.mem_sup.mpr ⟨sideMap K n 1 (-(A w), -(H w), 0), ⟨_, rfl⟩, b, hb, ?_⟩
    apply Prod.ext
    · funext j
      fin_cases j <;> simp [Matrix.vecHead, Matrix.vecTail, b, sideMap, pairMap, demandMap]
    · funext j
      fin_cases j <;> simp [Matrix.vecHead, Matrix.vecTail, b, sideMap, pairMap, demandMap]
  · obtain ⟨q, hq⟩ := hH (-t)
    let b := pairMap K n A H 1 (q, t)
    let c := pairMap K n A H 2 (w-q, 0)
    have hb : b ∈ LinearMap.range (pairMap K n A H 1) ⊓ LinearMap.range (relayMap K n) := by
      constructor
      · exact ⟨(q, t), rfl⟩
      · rw [relay_range_eq_kernel]
        simp [b, pairMap, relayForm, LinearMap.mem_ker, hq]
    have hc : c ∈ LinearMap.range (pairMap K n A H 2) ⊓ LinearMap.range (relayMap K n) := by
      constructor
      · exact ⟨(w-q, 0), rfl⟩
      · rw [relay_range_eq_kernel]
        simp [c, pairMap, relayForm, LinearMap.mem_ker]
    have hbc : b+c ∈ repairedPairs K n A H 2 :=
      Submodule.mem_sup.mpr ⟨b, hb, c, hc, rfl⟩
    let a := sideMap K n 2 (-(A q + (w-q)), -(H (w-q)), 0)
    refine Submodule.mem_sup.mpr ⟨a, ⟨_, rfl⟩, b+c, hbc, ?_⟩
    apply Prod.ext
    · funext j
      fin_cases j <;> simp [Matrix.vecHead, Matrix.vecTail, a, b, c, sideMap, pairMap, demandMap]
      all_goals abel
    · funext j
      fin_cases j <;> simp [Matrix.vecHead, Matrix.vecTail, a, b, c, sideMap, pairMap, demandMap]

theorem signal_eq_side_repairedPairs (hH : Function.Surjective H) (i : Fin 3) :
    signal K n A H i = side K n i ⊔ repairedPairs K n A H i := by
  apply le_antisymm
  · exact sup_le le_sup_left (demand_le_side_repairedPairs K n A H hH i)
  · exact sup_le le_sup_left (repairedPairs_le_signal K n A H i)

theorem repairedPairs_actual (i : Fin 3) : repairedPairs K n A H i =
    ((signal K n A H i ⊓ signal K n A H (i+1)) ⊓ LinearMap.range (relayMap K n)) ⊔
    ((signal K n A H i ⊓ signal K n A H (i+2)) ⊓ LinearMap.range (relayMap K n)) := by
  fin_cases i
  · change (_ ⊓ _) ⊔ (_ ⊓ _) =
      (signal K n A H 0 ⊓ signal K n A H 1 ⊓ _) ⊔
      (signal K n A H 0 ⊓ signal K n A H 2 ⊓ _)
    rw [pair₁₂_eq, pair₁₃_eq]
  · change (_ ⊓ _) ⊔ (_ ⊓ _) =
      (signal K n A H 1 ⊓ signal K n A H 2 ⊓ _) ⊔
      (signal K n A H 1 ⊓ signal K n A H 0 ⊓ _)
    rw [inf_comm (signal K n A H 1) (signal K n A H 0), pair₁₂_eq, pair₂₃_eq, sup_comm]
  · change (_ ⊓ _) ⊔ (_ ⊓ _) =
      (signal K n A H 2 ⊓ signal K n A H 0 ⊓ _) ⊔
      (signal K n A H 2 ⊓ signal K n A H 1 ⊓ _)
    rw [inf_comm (signal K n A H 2) (signal K n A H 0),
      inf_comm (signal K n A H 2) (signal K n A H 1), pair₁₃_eq, pair₂₃_eq]


/-- The repaired task keeps the original ambient space but restricts every flag to P. -/
def repairedTask : UploadBroadcast.Task K (Ambient K n) where
  A := fun i => side K n i ⊓ LinearMap.range (relayMap K n)
  U := fun i => signal K n A H i ⊓ LinearMap.range (relayMap K n)
  side_le_signal := fun _ => inf_le_inf le_sup_left le_rfl
  feasible := by
    intro i
    have h : (⨆ j : Fin 3, side K n j ⊓ LinearMap.range (relayMap K n)) =
        LinearMap.range (relayMap K n) := by
      simpa only [inf_comm] using (relay_locally_generated K n).symm
    rw [h]
    exact inf_le_right

theorem repaired_signal_eq_side_pairs (hH : Function.Surjective H) (i : Fin 3) :
    (repairedTask K n A H).U i = (repairedTask K n A H).A i ⊔ repairedPairs K n A H i := by
  change signal K n A H i ⊓ _ = (side K n i ⊓ _) ⊔ _
  rw [signal_eq_side_repairedPairs K n A H hH i, sup_comm,
    sup_inf_assoc_of_le _ (repairedPairs_le_relay K n A H i), sup_comm]

theorem repairedPairs_induced_actual (i : Fin 3) : repairedPairs K n A H i =
    ((repairedTask K n A H).U i ⊓ (repairedTask K n A H).U (i+1)) ⊔
    ((repairedTask K n A H).U i ⊓ (repairedTask K n A H).U (i+2)) := by
  change _ = ((signal K n A H i ⊓ _) ⊓ (signal K n A H (i+1) ⊓ _)) ⊔
    ((signal K n A H i ⊓ _) ⊓ (signal K n A H (i+2) ⊓ _))
  rw [inf_inf_inf_comm, inf_idem, inf_inf_inf_comm, inf_idem]
  exact repairedPairs_actual K n A H i

/-- Conditional rank is saturated by any intermediate space containing a quotient-spanning space. -/
theorem condRank_of_quotient_spanning {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A₀ U₀ C B : Submodule K V)
    (hspan : A₀ ⊔ C = U₀) (hCB : C ≤ B) (hBU : B ≤ U₀) :
    condRank B A₀ = condRank U₀ A₀ := by
  have hAU : A₀ ≤ U₀ := hspan ▸ le_sup_left
  have hs : A₀ ⊔ B = U₀ := le_antisymm (sup_le hAU hBU)
    (hspan ▸ sup_le_sup_left hCB A₀)
  unfold condRank
  rw [hs, sup_eq_right.mpr hAU]

/-- For any three spaces, the two incident pair spaces lie in the mixed branch. -/
theorem incidentPairs_le_branch {V : Type*} [AddCommGroup V] [Module K V]
    (U : Fin 3 → Submodule K V) (i : Fin 3) :
    (U i ⊓ U (i+1)) ⊔ (U i ⊓ U (i+2)) ≤ U i ⊓ (U (i+1) ⊔ U (i+2)) :=
  sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)

theorem repaired_branch_condRank (hH : Function.Surjective H) (i : Fin 3) :
    condRank ((repairedTask K n A H).U i ⊓
      ((repairedTask K n A H).U (i+1) ⊔ (repairedTask K n A H).U (i+2)))
      ((repairedTask K n A H).A i) = n + 1 := by
  rw [condRank_of_quotient_spanning K _ _ (repairedPairs K n A H i) _
    (repaired_signal_eq_side_pairs K n A H hH i).symm
    (by rw [repairedPairs_induced_actual]; exact incidentPairs_le_branch K _ i)
    inf_le_left]
  exact induced_demand_condRank K n A H i

theorem repaired_pairSum_condRank (hH : Function.Surjective H) (i : Fin 3) :
    condRank (((repairedTask K n A H).U i ⊓ (repairedTask K n A H).U (i+1)) ⊔
      ((repairedTask K n A H).U i ⊓ (repairedTask K n A H).U (i+2)))
      ((repairedTask K n A H).A i) = n + 1 := by
  rw [← repairedPairs_induced_actual]
  rw [condRank_of_quotient_spanning K _ _ (repairedPairs K n A H i) _
    (repaired_signal_eq_side_pairs K n A H hH i).symm le_rfl
    (by exact le_inf (repairedPairs_le_signal K n A H i) (repairedPairs_le_relay K n A H i))]
  exact induced_demand_condRank K n A H i

theorem full_branch_condRank (hH : Function.Surjective H) (i : Fin 3) :
    condRank (signal K n A H i ⊓ (signal K n A H (i+1) ⊔ signal K n A H (i+2)))
      (side K n i) = n + 1 := by
  have hp : repairedPairs K n A H i ≤
      (signal K n A H i ⊓ signal K n A H (i+1)) ⊔
      (signal K n A H i ⊓ signal K n A H (i+2)) := by
    rw [repairedPairs_actual]
    exact sup_le_sup inf_le_left inf_le_left
  rw [condRank_of_quotient_spanning K _ _ (repairedPairs K n A H i) _
    (signal_eq_side_repairedPairs K n A H hH i).symm
    (hp.trans (incidentPairs_le_branch K _ i)) inf_le_left]
  exact demand_condRank K n A H i

theorem full_pairSum_condRank (hH : Function.Surjective H) (i : Fin 3) :
    condRank ((signal K n A H i ⊓ signal K n A H (i+1)) ⊔
      (signal K n A H i ⊓ signal K n A H (i+2))) (side K n i) = n + 1 := by
  have hp : repairedPairs K n A H i ≤
      (signal K n A H i ⊓ signal K n A H (i+1)) ⊔
      (signal K n A H i ⊓ signal K n A H (i+2)) := by
    rw [repairedPairs_actual]
    exact sup_le_sup inf_le_left inf_le_left
  rw [condRank_of_quotient_spanning K _ _ (repairedPairs K n A H i) _
    (signal_eq_side_repairedPairs K n A H hH i).symm hp
    (sup_le inf_le_left inf_le_left)]
  exact demand_condRank K n A H i

theorem totalDemand_of_condRanks {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : UploadBroadcast.Task K V) (m : ℕ)
    (hm : ∀ i, condRank (T.U i) (T.A i) = m) : Profile.totalDemand T = 3*m := by
  have hd (i : Fin 3) : Module.finrank K (T.U i) - Module.finrank K (T.A i) = m := by
    have h := hm i
    unfold condRank at h
    rw [sup_eq_right.mpr (T.side_le_signal i)] at h
    exact h
  unfold Profile.totalDemand
  simp only [hd]
  simp

theorem full_totalDemand : Profile.totalDemand (task K n A H) = 3*(n+1) :=
  totalDemand_of_condRanks K _ (n+1) (demand_condRank K n A H)

theorem repaired_totalDemand : Profile.totalDemand (repairedTask K n A H) = 3*(n+1) :=
  totalDemand_of_condRanks K _ (n+1) (induced_demand_condRank K n A H)

theorem repaired_triple_eq_bot
    (hjoint : ∀ w : Vec K n, A w = w → H w = 0 → w = 0) :
    ((repairedTask K n A H).U 0 ⊓ (repairedTask K n A H).U 1) ⊓
      (repairedTask K n A H).U 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← triple_eq_bot K n A H hjoint]
  exact inf_le_inf (inf_le_inf inf_le_left inf_le_left) inf_le_left

theorem firstEntry_formula {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : UploadBroadcast.Task K V) (m : ℕ)
    (ht : Profile.totalDemand T = 3*m) (i j k : Fin 3)
    (hb : condRank (T.U k ⊓ (T.U i ⊔ T.U j)) (T.A k) = m) :
    Profile.firstEntry T i j k = 2*(m : ℝ) - condRank (T.U i ⊓ T.U j) (T.A j) := by
  unfold Profile.firstEntry
  rw [ht, hb]
  push_cast
  ring

theorem full_firstProfile (hA : Function.Injective A) (hH : Function.Surjective H) (r : Fin 6) :
    Profile.entry (task K n A H) (.inl r) =
      ![(n : ℝ)+2, n+1, n+1, n+2, n+2, n+1] r := by
  obtain ⟨f₁, f₂, f₃, f₄, f₅, f₆⟩ := pair_condRanks K n A H hA
  rw [← pair₁₂_eq] at f₁ f₂
  rw [← pair₁₃_eq] at f₃ f₄
  rw [← pair₂₃_eq] at f₅ f₆
  change condRank ((task K n A H).U 0 ⊓ (task K n A H).U 1) ((task K n A H).A 0) = n + 1 at f₁
  change condRank ((task K n A H).U 0 ⊓ (task K n A H).U 1) ((task K n A H).A 1) = n at f₂
  change condRank ((task K n A H).U 0 ⊓ (task K n A H).U 2) ((task K n A H).A 0) = n at f₃
  change condRank ((task K n A H).U 0 ⊓ (task K n A H).U 2) ((task K n A H).A 2) = n + 1 at f₄
  change condRank ((task K n A H).U 1 ⊓ (task K n A H).U 2) ((task K n A H).A 1) = n + 1 at f₅
  change condRank ((task K n A H).U 1 ⊓ (task K n A H).U 2) ((task K n A H).A 2) = n at f₆
  have b₀ := full_branch_condRank K n A H hH 0
  change condRank ((task K n A H).U 0 ⊓ ((task K n A H).U 1 ⊔ (task K n A H).U 2)) ((task K n A H).A 0) = n+1 at b₀
  have b₁ := full_branch_condRank K n A H hH 1
  change condRank ((task K n A H).U 1 ⊓ ((task K n A H).U 2 ⊔ (task K n A H).U 0)) ((task K n A H).A 1) = n+1 at b₁
  have b₂ := full_branch_condRank K n A H hH 2
  change condRank ((task K n A H).U 2 ⊓ ((task K n A H).U 0 ⊔ (task K n A H).U 1)) ((task K n A H).A 2) = n+1 at b₂
  have e₀ := firstEntry_formula K (task K n A H) (n+1) (full_totalDemand K n A H) 0 1 2 b₂
  rw [f₂] at e₀
  have e₁ := firstEntry_formula K (task K n A H) (n+1) (full_totalDemand K n A H) 0 2 1 (by simpa only [sup_comm] using b₁)
  rw [f₄] at e₁
  have e₂ := firstEntry_formula K (task K n A H) (n+1) (full_totalDemand K n A H) 1 0 2 (by simpa only [sup_comm] using b₂)
  rw [inf_comm, f₁] at e₂
  have e₃ := firstEntry_formula K (task K n A H) (n+1) (full_totalDemand K n A H) 1 2 0 b₀
  rw [f₆] at e₃
  have e₄ := firstEntry_formula K (task K n A H) (n+1) (full_totalDemand K n A H) 2 0 1 b₁
  rw [inf_comm, f₃] at e₄
  have e₅ := firstEntry_formula K (task K n A H) (n+1) (full_totalDemand K n A H) 2 1 0 (by simpa only [sup_comm] using b₀)
  rw [inf_comm, f₅] at e₅
  fin_cases r <;> simp only [Profile.entry, Profile.firstOrder, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]
  all_goals push_cast at *
  · linarith [e₀]
  · linarith [e₁]
  · linarith [e₂]
  · linarith [e₃]
  · linarith [e₄]
  · linarith [e₅]

theorem secondProfile_formula {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : UploadBroadcast.Task K V) (m : ℕ)
    (htotal : Profile.totalDemand T = 3*m)
    (htriple : T.U 0 ⊓ T.U 1 ⊓ T.U 2 = ⊥)
    (hpair : ∀ i : Fin 3, condRank ((T.U i ⊓ T.U (i+1)) ⊔
      (T.U i ⊓ T.U (i+2))) (T.A i) = m)
    (hbranch : ∀ i : Fin 3, condRank (T.U i ⊓ (T.U (i+1) ⊔ T.U (i+2))) (T.A i) = m)
    (i l : Fin 3) : 2 * Profile.secondEntry T i (i+1) (i+2) l = 3*(m : ℝ) := by
  have ht (l : Fin 3) : condRank (T.U 0 ⊓ T.U 1 ⊓ T.U 2) (T.A l) = 0 := by
    rw [htriple]
    unfold condRank
    rw [sup_bot_eq]
    exact Nat.sub_self _
  have p₀ := hpair 0
  have p₁ := hpair 1
  have p₂ := hpair 2
  have b₀ := hbranch 0
  have b₁ := hbranch 1
  have b₂ := hbranch 2
  change condRank ((T.U 0 ⊓ T.U 1) ⊔ (T.U 0 ⊓ T.U 2)) (T.A 0) = m at p₀
  change condRank (T.U 0 ⊓ (T.U 1 ⊔ T.U 2)) (T.A 0) = m at b₀
  change condRank ((T.U 1 ⊓ T.U 2) ⊔ (T.U 1 ⊓ T.U 0)) (T.A 1) = m at p₁
  change condRank (T.U 1 ⊓ (T.U 2 ⊔ T.U 0)) (T.A 1) = m at b₁
  change condRank ((T.U 2 ⊓ T.U 0) ⊔ (T.U 2 ⊓ T.U 1)) (T.A 2) = m at p₂
  change condRank (T.U 2 ⊓ (T.U 0 ⊔ T.U 1)) (T.A 2) = m at b₂
  have b₀' : condRank (T.U 0 ⊓ (T.U 2 ⊔ T.U 1)) (T.A 0) = m := by
    simpa only [sup_comm] using b₀
  have b₁' : condRank (T.U 1 ⊓ (T.U 0 ⊔ T.U 2)) (T.A 1) = m := by
    simpa only [sup_comm] using b₁
  have b₂' : condRank (T.U 2 ⊓ (T.U 1 ⊔ T.U 0)) (T.A 2) = m := by
    simpa only [sup_comm] using b₂
  fin_cases i
  · change 2 * Profile.secondEntry T 0 1 2 l = _
    unfold Profile.secondEntry
    rw [htotal, ht, p₀, b₁', b₂]
    push_cast
    ring
  · change 2 * Profile.secondEntry T 1 2 0 l = _
    unfold Profile.secondEntry
    rw [htotal, ht, p₁, b₂', b₀]
    push_cast
    ring
  · change 2 * Profile.secondEntry T 2 0 1 l = _
    unfold Profile.secondEntry
    rw [htotal, ht, p₂, b₀', b₁]
    push_cast
    ring

theorem full_secondProfile (hH : Function.Surjective H)
    (hjoint : ∀ w : Vec K n, A w = w → H w = 0 → w = 0) (i l : Fin 3) :
    2 * Profile.entry (task K n A H) (.inr (i,l)) = 3*((n : ℝ)+1) := by
  simpa only [Profile.entry, Nat.cast_add, Nat.cast_one] using secondProfile_formula K (task K n A H) (n+1) (full_totalDemand K n A H)
    (triple_eq_bot K n A H hjoint) (full_pairSum_condRank K n A H hH)
    (full_branch_condRank K n A H hH) i l

theorem repaired_secondProfile (hH : Function.Surjective H)
    (hjoint : ∀ w : Vec K n, A w = w → H w = 0 → w = 0) (i l : Fin 3) :
    2 * Profile.entry (repairedTask K n A H) (.inr (i,l)) = 3*((n : ℝ)+1) := by
  simpa only [Profile.entry, Nat.cast_add, Nat.cast_one] using secondProfile_formula K (repairedTask K n A H) (n+1) (repaired_totalDemand K n A H)
    (repaired_triple_eq_bot K n A H hjoint) (repaired_pairSum_condRank K n A H hH)
    (repaired_branch_condRank K n A H hH) i l

theorem repaired_pair₁₂_eq :
    (repairedTask K n A H).U 0 ⊓ (repairedTask K n A H).U 1 =
      LinearMap.range (pairMap K n A H 0) ⊓ LinearMap.range (relayMap K n) := by
  change (_ ⊓ _) ⊓ (_ ⊓ _) = _
  rw [inf_inf_inf_comm, inf_idem, pair₁₂_eq]

theorem repaired_pair₁₃_eq :
    (repairedTask K n A H).U 0 ⊓ (repairedTask K n A H).U 2 =
      LinearMap.range (pairMap K n A H 1) ⊓ LinearMap.range (relayMap K n) := by
  change (_ ⊓ _) ⊓ (_ ⊓ _) = _
  rw [inf_inf_inf_comm, inf_idem, pair₁₃_eq]

theorem repaired_pair₂₃_eq :
    (repairedTask K n A H).U 1 ⊓ (repairedTask K n A H).U 2 =
      LinearMap.range (pairMap K n A H 2) ⊓ LinearMap.range (relayMap K n) := by
  change (_ ⊓ _) ⊓ (_ ⊓ _) = _
  rw [inf_inf_inf_comm, inf_idem, pair₂₃_eq]

theorem repaired_firstProfile (hA : Function.Injective A) (hH : Function.Surjective H) (r : Fin 6) :
    Profile.entry (repairedTask K n A H) (.inl r) =
      ![(n : ℝ)+2, n+2, n+1, n+2, n+2, n+1] r := by
  obtain ⟨f₁, f₂, f₃, f₄, f₅, f₆⟩ := induced_pair_condRanks K n A H hA
  rw [← repaired_pair₁₂_eq] at f₁ f₂
  rw [← repaired_pair₁₃_eq] at f₃ f₄
  rw [← repaired_pair₂₃_eq] at f₅ f₆
  change condRank ((repairedTask K n A H).U 0 ⊓ (repairedTask K n A H).U 1) ((repairedTask K n A H).A 0) = n + 1 at f₁
  change condRank ((repairedTask K n A H).U 0 ⊓ (repairedTask K n A H).U 1) ((repairedTask K n A H).A 1) = n at f₂
  change condRank ((repairedTask K n A H).U 0 ⊓ (repairedTask K n A H).U 2) ((repairedTask K n A H).A 0) = n at f₃
  change condRank ((repairedTask K n A H).U 0 ⊓ (repairedTask K n A H).U 2) ((repairedTask K n A H).A 2) = n at f₄
  change condRank ((repairedTask K n A H).U 1 ⊓ (repairedTask K n A H).U 2) ((repairedTask K n A H).A 1) = n + 1 at f₅
  change condRank ((repairedTask K n A H).U 1 ⊓ (repairedTask K n A H).U 2) ((repairedTask K n A H).A 2) = n at f₆
  have b₀ := repaired_branch_condRank K n A H hH 0
  change condRank ((repairedTask K n A H).U 0 ⊓ ((repairedTask K n A H).U 1 ⊔ (repairedTask K n A H).U 2)) ((repairedTask K n A H).A 0) = n+1 at b₀
  have b₁ := repaired_branch_condRank K n A H hH 1
  change condRank ((repairedTask K n A H).U 1 ⊓ ((repairedTask K n A H).U 2 ⊔ (repairedTask K n A H).U 0)) ((repairedTask K n A H).A 1) = n+1 at b₁
  have b₂ := repaired_branch_condRank K n A H hH 2
  change condRank ((repairedTask K n A H).U 2 ⊓ ((repairedTask K n A H).U 0 ⊔ (repairedTask K n A H).U 1)) ((repairedTask K n A H).A 2) = n+1 at b₂
  have e₀ := firstEntry_formula K (repairedTask K n A H) (n+1) (repaired_totalDemand K n A H) 0 1 2 b₂
  rw [f₂] at e₀
  have e₁ := firstEntry_formula K (repairedTask K n A H) (n+1) (repaired_totalDemand K n A H) 0 2 1 (by simpa only [sup_comm] using b₁)
  rw [f₄] at e₁
  have e₂ := firstEntry_formula K (repairedTask K n A H) (n+1) (repaired_totalDemand K n A H) 1 0 2 (by simpa only [sup_comm] using b₂)
  rw [inf_comm, f₁] at e₂
  have e₃ := firstEntry_formula K (repairedTask K n A H) (n+1) (repaired_totalDemand K n A H) 1 2 0 b₀
  rw [f₆] at e₃
  have e₄ := firstEntry_formula K (repairedTask K n A H) (n+1) (repaired_totalDemand K n A H) 2 0 1 b₁
  rw [inf_comm, f₃] at e₄
  have e₅ := firstEntry_formula K (repairedTask K n A H) (n+1) (repaired_totalDemand K n A H) 2 1 0 (by simpa only [sup_comm] using b₀)
  rw [inf_comm, f₅] at e₅
  fin_cases r <;> simp only [Profile.entry, Profile.firstOrder, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]
  all_goals push_cast at *
  · linarith [e₀]
  · linarith [e₁]
  · linarith [e₂]
  · linarith [e₃]
  · linarith [e₄]
  · linarith [e₅]

end UploadBroadcast.CycleRepair
