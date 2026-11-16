import UploadBroadcast.ResonantFlagNormalization
import UploadBroadcast.TaskQuiverBridge
import UploadBroadcast.ResonantTripodTransversality

/-! The explicit tripod with one enlarged arm, and its exclusion from a
regular resonant indecomposable by actual reflection Hom transport. -/
namespace UploadBroadcast.TripodSubobjectExclusion
open TaskDecomposition
variable (K : Type*) [Field K]

abbrev Plane := K × K

def line₁ : Submodule K (Plane K) where
  carrier := {p | p.2=0}
  zero_mem' := rfl
  add_mem' := by intro p q hp hq; simp_all
  smul_mem' := by intro a p hp; simp_all

def line₂ : Submodule K (Plane K) where
  carrier := {p | p.1=0}
  zero_mem' := rfl
  add_mem' := by intro p q hp hq; simp_all
  smul_mem' := by intro a p hp; simp_all

def line₃ : Submodule K (Plane K) where
  carrier := {p | p.1+p.2=0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    change p.1+p.2=0 at hp
    change q.1+q.2=0 at hq
    change (p.1+q.1)+(p.2+q.2)=0
    linear_combination hp+hq
  smul_mem' := by intro a p hp; change a*p.1+a*p.2=0; rw [←mul_add,hp,mul_zero]

def sides : Fin 3 → Submodule K (Plane K) := ![line₁ K,line₂ K,line₃ K]

def enlargement (r : Fin 3) : TaskDecomposition.Task K (Plane K) where
  A := sides K
  U i := if i=r then ⊤ else sides K i
  nested i := by split_ifs <;> simp

/-- Every endomorphism of the three tripod lines is a scalar. -/
theorem tripod_scalar (f : Module.End K (Plane K))
    (hf : ∀ i p, p ∈ sides K i → f p ∈ sides K i) :
    ∃ a : K, ∀ p, f p = (a*p.1,a*p.2) := by
  have h₁ := hf 0 (1,0) (by simp [sides,line₁])
  have h₂ := hf 1 (0,1) (by simp [sides,line₂])
  have h₃ := hf 2 ((0,1)-(1,0)) (by simp [sides,line₃])
  change (f (1,0)).2=0 at h₁
  change (f (0,1)).1=0 at h₂
  change (f ((0,1)-(1,0))).1+(f ((0,1)-(1,0))).2=0 at h₃
  rw [map_sub] at h₃
  change (f (0,1)).1-(f (1,0)).1+((f (0,1)).2-(f (1,0)).2)=0 at h₃
  have hsame : (f (0,1)).2=(f (1,0)).1 := by linear_combination h₃-h₂+h₁
  refine ⟨(f (1,0)).1,fun p => ?_⟩
  have hp : p=p.1 • (1,0)+p.2 • (0,1) := by ext <;> simp
  rw [hp,map_add,map_smul,map_smul]
  apply Prod.ext
  · simp [h₂,mul_comm]
  · simp [h₁,hsame,mul_comm]

/-- Enlarging any one arm of the tripod preserves indecomposability. -/
theorem enlargement_indecomposable (r : Fin 3) :
    Indecomposable (enlargement K r).spaces ⊤ := by
  apply indecomposable_of_projection_eq_zero_or_id
  · exact top_ne_bot
  · intro f hf hid
    obtain ⟨a,ha⟩ := tripod_scalar K f (fun i p hp => hf (i,false) p hp)
    have haa : a*a=a := by
      have he := congrArg Prod.fst (hid (1,0))
      rw [ha,ha] at he
      simpa using he
    have hz : a*(a-1)=0 := by linear_combination haa
    obtain hz | ho := mul_eq_zero.mp hz
    · left
      apply LinearMap.ext
      intro p
      simp [ha,hz]
    · right
      have ha1 : a=1 := sub_eq_zero.mp ho
      apply LinearMap.ext
      intro p
      simp [ha,ha1]

def vector₁ : K →ₗ[K] Plane K where
  toFun a := (a,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def vector₂ : K →ₗ[K] Plane K where
  toFun a := (0,a)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def vector₃ : K →ₗ[K] Plane K where
  toFun a := (-a,a)
  map_add' a b := by simp [add_comm]
  map_smul' a b := by simp

theorem line₁_range : LinearMap.range (vector₁ K)=line₁ K := by
  ext p
  constructor
  · rintro ⟨a,rfl⟩; simp [vector₁,vector₂,line₁,line₂]
  · intro hp
    refine ⟨p.1,?_⟩
    change (p.1,0)=p
    exact Prod.ext rfl hp.symm

theorem line₂_range : LinearMap.range (vector₂ K)=line₂ K := by
  ext p
  constructor
  · rintro ⟨a,rfl⟩; simp [vector₁,vector₂,line₁,line₂]
  · intro hp
    refine ⟨p.2,?_⟩
    change (0,p.2)=p
    exact Prod.ext hp.symm rfl

theorem line₃_range : LinearMap.range (vector₃ K)=line₃ K := by
  ext p
  constructor
  · rintro ⟨a,rfl⟩; simp [vector₃,line₃]
  · intro hp
    change p.1+p.2=0 at hp
    refine ⟨p.2,?_⟩
    change (-p.2,p.2)=p
    exact Prod.ext (by linear_combination -hp) rfl

theorem sides_finrank (i : Fin 3) : Module.finrank K (sides K i)=1 := by
  fin_cases i
  · change Module.finrank K (line₁ K)=1
    rw [←line₁_range,LinearMap.finrank_range_of_inj (f := vector₁ K)
      (by intro a b he; exact congrArg Prod.fst he)]
    simp
  · change Module.finrank K (line₂ K)=1
    rw [←line₂_range,LinearMap.finrank_range_of_inj (f := vector₂ K)
      (by intro a b he; exact congrArg Prod.snd he)]
    simp
  · change Module.finrank K (line₃ K)=1
    rw [←line₃_range,LinearMap.finrank_range_of_inj (f := vector₃ K)
      (by intro a b he; exact congrArg Prod.snd he)]
    simp

variable {F : Type*} [AddCommGroup F] [Module K F]

def planeMap (v r : F) : Plane K →ₗ[K] F where
  toFun p := p.1 • v+p.2 • r
  map_add' p q := by simp [add_smul]; abel
  map_smul' a p := by simp [smul_add,smul_smul]

theorem planeMap_preserves (T : TaskDecomposition.Task K F) (i : Fin 3) (v r : F)
    (hv : v ∈ T.A 0) (hr : r ∈ T.A 1) (ht : r-v ∈ T.A 2)
    (huv : v ∈ T.U i) (hur : r ∈ T.U i) :
    Preserves (enlargement K i).spaces T.spaces (planeMap K v r) := by
  have hA (j : Fin 3) (p : Plane K) (hp : p ∈ sides K j) : planeMap K v r p ∈ T.A j := by
    fin_cases j
    · change p.2=0 at hp
      change p.1 • v+p.2 • r ∈ T.A 0
      simpa [hp] using (T.A 0).smul_mem p.1 hv
    · change p.1=0 at hp
      change p.1 • v+p.2 • r ∈ T.A 1
      simpa [hp] using (T.A 1).smul_mem p.2 hr
    · change p.1+p.2=0 at hp
      have he : p.1 • v+p.2 • r = p.2 • (r-v) := by
        rw [eq_neg_of_add_eq_zero_left hp,neg_smul,smul_sub]
        abel
      change p.1 • v+p.2 • r ∈ T.A 2
      rw [he]
      exact (T.A 2).smul_mem p.2 ht
  rintro ⟨j,b⟩ p hp
  cases b
  · exact hA j p hp
  · change planeMap K v r p ∈ T.U j
    by_cases hj : j=i
    · subst j
      exact (T.U i).add_mem ((T.U i).smul_mem p.1 huv) ((T.U i).smul_mem p.2 hur)
    · apply T.nested j
      apply hA j p
      simpa [TaskDecomposition.Task.spaces,enlargement,hj] using hp

open QuiverRepresentation E6Reflection ResonantTripodTransversality

/-- Dimensions of the actual explicit tripod-enlargement representation. -/
theorem enlargement_rep_dimension (K : Type) [Field K] (i : Fin 3) :
    dimension (enlargement K i).toRep = encode (tripodEnlargementAt i) := by
  funext v
  cases v with
  | center => simp [dimension,TaskDecomposition.Task.toRep,enlargement,
      tripodEnlargementAt,encode,Plane]
  | middle j =>
    fin_cases i <;> fin_cases j <;>
      simp [dimension,TaskDecomposition.Task.toRep,enlargement,tripodEnlargementAt,
        encode,sides_finrank,Plane]
  | outer j => fin_cases j <;> simp [dimension,TaskDecomposition.Task.toRep,enlargement,
      tripodEnlargementAt,encode,sides_finrank]

/-- An actual regular resonant flag configuration cannot contain a nonzero
tripod whose whole plane lies in any one enlarged arm. The proof constructs
the concrete forbidden morphism, then uses 28 reflection steps to kill it. -/
theorem tripod_plane_vectors_zero {K F : Type} [Field K] [AddCommGroup F] [Module K F]
    [FiniteDimensional K F] (T : TaskDecomposition.Task K F)
    (hT : TaskDecomposition.Indecomposable T.spaces ⊤)
    (n : ℕ) (hD : dimension T.toRep = regular n)
    (i : Fin 3) (v r : F)
    (hv : v ∈ T.A 0) (hr : r ∈ T.A 1) (ht : r-v ∈ T.A 2)
    (huv : v ∈ T.U i) (hur : r ∈ T.U i) : v=0 ∧ r=0 := by
  let f := (enlargement K i).homOfPreserves T (planeMap K v r)
    (planeMap_preserves K T i v r hv hr ht huv hur)
  have hz := tripodEnlargementAt_hom_zero i (enlargement K i).toRep T.toRep
    ((enlargement K i).rep_indec_of_indec (enlargement_indecomposable K i))
    (T.rep_indec_of_indec hT) (enlargement_rep_dimension K i) n hD f
  have hcenter := congrArg (fun a : Hom (enlargement K i).toRep T.toRep => a.map .center) hz
  constructor
  · have he := LinearMap.congr_fun hcenter (1,0)
    change (1:K) • v+(0:K) • r=0 at he
    simpa using he
  · have he := LinearMap.congr_fun hcenter (0,1)
    change (0:K) • v+(1:K) • r=0 at he
    simpa using he

/-- The exclusion needs only zero defect, with no root or exact-dimension hypothesis. -/
theorem tripod_plane_vectors_zero_of_zero_defect {K F : Type} [Field K] [AddCommGroup F] [Module K F]
    [FiniteDimensional K F] (T : TaskDecomposition.Task K F)
    (hT : TaskDecomposition.Indecomposable T.spaces ⊤)
    (hD : ReflectionReduction.defect T.dimensionVector = 0)
    (i : Fin 3) (v r : F)
    (hv : v ∈ T.A 0) (hr : r ∈ T.A 1) (ht : r-v ∈ T.A 2)
    (huv : v ∈ T.U i) (hur : r ∈ T.U i) : v=0 ∧ r=0 := by
  let f := (enlargement K i).homOfPreserves T (planeMap K v r)
    (planeMap_preserves K T i v r hv hr ht huv hur)
  have hz := tripodEnlargementAt_hom_zero_of_zero_defect i (enlargement K i).toRep T.toRep
    ((enlargement K i).rep_indec_of_indec (enlargement_indecomposable K i))
    (T.rep_indec_of_indec hT) (enlargement_rep_dimension K i)
    (by simpa only [TaskDecomposition.Task.dimensionVector_eq] using hD) f
  have hcenter := congrArg (fun a : Hom (enlargement K i).toRep T.toRep => a.map .center) hz
  constructor
  · have he := LinearMap.congr_fun hcenter (1,0)
    change (1:K) • v+(0:K) • r=0 at he
    simpa using he
  · have he := LinearMap.congr_fun hcenter (0,1)
    change (0:K) • v+(1:K) • r=0 at he
    simpa using he

/-- The intrinsic full tripod plane of the three side spaces. -/
def tripodPlane (T : TaskDecomposition.Task K F) : Submodule K F :=
  (T.A 0 ⊓ (T.A 1 ⊔ T.A 2)) ⊔ (T.A 1 ⊓ (T.A 0 ⊔ T.A 2))

section Intrinsic
variable {K F : Type} [Field K] [AddCommGroup F] [Module K F] [FiniteDimensional K F]
variable (T : TaskDecomposition.Task K F)
    (hT : TaskDecomposition.Indecomposable T.spaces ⊤)
    (hD : ReflectionReduction.defect T.dimensionVector = 0)
include hT hD

/-- Regular indecomposable injective flags have pairwise-disjoint sides. -/
theorem regular_sides_disjoint :
    Disjoint (T.A 0) (T.A 1) ∧ Disjoint (T.A 0) (T.A 2) ∧ Disjoint (T.A 1) (T.A 2) := by
  refine ⟨Submodule.disjoint_def.mpr ?_,Submodule.disjoint_def.mpr ?_,Submodule.disjoint_def.mpr ?_⟩
  · intro x h0 h1
    exact (tripod_plane_vectors_zero_of_zero_defect T hT hD 0 x x h0 h1
      (by simp) (T.nested 0 h0) (T.nested 0 h0)).1
  · intro x h0 h2
    exact (tripod_plane_vectors_zero_of_zero_defect T hT hD 0 x 0 h0 (T.A 1).zero_mem
      (by simpa using (T.A 2).neg_mem h2) (T.nested 0 h0) (T.U 0).zero_mem).1
  · intro x h1 h2
    exact (tripod_plane_vectors_zero_of_zero_defect T hT hD 1 0 x (T.A 0).zero_mem h1
      (by simpa using h2) (T.U 1).zero_mem (T.nested 1 h1)).2

private theorem second_tripod_zero (i : Fin 3) (hi : i=0 ∨ i=2) (r : F)
    (hr : r ∈ T.A 1 ⊓ (T.A 0 ⊔ T.A 2)) (hu : r ∈ T.U i) : r=0 := by
  obtain ⟨v,hv,t,ht,he⟩ := Submodule.mem_sup.mp hr.2
  have hrv : r-v=t := by rw [←he]; abel
  have hvU : v ∈ T.U i := by
    rcases hi with rfl | rfl
    · exact T.nested 0 hv
    · have he' : v=r-t := by rw [←he]; abel
      rw [he']
      exact (T.U 2).sub_mem hu (T.nested 2 ht)
  exact (tripod_plane_vectors_zero_of_zero_defect T hT hD i v r hv hr.1
    (by rw [hrv]; exact ht) hvU hu).2

private theorem first_tripod_zero (v : F)
    (hv : v ∈ T.A 0 ⊓ (T.A 1 ⊔ T.A 2)) (hu : v ∈ T.U 1) : v=0 := by
  obtain ⟨r,hr,t,ht,he⟩ := Submodule.mem_sup.mp hv.2
  have hrv : r-v= -t := by rw [←he]; abel
  exact (tripod_plane_vectors_zero_of_zero_defect T hT hD 1 v r hv.1 hr
    (by rw [hrv]; exact (T.A 2).neg_mem ht) hu (T.nested 1 hr)).1

/-- No enlarged arm gains an extra direction in the full intrinsic tripod
plane. Consequently quotienting by that plane loses only its side subspace. -/
theorem regular_tripod_intersection (i : Fin 3) :
    T.U i ⊓ tripodPlane K T = T.A i ⊓ tripodPlane K T := by
  apply le_antisymm
  · intro p hp
    refine ⟨?_,hp.2⟩
    obtain ⟨v,hv,r,hr,he⟩ := Submodule.mem_sup.mp hp.2
    fin_cases i
    · have hrU : r ∈ T.U 0 := by
        have he' : r=p-v := by rw [←he]; abel
        rw [he']
        exact (T.U 0).sub_mem hp.1 (T.nested 0 hv.1)
      have hr0 := second_tripod_zero T hT hD 0 (Or.inl rfl) r hr hrU
      simpa [←he,hr0] using hv.1
    · have hvU : v ∈ T.U 1 := by
        have he' : v=p-r := by rw [←he]; abel
        rw [he']
        exact (T.U 1).sub_mem hp.1 (T.nested 1 hr.1)
      have hv0 := first_tripod_zero T hT hD v hv hvU
      simpa [←he,hv0] using hr.1
    · obtain ⟨r₀,hr₀,t,ht,hev⟩ := Submodule.mem_sup.mp hv.2
      have hsum : r₀+r ∈ T.A 1 ⊓ (T.A 0 ⊔ T.A 2) := by
        constructor
        · exact (T.A 1).add_mem hr₀ hr.1
        · apply (T.A 0 ⊔ T.A 2).add_mem _ hr.2
          have he' : r₀=v-t := by rw [←hev]; abel
          rw [he']
          exact (T.A 0 ⊔ T.A 2).sub_mem (Submodule.mem_sup_left hv.1) (Submodule.mem_sup_right ht)
      have hsumU : r₀+r ∈ T.U 2 := by
        have he' : r₀+r=p-t := by rw [←he,←hev]; abel
        rw [he']
        exact (T.U 2).sub_mem hp.1 (T.nested 2 ht)
      have hzero := second_tripod_zero T hT hD 2 (Or.inr rfl) (r₀+r) hsum hsumU
      have hp' : p=t := by
        calc p=(r₀+r)+t := by rw [←he,←hev]; abel
             _=t := by rw [hzero,zero_add]
      rw [hp']
      exact ht
  · exact inf_le_inf (T.nested i) le_rfl
end Intrinsic

end UploadBroadcast.TripodSubobjectExclusion
