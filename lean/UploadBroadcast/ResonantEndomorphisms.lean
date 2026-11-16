import UploadBroadcast.JordanResonance
import UploadBroadcast.StableEnd
import UploadBroadcast.NilpotentFiltration
import UploadBroadcast.ProjectionCriterion
import Mathlib.Tactic.LinearCombination

/-!
# Endomorphisms of the manuscript's resonant model

The ambient coordinates are exactly three private blocks and V,R. The six
submodules are the three side-information spaces and their demand enlargements;
`total₁_eq_side_sup_demand` and its companions verify this identification.
Preservation forces the displayed block form and commutant equations. A kernel
filtration argument proves scalar-plus-nilpotence, without assuming a polynomial
centralizer or invoking real-root uniqueness. The source coupling column may be
any column outside the image of the source Jordan block.

The parameter `n` in the Jordan specializations represents manuscript R_(n+1).
These calculations concern the explicit family; they do not classify all
zero-defect indecomposables or prove the paper's real-root uniqueness theorem.
-/
namespace UploadBroadcast.ResonantEndomorphisms
variable (K X : Type*) [Field K] [AddCommGroup X] [Module K X]

/-- The three private coefficient blocks and the scalar directions V,R. -/
abbrev Ambient := X × X × X × K × K

def E₁ : X →ₗ[K] Ambient K X where
  toFun x := (x,0,0,0,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def E₂ : X →ₗ[K] Ambient K X where
  toFun x := (0,x,0,0,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def E₃ : X →ₗ[K] Ambient K X where
  toFun x := (0,0,x,0,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def scalarV : K →ₗ[K] Ambient K X where
  toFun a := (0,0,0,a,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def scalarR : K →ₗ[K] Ambient K X where
  toFun a := (0,0,0,0,a)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def side₁ : Submodule K (Ambient K X) where
  carrier := {p | p.2.1 = 0 ∧ p.2.2.1 = 0 ∧ p.2.2.2.2 = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simp_all
  smul_mem' := by intro a b hb; simp_all

def side₂ : Submodule K (Ambient K X) where
  carrier := {p | p.1 = 0 ∧ p.2.2.1 = 0 ∧ p.2.2.2.1 = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simp_all
  smul_mem' := by intro a b hb; simp_all

def side₃ : Submodule K (Ambient K X) where
  carrier := {p | p.1 = 0 ∧ p.2.1 = 0 ∧ p.2.2.2.1 + p.2.2.2.2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    refine ⟨by simp_all, by simp_all, ?_⟩
    change (a.2.2.2.1 + b.2.2.2.1) + (a.2.2.2.2 + b.2.2.2.2) = 0
    linear_combination ha.2.2 + hb.2.2
  smul_mem' := by
    intro a b hb
    refine ⟨by simp_all, by simp_all, ?_⟩
    change a * b.2.2.2.1 + a * b.2.2.2.2 = 0
    rw [← mul_add, hb.2.2, mul_zero]

def total₁ : Submodule K (Ambient K X) where
  carrier := {p | p.2.1 = p.2.2.1 ∧ p.2.2.2.2 = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simp_all
  smul_mem' := by intro a b hb; simp_all

def total₂ : Submodule K (Ambient K X) where
  carrier := {p | p.1 = p.2.2.1 ∧ p.2.2.2.1 = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simp_all
  smul_mem' := by intro a b hb; simp_all

variable (J : X →ₗ[K] X) (h : X →ₗ[K] K)
def total₃ : Submodule K (Ambient K X) where
  carrier := {p | p.2.1 = p.1 + J p.1 ∧ p.2.2.2.1 + p.2.2.2.2 = h p.1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    constructor
    · change a.2.1 + b.2.1 = a.1 + b.1 + J (a.1 + b.1)
      rw [map_add, ha.1, hb.1]; abel
    · change (a.2.2.2.1 + b.2.2.2.1) + (a.2.2.2.2 + b.2.2.2.2) = h (a.1 + b.1)
      rw [map_add]; linear_combination ha.2 + hb.2
  smul_mem' := by
    intro a b hb
    constructor
    · change a • b.2.1 = a • b.1 + J (a • b.1)
      rw [map_smul, hb.1, smul_add]
    · change a * b.2.2.2.1 + a * b.2.2.2.2 = h (a • b.1)
      rw [map_smul, ← mul_add, hb.2]; rfl

/-- Six labels are exactly A₁,A₂,A₃,U₁,U₂,U₃ of the source model. -/
def spaces : Fin 6 → Submodule K (Ambient K X) :=
  ![side₁ K X, side₂ K X, side₃ K X, total₁ K X, total₂ K X, total₃ K X J h]

/-- The three demand-row embeddings, without any added demand cycle. -/
def demand₁ : X →ₗ[K] Ambient K X := E₂ K X + E₃ K X
def demand₂ : X →ₗ[K] Ambient K X := E₁ K X + E₃ K X
def demand₃ : X →ₗ[K] Ambient K X where
  toFun x := (x,x+J x,0,h x,0)
  map_add' x y := by simp [add_add_add_comm]
  map_smul' a x := by simp [smul_add]

/-- Exact equality with side information plus the first source demand. -/
theorem total₁_eq_side_sup_demand : total₁ K X =
    side₁ K X ⊔ LinearMap.range (demand₁ K X) := by
  ext p
  constructor
  · intro hp
    change p.2.1 = p.2.2.1 ∧ p.2.2.2.2 = 0 at hp
    apply Submodule.mem_sup.mpr
    refine ⟨(p.1,0,0,p.2.2.2.1,0), by simp [side₁],
      demand₁ K X p.2.1, ⟨_,rfl⟩, ?_⟩
    apply Prod.ext
    · simp [demand₁,E₂,E₃]
    apply Prod.ext
    · simp [demand₁,E₂,E₃]
    apply Prod.ext
    · simpa [demand₁,E₂,E₃] using hp.1
    apply Prod.ext
    · simp [demand₁,E₂,E₃]
    · simpa [demand₁,E₂,E₃] using hp.2.symm
  · rintro hp
    obtain ⟨a,ha,b,⟨x,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hp
    change a.2.1 = 0 ∧ a.2.2.1 = 0 ∧ a.2.2.2.2 = 0 at ha
    simp [total₁,demand₁,E₂,E₃,ha.1,ha.2.1,ha.2.2]

/-- Exact equality with side information plus the second source demand. -/
theorem total₂_eq_side_sup_demand : total₂ K X =
    side₂ K X ⊔ LinearMap.range (demand₂ K X) := by
  ext p
  constructor
  · intro hp
    change p.1 = p.2.2.1 ∧ p.2.2.2.1 = 0 at hp
    apply Submodule.mem_sup.mpr
    refine ⟨(0,p.2.1,0,0,p.2.2.2.2), by simp [side₂],
      demand₂ K X p.1, ⟨_,rfl⟩, ?_⟩
    apply Prod.ext
    · simp [demand₂,E₁,E₃]
    apply Prod.ext
    · simp [demand₂,E₁,E₃]
    apply Prod.ext
    · simpa [demand₂,E₁,E₃] using hp.1
    apply Prod.ext
    · simpa [demand₂,E₁,E₃] using hp.2.symm
    · simp [demand₂,E₁,E₃]
  · rintro hp
    obtain ⟨a,ha,b,⟨x,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hp
    change a.1 = 0 ∧ a.2.2.1 = 0 ∧ a.2.2.2.1 = 0 at ha
    simp [total₂,demand₂,E₁,E₃,ha.1,ha.2.1,ha.2.2]

/-- Exact equality with side information plus X₁+(I+J)X₂+hV. -/
theorem total₃_eq_side_sup_demand : total₃ K X J h =
    side₃ K X ⊔ LinearMap.range (demand₃ K X J h) := by
  ext p
  constructor
  · intro hp
    change p.2.1 = p.1 + J p.1 ∧ p.2.2.2.1 + p.2.2.2.2 = h p.1 at hp
    apply Submodule.mem_sup.mpr
    refine ⟨(0,0,p.2.2.1,-p.2.2.2.2,p.2.2.2.2), by simp [side₃],
      demand₃ K X J h p.1, ⟨_,rfl⟩, ?_⟩
    apply Prod.ext
    · simp [demand₃]
    apply Prod.ext
    · simpa [demand₃] using hp.1.symm
    apply Prod.ext
    · simp [demand₃]
    apply Prod.ext
    · change -p.2.2.2.2 + h p.1 = p.2.2.2.1
      linear_combination -hp.2
    · simp [demand₃]
  · rintro hp
    obtain ⟨a,ha,b,⟨x,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hp
    change a.1 = 0 ∧ a.2.1 = 0 ∧ a.2.2.2.1 + a.2.2.2.2 = 0 at ha
    change (a.2.1 + (x + J x)) = a.1 + x + J (a.1+x) ∧
      (a.2.2.2.1 + h x) + (a.2.2.2.2 + 0) = h (a.1+x)
    simp only [ha.1,ha.2.1,zero_add,add_zero]
    constructor
    · trivial
    · linear_combination ha.2.2

variable {K X}
/-- Preservation of the three side-information subspaces. -/
structure SideStable (f : Ambient K X →ₗ[K] Ambient K X) : Prop where
  one : ∀ p ∈ side₁ K X, f p ∈ side₁ K X
  two : ∀ p ∈ side₂ K X, f p ∈ side₂ K X
  three : ∀ p ∈ side₃ K X, f p ∈ side₃ K X

/-- The tripod's scalar plane is forced to carry a single scalar action.
The conclusion is derived from side-space preservation alone. -/
theorem scalar_action (f : Ambient K X →ₗ[K] Ambient K X) (hf : SideStable f) :
    ∃ α : K, (∀ a, f (scalarV K X a) = scalarV K X (α*a)) ∧
      (∀ a, f (scalarR K X a) = scalarR K X (α*a)) := by
  have hv := hf.one (scalarV K X 1) (by simp [side₁, scalarV])
  have hr := hf.two (scalarR K X 1) (by simp [side₂, scalarR])
  have ht := hf.three (scalarR K X 1 - scalarV K X 1) (by simp [side₃, scalarV, scalarR])
  change _ = 0 ∧ _ = 0 ∧ _ = 0 at hv hr ht
  rw [map_sub] at ht
  have hvx : (f (scalarV K X 1)).1 = 0 := by
    have := ht.1
    simpa [hr.1] using this
  have hrx : (f (scalarR K X 1)).2.1 = 0 := by
    have := ht.2.1
    simpa [hv.1] using this
  have hs : (f (scalarR K X 1)).2.2.2.2 = (f (scalarV K X 1)).2.2.2.1 := by
    have := ht.2.2
    change ((f (scalarR K X 1)).2.2.2.1 - (f (scalarV K X 1)).2.2.2.1) +
      ((f (scalarR K X 1)).2.2.2.2 - (f (scalarV K X 1)).2.2.2.2) = 0 at this
    rw [hr.2.2, hv.2.2] at this
    linear_combination this
  let α := (f (scalarV K X 1)).2.2.2.1
  have hv' : f (scalarV K X 1) = scalarV K X α := by
    apply Prod.ext hvx
    apply Prod.ext hv.1
    apply Prod.ext hv.2.1
    exact Prod.ext rfl hv.2.2
  have hr' : f (scalarR K X 1) = scalarR K X α := by
    apply Prod.ext hr.1
    apply Prod.ext hrx
    apply Prod.ext hr.2.1
    exact Prod.ext hr.2.2 hs
  refine ⟨α, ?_, ?_⟩
  · intro a
    have he : scalarV K X a = a • scalarV K X 1 := by simp [← map_smul]
    rw [he, map_smul, hv', ← map_smul]
    congr 1
    exact mul_comm a α
  · intro a
    have he : scalarR K X a = a • scalarR K X 1 := by simp [← map_smul]
    rw [he, map_smul, hr', ← map_smul]
    congr 1
    exact mul_comm a α

/-- The exact block form asserted by the manuscript. -/
def BlockForm (f : Ambient K X →ₗ[K] Ambient K X) (α : K)
    (B : X →ₗ[K] X) (g : X →ₗ[K] K) : Prop :=
  ∀ p, f p = (B p.1, B p.2.1, B p.2.2.1,
    g p.1 - g p.2.2.1 + α * p.2.2.2.1,
    -g p.2.1 + g p.2.2.1 + α * p.2.2.2.2)

/-- Side preservation and the first two enlarged spaces force the full block form. -/
theorem block_form_of_preservation
    (f : Ambient K X →ₗ[K] Ambient K X) (hf : SideStable f)
    (hu₁ : ∀ p ∈ total₁ K X, f p ∈ total₁ K X)
    (hu₂ : ∀ p ∈ total₂ K X, f p ∈ total₂ K X) :
    ∃ (α : K) (B : X →ₗ[K] X) (g : X →ₗ[K] K), BlockForm f α B g := by
  obtain ⟨α, hV, hR⟩ := scalar_action f hf
  let B : X →ₗ[K] X := (LinearMap.fst K X (X × X × K × K)).comp (f.comp (E₁ K X))
  let g : X →ₗ[K] K :=
    (LinearMap.fst K K K).comp ((LinearMap.snd K X (K × K)).comp
      ((LinearMap.snd K X (X × K × K)).comp
        ((LinearMap.snd K X (X × X × K × K)).comp (f.comp (E₁ K X)))))
  have h₁ (x : X) : f (E₁ K X x) = (B x,0,0,g x,0) := by
    have hh := hf.one (E₁ K X x) (by simp [E₁, side₁])
    change _ = 0 ∧ _ = 0 ∧ _ = 0 at hh
    exact Prod.ext rfl (Prod.ext hh.1 (Prod.ext hh.2.1 (Prod.ext rfl hh.2.2)))
  have h₂₃ (x : X) : f (E₂ K X x) = (0,B x,0,0,-g x) ∧
      f (E₃ K X x) = (0,0,B x,-g x,g x) := by
    have h₂ := hf.two (E₂ K X x) (by simp [E₂, side₂])
    have h₃ := hf.three (E₃ K X x) (by simp [E₃, side₃])
    have h₂₃ := hu₁ (E₂ K X x + E₃ K X x) (by simp [E₂, E₃, total₁])
    have h₁₃ := hu₂ (E₁ K X x + E₃ K X x) (by simp [E₁, E₃, total₂])
    change _ = 0 ∧ _ = 0 ∧ _ = 0 at h₂ h₃
    change _ = _ ∧ _ = 0 at h₂₃ h₁₃
    rw [map_add] at h₂₃ h₁₃
    rw [h₁] at h₁₃
    have hb₃ : (f (E₃ K X x)).2.2.1 = B x := by
      simpa [h₃.1] using h₁₃.1.symm
    have hb₂ : (f (E₂ K X x)).2.1 = B x := by
      simpa [h₃.2.1, h₂.2.1, hb₃] using h₂₃.1
    have hv₃ : (f (E₃ K X x)).2.2.2.1 = -g x := by
      have hh := h₁₃.2
      change g x + (f (E₃ K X x)).2.2.2.1 = 0 at hh
      linear_combination hh
    have hr₃ : (f (E₃ K X x)).2.2.2.2 = g x := by
      have hh := h₃.2.2
      rw [hv₃] at hh
      linear_combination hh
    have hr₂ : (f (E₂ K X x)).2.2.2.2 = -g x := by
      have hh := h₂₃.2
      change (f (E₂ K X x)).2.2.2.2 + (f (E₃ K X x)).2.2.2.2 = 0 at hh
      rw [hr₃] at hh
      linear_combination hh
    exact ⟨Prod.ext h₂.1 (Prod.ext hb₂ (Prod.ext h₂.2.1 (Prod.ext h₂.2.2 hr₂))),
      Prod.ext h₃.1 (Prod.ext h₃.2.1 (Prod.ext hb₃ (Prod.ext hv₃ hr₃)))⟩
  refine ⟨α, B, g, ?_⟩
  intro p
  have hp : p = E₁ K X p.1 + E₂ K X p.2.1 + E₃ K X p.2.2.1 +
      scalarV K X p.2.2.2.1 + scalarR K X p.2.2.2.2 := by simp [E₁,E₂,E₃,scalarV,scalarR]
  calc
    f p = f (E₁ K X p.1) + f (E₂ K X p.2.1) + f (E₃ K X p.2.2.1) +
      f (scalarV K X p.2.2.2.1) + f (scalarR K X p.2.2.2.2) := by
        rw [← map_add, ← map_add, ← map_add, ← map_add, ← hp]
    _ = _ := by
      rw [h₁, (h₂₃ _).1, (h₂₃ _).2, hV, hR]
      simp [scalarV, scalarR, sub_eq_add_neg]

/-- The third enlarged space imposes precisely the commutant and coupling equations. -/
theorem commutant_of_preservation (f : Ambient K X →ₗ[K] Ambient K X)
    (α : K) (B : X →ₗ[K] X) (g : X →ₗ[K] K)
    (hf : BlockForm f α B g) (J : X →ₗ[K] X) (h : X →ₗ[K] K)
    (hu₃ : ∀ p ∈ total₃ K X J h, f p ∈ total₃ K X J h) :
    (∀ x, B (J x) = J (B x)) ∧ (∀ x, h (B x) - α * h x = -g (J x)) := by
  have hh (x : X) := hu₃ (x, x + J x, 0, h x, 0) (by simp [total₃])
  constructor
  · intro x
    have hx := (hh x).1
    rw [hf] at hx
    change B (x + J x) = B x + J (B x) at hx
    simpa using hx
  · intro x
    have hx := (hh x).2
    rw [hf] at hx
    change (g x - g 0 + α * h x) + (-g (x + J x) + g 0 + α * 0) = h (B x) at hx
    simp only [map_zero, sub_zero, mul_zero, add_zero, map_add] at hx
    linear_combination -hx

theorem subtract_scalar_block (f : Ambient K X →ₗ[K] Ambient K X)
    (α : K) (B : X →ₗ[K] X) (g : X →ₗ[K] K) (hf : BlockForm f α B g) :
    BlockForm (f - α • LinearMap.id) 0 (B - α • LinearMap.id) g := by
  rintro ⟨x,y,z,v,r⟩
  change f (x,y,z,v,r) - α • (x,y,z,v,r) = _
  rw [hf]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Prod.mk_sub_mk, Prod.smul_mk, zero_mul, add_zero]
  simp [smul_eq_mul]

theorem block_nilpotent (f : Ambient K X →ₗ[K] Ambient K X)
    (B : X →ₗ[K] X) (g : X →ₗ[K] K) (hf : BlockForm f 0 B g)
    (m : ℕ) (hB : B^m = 0) : f^(m+1) = 0 := by
  have hp (k : ℕ) (p : Ambient K X) :
      ((f^k) p).1 = (B^k) p.1 ∧ ((f^k) p).2.1 = (B^k) p.2.1 ∧
      ((f^k) p).2.2.1 = (B^k) p.2.2.1 := by
    induction k with
    | zero => exact ⟨rfl,rfl,rfl⟩
    | succ k ih =>
      rw [pow_succ', pow_succ']
      change (f ((f^k) p)).1 = B ((B^k) p.1) ∧
        (f ((f^k) p)).2.1 = B ((B^k) p.2.1) ∧
        (f ((f^k) p)).2.2.1 = B ((B^k) p.2.2.1)
      rw [hf]
      exact ⟨congrArg B ih.1, congrArg B ih.2.1, congrArg B ih.2.2⟩
  apply LinearMap.ext
  intro p
  rw [pow_succ']
  change f ((f^m) p) = 0
  rw [hf]
  obtain ⟨h₁,h₂,h₃⟩ := hp m p
  rw [hB] at h₁ h₂ h₃
  simp only [LinearMap.zero_apply] at h₁ h₂ h₃
  simp [h₁,h₂,h₃]

/-- No cyclic-centralizer theorem is needed: the coupling detects the kernel,
and commutation lowers the kernel filtration. -/
theorem private_nilpotent (α : K) (B J : X →ₗ[K] X) (g h : X →ₗ[K] K)
    (hc : ∀ x, B (J x) = J (B x))
    (hg : ∀ x, h (B x) - α * h x = -g (J x))
    (hdetect : ∀ x, J x = 0 → h x = 0 → x = 0)
    (m : ℕ) (hJ : J^m = 0) : (B - α • LinearMap.id)^m = 0 := by
  let D := B - α • LinearMap.id
  have hd (x : X) : D x = B x - α • x := rfl
  have hcomm : Commute D J := by
    apply LinearMap.ext
    intro x
    change D (J x) = J (D x)
    simp only [hd, map_sub, map_smul, hc]
  apply NilpotentFiltration.pow_eq_zero_of_commute hcomm _ hJ
  intro x hx
  change J x = 0 at hx
  change D x = 0
  apply hdetect
  · rw [hd, map_sub, map_smul, ← hc, hx, map_zero, smul_zero, sub_self]
  · rw [hd, map_sub, map_smul]
    change h (B x) - α * h x = 0
    rw [hg, hx, map_zero, neg_zero]

/-- Every endomorphism of the explicit resonant configuration is scalar plus
nilpotent, over any field, with an explicit exponent. -/
theorem scalar_plus_nilpotent (J : X →ₗ[K] X) (h : X →ₗ[K] K)
    (hdetect : ∀ x, J x = 0 → h x = 0 → x = 0)
    (m : ℕ) (hJ : J^m = 0)
    (f : Ambient K X →ₗ[K] Ambient K X)
    (hf : TaskDecomposition.Stable (spaces K X J h) f) :
    ∃ α : K, (f - α • LinearMap.id)^(m+1) = 0 := by
  have hs : SideStable f :=
    ⟨by simpa [spaces] using hf 0, by simpa [spaces] using hf 1,
      by simpa [spaces] using hf 2⟩
  obtain ⟨α,B,g,hform⟩ := block_form_of_preservation f hs
    (by simpa [spaces] using hf 3) (by simpa [spaces] using hf 4)
  obtain ⟨hc,hg⟩ := commutant_of_preservation f α B g hform J h
    (by simpa [spaces] using hf 5)
  exact ⟨α, block_nilpotent _ _ g (subtract_scalar_block f α B g hform) m
    (private_nilpotent α B J g h hc hg hdetect m hJ)⟩

/-- The arbitrary-field single-Jordan-block specialization of the source model. -/
theorem jordan_scalar_plus_nilpotent (K : Type*) [Field K] (n : ℕ)
    (f : Ambient K (JordanResonance.V K n) →ₗ[K] Ambient K (JordanResonance.V K n))
    (hf : TaskDecomposition.Stable
      (spaces K (JordanResonance.V K n) (JordanResonance.shift K n) (JordanResonance.head K n)) f) :
    ∃ α : K, (f - α • LinearMap.id)^(n+2) = 0 := by
  apply scalar_plus_nilpotent _ _ _ (n+1) (JordanResonance.shift_nilpotent K n) f hf
  intro x hx hh
  apply JordanResonance.fixed_head_eq_zero K n x _ hh
  change x + JordanResonance.shift K n x = x
  rw [hx, add_zero]

/-- For the single Jordan shift, the first-coordinate vector spans its kernel. -/
theorem jordan_kernel_coordinate (K : Type*) [Field K] (n : ℕ)
    (x : JordanResonance.V K n) (hx : JordanResonance.shift K n x = 0) :
    x = x 0 • JordanResonance.sourceColumn K n := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [JordanResonance.sourceColumn]
  · have hj := congrFun hx j.castSucc
    simpa [JordanResonance.sourceColumn] using hj

/-- Any coupling nonzero on the kernel works, not only the normalized coordinate head. -/
theorem jordan_coupling_detects (K : Type*) [Field K] (n : ℕ)
    (h : JordanResonance.V K n →ₗ[K] K)
    (hh : h (JordanResonance.sourceColumn K n) ≠ 0)
    (x : JordanResonance.V K n) (hx : JordanResonance.shift K n x = 0)
    (hz : h x = 0) : x = 0 := by
  have he := jordan_kernel_coordinate K n x hx
  have hc : x 0 = 0 := by
    rw [he, map_smul] at hz
    exact (mul_eq_zero.mp hz).resolve_right hh
  rw [he, hc, zero_smul]

/-- The source condition that the coupling column lies outside the source
Jordan image is exactly nonzero first coordinate. -/
theorem column_outside_image_iff (K : Type*) [Field K] (n : ℕ)
    (c : JordanResonance.V K n) :
    c ∉ LinearMap.range (JordanResonance.sourceShift K n) ↔ c 0 ≠ 0 := by
  constructor
  · intro hc hz
    apply hc
    refine ⟨JordanResonance.shift K n c, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [JordanResonance.sourceShift] using hz.symm
    · change JordanResonance.shift K n c j.castSucc = c j.succ
      exact JordanResonance.shift_castSucc K n c j
  · intro hc hr
    obtain ⟨x,rfl⟩ := hr
    exact hc rfl

/-- Evaluation by the source coupling column, i.e. its transposed row. -/
def columnForm (K : Type*) [Field K] (n : ℕ) (c : JordanResonance.V K n) :
    JordanResonance.V K n →ₗ[K] K where
  toFun x := ∑ i, c i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum, mul_left_comm]

theorem columnForm_on_kernel_vector (K : Type*) [Field K] (n : ℕ)
    (c : JordanResonance.V K n) :
    columnForm K n c (JordanResonance.sourceColumn K n) = c 0 := by
  simp [columnForm, JordanResonance.sourceColumn, Fin.sum_univ_succ]

/-- The complete source choice h ∉ im N, without normalizing that column. -/
theorem source_scalar_plus_nilpotent (K : Type*) [Field K] (n : ℕ)
    (c : JordanResonance.V K n)
    (hc : c ∉ LinearMap.range (JordanResonance.sourceShift K n))
    (f : Ambient K (JordanResonance.V K n) →ₗ[K] Ambient K (JordanResonance.V K n))
    (hf : TaskDecomposition.Stable
      (spaces K (JordanResonance.V K n) (JordanResonance.shift K n) (columnForm K n c)) f) :
    ∃ α : K, (f - α • LinearMap.id)^(n+2) = 0 := by
  apply scalar_plus_nilpotent _ _ _ (n+1) (JordanResonance.shift_nilpotent K n) f hf
  apply jordan_coupling_detects K n
  rw [columnForm_on_kernel_vector]
  exact (column_outside_image_iff K n c).mp hc

theorem jordan_idempotent_trivial (K : Type*) [Field K] (n : ℕ)
    (f : Ambient K (JordanResonance.V K n) →ₗ[K] Ambient K (JordanResonance.V K n))
    (hf : TaskDecomposition.Stable
      (spaces K (JordanResonance.V K n) (JordanResonance.shift K n) (JordanResonance.head K n)) f)
    (hi : IsIdempotentElem f) : f = 0 ∨ f = 1 := by
  obtain ⟨α,hα⟩ := jordan_scalar_plus_nilpotent K n f hf
  exact NilpotentFiltration.idempotent_eq_zero_or_one_of_sub_smul_nilpotent hi α ⟨n+2,hα⟩

/-- The source's nondegenerate coupling condition survives every field map. -/
theorem map_column_outside_image {K L : Type*} [Field K] [Field L]
    (σ : K →+* L) (n : ℕ) (c : JordanResonance.V K n)
    (hc : c ∉ LinearMap.range (JordanResonance.sourceShift K n)) :
    (fun i => σ (c i)) ∉ LinearMap.range (JordanResonance.sourceShift L n) := by
  apply (column_outside_image_iff L n _).mpr
  exact (map_ne_zero σ).mpr ((column_outside_image_iff K n c).mp hc)

theorem source_idempotent_trivial (K : Type*) [Field K] (n : ℕ)
    (c : JordanResonance.V K n)
    (hc : c ∉ LinearMap.range (JordanResonance.sourceShift K n))
    (f : Ambient K (JordanResonance.V K n) →ₗ[K] Ambient K (JordanResonance.V K n))
    (hf : TaskDecomposition.Stable
      (spaces K (JordanResonance.V K n) (JordanResonance.shift K n) (columnForm K n c)) f)
    (hi : IsIdempotentElem f) : f = 0 ∨ f = 1 := by
  obtain ⟨α,hα⟩ := source_scalar_plus_nilpotent K n c hc f hf
  exact NilpotentFiltration.idempotent_eq_zero_or_one_of_sub_smul_nilpotent hi α ⟨n+2,hα⟩

/-- Indecomposability of the actual source resonant model for every allowed
coupling column and every ground field. -/
theorem source_indecomposable (K : Type*) [Field K] (n : ℕ)
    (c : JordanResonance.V K n)
    (hc : c ∉ LinearMap.range (JordanResonance.sourceShift K n)) :
    TaskDecomposition.Indecomposable
      (spaces K (JordanResonance.V K n) (JordanResonance.shift K n) (columnForm K n c)) ⊤ := by
  apply TaskDecomposition.indecomposable_of_projection_eq_zero_or_id
  · exact top_ne_bot
  · intro f hf hi
    apply source_idempotent_trivial K n c hc f hf
    apply LinearMap.ext
    exact hi

/-- The canonical normalized model is indecomposable over every field. -/
theorem jordan_indecomposable (K : Type*) [Field K] (n : ℕ) :
    TaskDecomposition.Indecomposable
      (spaces K (JordanResonance.V K n) (JordanResonance.shift K n) (JordanResonance.head K n)) ⊤ := by
  apply TaskDecomposition.indecomposable_of_projection_eq_zero_or_id
  · exact top_ne_bot
  · intro f hf hi
    apply jordan_idempotent_trivial K n f hf
    apply LinearMap.ext
    exact hi

/-- Replacing the coefficient field along any field map gives an indecomposable
coordinate model. Tensor-product compatibility is established separately. -/
theorem source_indecomposable_over_field_map {K L : Type*} [Field K] [Field L]
    (σ : K →+* L) (n : ℕ) (c : JordanResonance.V K n)
    (hc : c ∉ LinearMap.range (JordanResonance.sourceShift K n)) :
    TaskDecomposition.Indecomposable
      (spaces L (JordanResonance.V L n) (JordanResonance.shift L n)
        (columnForm L n (fun i => σ (c i)))) ⊤ :=
  source_indecomposable L n _ (map_column_outside_image σ n c hc)

#print axioms scalar_plus_nilpotent
#print axioms jordan_idempotent_trivial
#print axioms source_idempotent_trivial
#print axioms source_indecomposable
end UploadBroadcast.ResonantEndomorphisms
