import UploadBroadcast.SignalBridge
import UploadBroadcast.LinearEntropy
import UploadBroadcast.ActiveReduction
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Exact residual-coordinate rank and row-upload calculations

The private and tripod coordinates are actual product vector spaces. Pure
row spaces are kept separate from projections of mixed demands. This module
provides explicit row-level upload constructions; the global simultaneous
normal-form assembly is a separate step.
-/
namespace UploadBroadcast.ResidualUpload
open Module
variable {K P₁ P₂ P₃ T : Type*} [Field K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup T] [Module K T]

abbrev Ambient (P₁ P₂ P₃ T : Type*) := ((P₁ × P₂) × P₃) × (T × T)

def side₁ : (P₁ × T) →ₗ[K] Ambient P₁ P₂ P₃ T where
  toFun x := (((x.1, 0), 0), (x.2, 0))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def side₂ : (P₂ × T) →ₗ[K] Ambient P₁ P₂ P₃ T where
  toFun x := (((0, x.1), 0), (0, x.2))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def side₃ : (P₃ × T) →ₗ[K] Ambient P₁ P₂ P₃ T where
  toFun x := (((0, 0), x.1), (-x.2, x.2))
  map_add' x y := by simp [add_comm]
  map_smul' a x := by simp

theorem side₁_injective : Function.Injective (side₁ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := T)) := by
  intro x y h
  exact Prod.ext (congrArg (fun z => z.1.1.1) h) (congrArg (fun z => z.2.1) h)

theorem side₂_injective : Function.Injective (side₂ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := T)) := by
  intro x y h
  exact Prod.ext (congrArg (fun z => z.1.1.2) h) (congrArg (fun z => z.2.2) h)

theorem side₃_injective : Function.Injective (side₃ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := T)) := by
  intro x y h
  exact Prod.ext (congrArg (fun z => z.1.2) h) (congrArg (fun z => z.2.2) h)

variable (K P₁ P₂ P₃ T)

def A₁ : Submodule K (Ambient P₁ P₂ P₃ T) := LinearMap.range side₁
def A₂ : Submodule K (Ambient P₁ P₂ P₃ T) := LinearMap.range side₂
def A₃ : Submodule K (Ambient P₁ P₂ P₃ T) := LinearMap.range side₃

variable {K P₁ P₂ P₃ T}

theorem sides_span : A₁ K P₁ P₂ P₃ T ⊔ A₂ K P₁ P₂ P₃ T ⊔ A₃ K P₁ P₂ P₃ T = ⊤ := by
  apply top_unique
  intro x _
  have h1 : side₁ (x.1.1.1, x.2.1 + x.2.2) ∈ A₁ K P₁ P₂ P₃ T := ⟨_, rfl⟩
  have h2 : side₂ (x.1.1.2, (0 : T)) ∈ A₂ K P₁ P₂ P₃ T := ⟨_, rfl⟩
  have h3 : side₃ (x.1.2, x.2.2) ∈ A₃ K P₁ P₂ P₃ T := ⟨_, rfl⟩
  have hh := Submodule.add_mem_sup (Submodule.add_mem_sup h1 h2) h3
  convert hh using 1; simp [side₁, side₂, side₃]

theorem sides_disjoint₁₂ : Disjoint (A₁ K P₁ P₂ P₃ T) (A₂ K P₁ P₂ P₃ T) := by
  apply Submodule.disjoint_def.mpr
  rintro z ⟨x, rfl⟩ ⟨y, h⟩
  have hp := congrArg (fun z : Ambient P₁ P₂ P₃ T => z.1.1.1) h
  have ht := congrArg (fun z : Ambient P₁ P₂ P₃ T => z.2.1) h
  simp only [side₂, side₁, LinearMap.coe_mk, AddHom.coe_mk] at hp ht ⊢
  simp [← hp, ← ht]

theorem sides_disjoint₁₃ : Disjoint (A₁ K P₁ P₂ P₃ T) (A₃ K P₁ P₂ P₃ T) := by
  apply Submodule.disjoint_def.mpr
  rintro z ⟨x, rfl⟩ ⟨y, h⟩
  have hp := congrArg (fun z : Ambient P₁ P₂ P₃ T => z.1.1.1) h
  have ht := congrArg (fun z : Ambient P₁ P₂ P₃ T => z.2.1) h
  have hy := congrArg (fun z : Ambient P₁ P₂ P₃ T => z.2.2) h
  simp only [side₃, side₁, LinearMap.coe_mk, AddHom.coe_mk] at hp ht hy ⊢
  simp [hy] at ht
  simp [← hp, ← ht]

theorem sides_disjoint₂₃ : Disjoint (A₂ K P₁ P₂ P₃ T) (A₃ K P₁ P₂ P₃ T) := by
  apply Submodule.disjoint_def.mpr
  rintro z ⟨x, rfl⟩ ⟨y, h⟩
  have hp := congrArg (fun z : Ambient P₁ P₂ P₃ T => z.1.1.2) h
  have ht := congrArg (fun z : Ambient P₁ P₂ P₃ T => z.2.2) h
  have hy := congrArg (fun z : Ambient P₁ P₂ P₃ T => z.2.1) h
  simp only [side₃, side₂, LinearMap.coe_mk, AddHom.coe_mk] at hp ht hy ⊢
  have hy' : y.2 = 0 := neg_eq_zero.mp hy
  simp [hy'] at ht
  simp [← hp, ← ht]

section FiniteRank
variable [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K T]

/-- The residual Γ rank identity is derived from the actual three embeddings. -/
theorem gamma_rank :
    2 * (finrank K (Ambient P₁ P₂ P₃ T) : ℤ) -
      (finrank K (A₁ K P₁ P₂ P₃ T) + finrank K (A₂ K P₁ P₂ P₃ T) +
       finrank K (A₃ K P₁ P₂ P₃ T)) =
    finrank K P₁ + finrank K P₂ + finrank K P₃ + finrank K T := by
  rw [A₁, A₂, A₃, LinearMap.finrank_range_of_inj side₁_injective,
    LinearMap.finrank_range_of_inj side₂_injective, LinearMap.finrank_range_of_inj side₃_injective]
  simp only [Ambient, Module.finrank_prod]
  omega

open MeasureTheory ProbabilityTheory
local instance sourceMeasurable (E : Type*) [AddCommGroup E] [Module K E] (n : ℕ) :
    MeasurableSpace (Source K E n) := ⊤
local instance sourceDiscrete (E : Type*) [AddCommGroup E] [Module K E] (n : ℕ) :
    DiscreteMeasurableSpace (Source K E n) := ⟨fun _ => trivial⟩

/-- The derived Γ identity for genuine Shannon entropy of the actual uniform
block source, in base-|K| units. The full observation is equivalent to the
joint side observations because `sides_span` was proved above. -/
theorem gamma_entropy [Finite K] (n : ℕ) :
    let F := Ambient P₁ P₂ P₃ T
    let H := fun B : Submodule K F =>
      entropy (observe K F B : Source K F n → Source K B n)
        (uniformOn (Set.univ : Set (Source K F n))) / Real.log (Nat.card K)
    2 * H ⊤ - (H (A₁ K P₁ P₂ P₃ T) + H (A₂ K P₁ P₂ P₃ T) +
      H (A₃ K P₁ P₂ P₃ T)) =
      (n : ℝ) * (finrank K P₁ + finrank K P₂ + finrank K P₃ + finrank K T) := by
  dsimp only
  rw [LinearObservation.model_entropy_rank, LinearObservation.model_entropy_rank,
    LinearObservation.model_entropy_rank, LinearObservation.model_entropy_rank,
    finrank_top]
  have hr : 2 * (finrank K (Ambient P₁ P₂ P₃ T) : ℝ) -
      (finrank K (A₁ K P₁ P₂ P₃ T) + finrank K (A₂ K P₁ P₂ P₃ T) +
       finrank K (A₃ K P₁ P₂ P₃ T)) =
      finrank K P₁ + finrank K P₂ + finrank K P₃ + finrank K T := by
    exact_mod_cast (gamma_rank (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := T))
  nlinarith

/-- Pairwise independence is proved from the actual disjoint coefficient
subspaces and actual uniform law; it is not assumed as an entropy axiom. -/
theorem side_observations_pairwise_independent [Finite K] (n : ℕ) :
    let F := Ambient P₁ P₂ P₃ T
    let μ := uniformOn (Set.univ : Set (Source K F n))
    let W₁ := observe K F (A₁ K P₁ P₂ P₃ T) (L := n)
    let W₂ := observe K F (A₂ K P₁ P₂ P₃ T) (L := n)
    let W₃ := observe K F (A₃ K P₁ P₂ P₃ T) (L := n)
    IndepFun W₁ W₂ μ ∧ IndepFun W₁ W₃ μ ∧ IndepFun W₂ W₃ μ := by
  dsimp only
  let F := Ambient P₁ P₂ P₃ T
  letI : Finite (Source K F n) := Module.finite_of_finite K
  have hi (B C : Submodule K F) (hBC : Disjoint B C) :
      IndepFun (observe K F B (L := n)) (observe K F C (L := n))
        (uniformOn (Set.univ : Set (Source K F n))) := by
    letI : FiniteRange (observe K F B (L := n)) := ⟨Set.finite_range _⟩
    letI : FiniteRange (observe K F C (L := n)) := ⟨Set.finite_range _⟩
    have hq : (1 : ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
    have hlog : Real.log (Nat.card K) ≠ 0 := ne_of_gt (Real.log_pos hq)
    apply (mutualInfo_eq_zero Measurable.of_discrete Measurable.of_discrete).mp
    have hr := LinearObservation.model_mutualInfo_rank B C n
    rw [disjoint_iff.mp hBC, finrank_bot, Nat.cast_zero, mul_zero] at hr
    exact (div_eq_zero_iff.mp hr).resolve_right hlog
  exact ⟨hi _ _ sides_disjoint₁₂, hi _ _ sides_disjoint₁₃, hi _ _ sides_disjoint₂₃⟩

end FiniteRank

/-- Any row-coordinate demand on the remote private subspace extends to a
sum of corrections from the two remote users. This is a proved extension,
not a hypothesis that mixed-demand projections are pure demands. -/
theorem cancel_row_coordinate {P Q W : Type*}
    [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
    [AddCommGroup W] [Module K W]
    (L : Submodule K (P × Q)) (φ : L →ₗ[K] W) :
    ∃ (g : P →ₗ[K] W) (h : Q →ₗ[K] W),
      ∀ x : L, φ x + g x.val.1 + h x.val.2 = 0 := by
  obtain ⟨f, hf⟩ := (-φ).exists_extend
  refine ⟨f.comp (LinearMap.inl K P Q), f.comp (LinearMap.inr K P Q), ?_⟩
  intro x
  have he : f x.val = -φ x := LinearMap.congr_fun hf x
  have hh : f (x.val.1, 0) + f (0, x.val.2) = -φ x := by
    rw [← map_add]
    simpa using he
  change φ x + f (x.val.1, 0) + f (0, x.val.2) = 0
  rw [add_assoc, hh, add_neg_cancel]

/-- The actual simultaneous private-to-tripod correction in coefficient
coordinates. It fixes all tripod coordinates and has square zero. -/
def privateCorrection (g₁ : P₁ →ₗ[K] T) (g₂ : P₂ →ₗ[K] T) (g₃ : P₃ →ₗ[K] T) :
    Ambient P₁ P₂ P₃ T →ₗ[K] Ambient P₁ P₂ P₃ T where
  toFun x := (((0, 0), 0), (g₁ x.1.1.1 - g₃ x.1.2, g₂ x.1.1.2 + g₃ x.1.2))
  map_add' x y := by ext <;> simp [map_add] <;> abel
  map_smul' a x := by ext <;> simp [map_smul, smul_sub, smul_add]

theorem privateCorrection_square_zero
    (g₁ : P₁ →ₗ[K] T) (g₂ : P₂ →ₗ[K] T) (g₃ : P₃ →ₗ[K] T) :
    (privateCorrection g₁ g₂ g₃).comp (privateCorrection g₁ g₂ g₃) = 0 := by
  ext x <;> simp [privateCorrection]

/-- One simultaneous invertible shear preserves all three side spaces exactly. -/
theorem privateShear_preserves
    (g₁ : P₁ →ₗ[K] T) (g₂ : P₂ →ₗ[K] T) (g₃ : P₃ →ₗ[K] T) :
    let e := squareZeroShear (privateCorrection g₁ g₂ g₃) (privateCorrection_square_zero g₁ g₂ g₃)
    (A₁ K P₁ P₂ P₃ T).map e.toLinearMap = A₁ K P₁ P₂ P₃ T ∧
    (A₂ K P₁ P₂ P₃ T).map e.toLinearMap = A₂ K P₁ P₂ P₃ T ∧
    (A₃ K P₁ P₂ P₃ T).map e.toLinearMap = A₃ K P₁ P₂ P₃ T := by
  dsimp only
  refine ⟨squareZeroShear_preserves _ _ _ ?_, squareZeroShear_preserves _ _ _ ?_,
    squareZeroShear_preserves _ _ _ ?_⟩
  · rintro _ ⟨x,rfl⟩
    exact ⟨(0,g₁ x.1), by simp [side₁,privateCorrection]⟩
  · rintro _ ⟨x,rfl⟩
    exact ⟨(0,g₂ x.1), by simp [side₂,privateCorrection]⟩
  · rintro _ ⟨x,rfl⟩
    exact ⟨(0,g₃ x.1), by simp [side₃,privateCorrection]⟩

section RowAtoms
variable {E : Type*} [AddCommGroup E] [Module K E]

/-- The v, r, and r-v side-information lines, with arbitrary row multiplicity. -/
def vMap : E →ₗ[K] (E × E) := LinearMap.inl K E E
def rMap : E →ₗ[K] (E × E) := LinearMap.inr K E E
def diffMap : E →ₗ[K] (E × E) := rMap - vMap

theorem v_sup_r : LinearMap.range (vMap (K := K) (E := E)) ⊔
    LinearMap.range (rMap (K := K) (E := E)) = ⊤ := by
  apply top_unique
  rintro ⟨v, r⟩ _
  exact Submodule.mem_sup.mpr ⟨(v, 0), ⟨v, rfl⟩, (0, r), ⟨r, rfl⟩, by simp⟩

theorem v_sup_diff : LinearMap.range (vMap (K := K) (E := E)) ⊔
    LinearMap.range (diffMap (K := K) (E := E)) = ⊤ := by
  apply top_unique
  rintro ⟨v, r⟩ _
  exact Submodule.mem_sup.mpr ⟨(v+r, 0), ⟨v+r, rfl⟩, (-r, r), ⟨r, by simp [diffMap, vMap, rMap]⟩,
    by simp⟩

theorem r_sup_diff : LinearMap.range (rMap (K := K) (E := E)) ⊔
    LinearMap.range (diffMap (K := K) (E := E)) = ⊤ := by
  apply top_unique
  rintro ⟨v, r⟩ _
  exact Submodule.mem_sup.mpr ⟨(0, r+v), ⟨r+v, rfl⟩, (v, -v), ⟨-v, by simp [diffMap, vMap, rMap]⟩,
    by simp⟩

/-- Uploading v on a pure row supplies both coordinates to users 2 and 3;
the uploading user only needs its own side coordinate after the shear. -/
theorem one_row_upload :
    LinearMap.range (vMap (K := K) (E := E)) ≤ LinearMap.range vMap ∧
    LinearMap.range (rMap (K := K) (E := E)) ⊔ LinearMap.range vMap = ⊤ ∧
    LinearMap.range (diffMap (K := K) (E := E)) ⊔ LinearMap.range vMap = ⊤ := by
  exact ⟨le_rfl, by rw [sup_comm]; exact v_sup_r,
    by rw [sup_comm]; exact v_sup_diff⟩

/-- On a two-row diamond, upload a⊗r from user 2 and b⊗v from user 1. -/
def diamondUpload : (E × E) →ₗ[K] ((E × E) × (E × E)) where
  toFun x := ((0, x.2), (x.1, 0))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

theorem diamondUpload_injective : Function.Injective (diamondUpload (K := K) (E := E)) := by
  intro x y h
  exact Prod.ext (congrArg (fun z => z.2.1) h) (congrArg (fun z => z.1.2) h)

/-- Each upload generator is locally known; the two users' ranges span the
relay space exactly. -/
theorem diamond_locally_generated :
    LinearMap.range (diamondUpload (K := K) (E := E)) =
      (LinearMap.range (diamondUpload (K := K) (E := E)) ⊓ LinearMap.range vMap) ⊔
      (LinearMap.range (diamondUpload (K := K) (E := E)) ⊓ LinearMap.range rMap) := by
  apply le_antisymm
  · rintro _ ⟨⟨a,b⟩, rfl⟩
    apply Submodule.mem_sup.mpr
    refine ⟨diamondUpload (0,b), ⟨⟨(0,b), rfl⟩, ⟨(0,b), ?_⟩⟩,
      diamondUpload (a,0), ⟨⟨(a,0), rfl⟩, ⟨(a,0), ?_⟩⟩, ?_⟩
    · rfl
    · rfl
    · simp [diamondUpload]
  · exact sup_le inf_le_left inf_le_left

/-- User 1 recovers every vector whose missing r-coordinate is along a. -/
theorem diamond_user₁ (z : (E × E) × (E × E)) (hz : z.2.2 = 0) :
    z ∈ LinearMap.range (vMap (K := K)) ⊔ LinearMap.range (diamondUpload (K := K) (E := E)) := by
  apply Submodule.mem_sup.mpr
  refine ⟨vMap z.1, ⟨z.1, rfl⟩, diamondUpload (z.2.1, 0), ⟨_, rfl⟩, ?_⟩
  ext <;> simp [vMap, diamondUpload, hz]

/-- User 2 recovers every vector whose missing v-coordinate is along b. -/
theorem diamond_user₂ (z : (E × E) × (E × E)) (hz : z.1.1 = 0) :
    z ∈ LinearMap.range (rMap (K := K)) ⊔ LinearMap.range (diamondUpload (K := K) (E := E)) := by
  apply Submodule.mem_sup.mpr
  refine ⟨rMap z.2, ⟨z.2, rfl⟩, diamondUpload (0, z.1.2), ⟨_, rfl⟩, ?_⟩
  ext <;> simp [rMap, diamondUpload, hz]

/-- User 3 recovers both coordinates on both diamond rows, including its
pure diagonal demand a+b. -/
theorem diamond_user₃ : LinearMap.range (diffMap (K := K) (E := E × E)) ⊔
    LinearMap.range (diamondUpload (K := K) (E := E)) = ⊤ := by
  apply top_unique
  rintro ⟨⟨va,vb⟩,⟨ra,rb⟩⟩ _
  apply Submodule.mem_sup.mpr
  refine ⟨diffMap (-va,rb), ⟨_,rfl⟩, diamondUpload (ra+va,vb+rb), ⟨_,rfl⟩, ?_⟩
  simp [diffMap, vMap, rMap, diamondUpload]

/-- Exactly two scalar uploads per diamond copy, over the original field. -/
theorem diamond_upload_rank [FiniteDimensional K E] :
    finrank K (LinearMap.range (diamondUpload (K := K) (E := E))) = 2 * finrank K E := by
  rw [LinearMap.finrank_range_of_inj diamondUpload_injective, Module.finrank_prod]
  omega

/-- Exactly one scalar upload per one-dimensional row component. -/
theorem one_row_upload_rank [FiniteDimensional K E] :
    finrank K (LinearMap.range (vMap (K := K) (E := E))) = finrank K E := by
  apply LinearMap.finrank_range_of_inj
  intro x y h
  exact congrArg Prod.fst h
end RowAtoms

section LocalBasis
variable {F : Type*} [AddCommGroup F] [Module K F]

/-- A locally generated finite-dimensional relay admits a basis consisting
entirely of locally available coefficients. No loss from redundant uploads. -/
theorem locally_generated_basis (A : Fin 3 → Submodule K F) (P : Submodule K F)
    [FiniteDimensional K P] (hP : P = ⨆ i, P ⊓ A i) :
    ∃ (b : Basis (Fin (finrank K P)) K P) (owner : Fin (finrank K P) → Fin 3),
      ∀ j, (b j : F) ∈ A (owner j) := by
  classical
  let s : Set P := {p | ∃ i, (p : F) ∈ A i}
  have hs : (⊤ : Submodule K P) ≤ Submodule.span K s := by
    have hm : P ≤ (Submodule.span K s).map P.subtype := by
      conv_lhs => rw [hP]
      apply iSup_le
      intro i z hz
      exact ⟨⟨z,hz.1⟩, Submodule.subset_span ⟨i,hz.2⟩, rfl⟩
    intro p _
    obtain ⟨q,hq,he⟩ := hm p.property
    have he' : q = p := Subtype.ext he
    exact he' ▸ hq
  let b := Basis.ofSpan hs
  letI := FiniteDimensional.fintypeBasisIndex b
  let e := Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  let b' := b.reindex e
  have hb : ∀ j, ∃ i, (b' j : F) ∈ A i := by
    intro j
    exact Basis.ofSpan_subset hs ⟨e.symm j, by simp [b', b]⟩
  choose owner ho using hb
  exact ⟨b',owner,ho⟩

/-- Actual local linear encoders and a linear relay assembler. The sum of
uploaded scalar coordinates is exactly dim P. The relay reconstructs the
entire P-observation for every source, so any feasible signal decoder applies. -/
theorem exists_local_linear_uploads (A : Fin 3 → Submodule K F) (P : Submodule K F)
    [FiniteDimensional K P] (hP : P = ⨆ i, P ⊓ A i) :
    ∃ owner : Fin (finrank K P) → Fin 3,
      ∃ enc : ∀ i, (A i →ₗ[K] K) →ₗ[K] ({j // owner j = i} → K),
      ∃ relay : (∀ i, {j // owner j = i} → K) →ₗ[K] (P →ₗ[K] K),
        (∑ i, Fintype.card {j // owner j = i}) = finrank K P ∧
        ∀ x : F →ₗ[K] K,
          relay (fun i => enc i (x.comp (A i).subtype)) = x.comp P.subtype := by
  classical
  obtain ⟨b,owner,ho⟩ := locally_generated_basis A P hP
  let enc : ∀ i, (A i →ₗ[K] K) →ₗ[K] ({j // owner j = i} → K) := fun i =>
    { toFun := fun x j => x ⟨(b j.val : F), by simpa only [j.property] using ho j.val⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let join : (∀ i, {j // owner j = i} → K) →ₗ[K] (Fin (finrank K P) → K) :=
    { toFun := fun m j => m (owner j) ⟨j,rfl⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let relay := (b.constr K).toLinearMap.comp join
  refine ⟨owner,enc,relay,?_,?_⟩
  · rw [← Fintype.card_sigma]
    exact (Fintype.card_congr (Equiv.sigmaFiberEquiv owner)).trans (Fintype.card_fin _)
  · intro x
    apply b.ext
    intro j
    simp [relay,join,enc,Basis.constr_basis]


/-- Operational zero-error upload code from a locally generated feasible
relay. The scalar uploads and relay are linear, and their total fixed length
is exactly dim P. Decoders reconstruct each complete signal observation. -/
theorem exists_local_linear_upload_code (A U : Fin 3 → Submodule K F) (P : Submodule K F)
    [FiniteDimensional K P] (hP : P = ⨆ i, P ⊓ A i)
    (hU : ∀ i, U i ≤ A i ⊔ P) :
    ∃ owner : Fin (finrank K P) → Fin 3,
      ∃ enc : ∀ i, (A i →ₗ[K] K) →ₗ[K] ({j // owner j = i} → K),
      ∃ relay : (∀ i, {j // owner j = i} → K) →ₗ[K] (P →ₗ[K] K),
      ∃ decode : ∀ i, ((P →ₗ[K] K) × (A i →ₗ[K] K)) →ₗ[K] (U i →ₗ[K] K),
        (∑ i, Fintype.card {j // owner j = i}) = finrank K P ∧
        ∀ (x : F →ₗ[K] K) i,
          decode i (relay (fun j => enc j (x.comp (A j).subtype)),
            x.comp (A i).subtype) = x.comp (U i).subtype := by
  obtain ⟨owner,enc,relay,hlen,hrelay⟩ := exists_local_linear_uploads A P hP
  have hk (i : Fin 3) : LinearMap.ker ((dualObserve P).prod (dualObserve (A i))) ≤
      LinearMap.ker (dualObserve (U i)) := by
    intro x hx
    have hh : (dualObserve P x, dualObserve (A i) x) = (0,0) := hx
    have hp := congrArg Prod.fst hh
    have ha := congrArg Prod.snd hh
    apply LinearMap.mem_ker.mpr
    ext u
    obtain ⟨a,ha',p,hp',he⟩ := Submodule.mem_sup.mp (hU i u.property)
    have ea := LinearMap.congr_fun ha ⟨a,ha'⟩
    have ep := LinearMap.congr_fun hp ⟨p,hp'⟩
    change x (u:F) = 0
    rw [← he,map_add]
    exact (congrArg₂ (· + ·) ea ep).trans (zero_add 0)
  choose d hd using fun i => factors_through_of_ker_le
    ((dualObserve P).prod (dualObserve (A i))) (dualObserve (U i)) (hk i)
  refine ⟨owner,enc,relay,d,hlen,?_⟩
  intro x i
  rw [hrelay]
  exact LinearMap.congr_fun (hd i) x


/-- Pulling a completed relay back through a side-preserving coordinate
change preserves feasibility, local generation, and its exact dimension. -/
theorem pullback_relay [FiniteDimensional K F]
    (A U : Fin 3 → Submodule K F) (e : F ≃ₗ[K] F) (P : Submodule K F)
    (hA : ∀ i, (A i).map e.toLinearMap = A i)
    (hP : P = ⨆ i, P ⊓ A i)
    (hU : ∀ i, (U i).map e.toLinearMap ≤ A i ⊔ P) :
    ∃ Q : Submodule K F, (Q = ⨆ i, Q ⊓ A i) ∧
      (∀ i, U i ≤ A i ⊔ Q) ∧ finrank K Q = finrank K P := by
  have invmap (B : Submodule K F) : (B.map e.toLinearMap).map e.symm.toLinearMap = B := by
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      simpa using hz
    · intro hx
      exact ⟨e x,⟨x,hx,rfl⟩,by simp⟩
  have hsym (i : Fin 3) : (A i).map e.symm.toLinearMap = A i := by
    have hh := congrArg (Submodule.map e.symm.toLinearMap) (hA i)
    rw [invmap] at hh
    exact hh.symm
  refine ⟨P.map e.symm.toLinearMap,?_,?_,e.symm.finrank_map_eq P⟩
  · calc
      P.map e.symm.toLinearMap = (⨆ i, P ⊓ A i).map e.symm.toLinearMap := congrArg _ hP
      _ = ⨆ i, P.map e.symm.toLinearMap ⊓ (A i).map e.symm.toLinearMap := by
        rw [Submodule.map_iSup]
        congr 1
        funext i
        exact Submodule.map_inf _ e.symm.injective
      _ = ⨆ i, P.map e.symm.toLinearMap ⊓ A i := by simp_rw [hsym]
  · intro i
    have hh := Submodule.map_mono (f := e.symm.toLinearMap) (hU i)
    simpa only [invmap, Submodule.map_sup, hsym] using hh

end LocalBasis

end UploadBroadcast.ResidualUpload
