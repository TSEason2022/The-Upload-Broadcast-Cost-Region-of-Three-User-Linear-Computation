import UploadBroadcast.LinearCosts
import UploadBroadcast.ObservationRank
import UploadBroadcast.Model
import PFR.ForMathlib.Entropy.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite-field rank--entropy dictionary for the actual uniform source

The source distribution is `uniformOn Set.univ`, and `entropy`, `condEntropy`,
`mutualInfo`, and `condMutualInfo` are PFR's actual Shannon definitions.
Equal-size fibres are proved by translation, rather than assumed. The final
three `model_*_rank` theorems apply directly to `Model.observe` on `Model.Source`.
Division by `Real.log (Nat.card K)` converts natural-log entropy to q-ary units.
-/
namespace UploadBroadcast
open MeasureTheory ProbabilityTheory
open Module

variable {K V W : Type*} [Field K] [Finite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]
  [MeasurableSpace V] [DiscreteMeasurableSpace V]
  [MeasurableSpace W] [DiscreteMeasurableSpace W]

/-- Fibres over attained values have equal cardinality, by translation. -/
noncomputable def linearFiberEquiv (f : V →ₗ[K] W) (a b : V) :
    {x : V // f x = f a} ≃ {x : V // f x = f b} where
  toFun x := ⟨x - a + b, by simp [map_sub, map_add, x.property]⟩
  invFun x := ⟨x - b + a, by simp [map_sub, map_add, x.property]⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

omit [MeasurableSpace W] [DiscreteMeasurableSpace W] in
/-- Every linear observation of an actual uniform source is uniform on its range. -/
theorem linear_isUniform (f : V →ₗ[K] W) :
    IsUniform (Set.range f) f (uniformOn (Set.univ : Set V)) := by
  letI : Finite V := Module.finite_of_finite K
  constructor
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp only [uniformOn_apply (Set.toFinite _), Set.univ_inter]
    congr 1
    exact_mod_cast Nat.card_congr (linearFiberEquiv f a b)
  · have he : f ⁻¹' (Set.range f)ᶜ = ∅ := by ext x; simp
    rw [he, measure_empty]

/-- Shannon entropy of a finite-field linear observation, proved from its law. -/
theorem linear_entropy (f : V →ₗ[K] W) :
    entropy f (uniformOn (Set.univ : Set V)) =
      (finrank K (LinearMap.range f) : ℝ) * Real.log (Nat.card K) := by
  letI : Finite V := Module.finite_of_finite K
  rw [(linear_isUniform f).entropy_eq' (Set.finite_range f) (Measurable.of_discrete),
    linear_alphabet_card, Nat.cast_pow, Real.log_pow]

variable {Z : Type*} [AddCommGroup Z] [Module K Z]
  [MeasurableSpace Z] [DiscreteMeasurableSpace Z] [Countable W] [Countable Z]

/-- Conditional entropy is the extra rank contributed by the new observation. -/
theorem linear_condEntropy (f : V →ₗ[K] W) (g : V →ₗ[K] Z) :
    condEntropy f g (uniformOn (Set.univ : Set V)) =
      ((finrank K (LinearMap.range (f.prod g)) : ℝ) -
        finrank K (LinearMap.range g)) * Real.log (Nat.card K) := by
  letI : Finite V := Module.finite_of_finite K
  letI : FiniteRange (f : V → W) := ⟨Set.finite_range f⟩
  letI : FiniteRange (g : V → Z) := ⟨Set.finite_range g⟩
  rw [chain_rule'' _ (Measurable.of_discrete) (Measurable.of_discrete)]
  change entropy (f.prod g) _ - entropy g _ = _
  rw [linear_entropy, linear_entropy, sub_mul]

/-- Mutual information is the linear rank overlap of the two observations. -/
theorem linear_mutualInfo (f : V →ₗ[K] W) (g : V →ₗ[K] Z) :
    mutualInfo f g (uniformOn (Set.univ : Set V)) =
      ((finrank K (LinearMap.range f) : ℝ) + finrank K (LinearMap.range g) -
        finrank K (LinearMap.range (f.prod g))) * Real.log (Nat.card K) := by
  rw [mutualInfo_def]
  change entropy f _ + entropy g _ - entropy (f.prod g) _ = _
  rw [linear_entropy, linear_entropy, linear_entropy, sub_mul, add_mul]

omit [Countable W] in
/-- Conversion to the paper's base-|K| entropy units. -/
theorem linear_entropy_q (f : V →ₗ[K] W) :
    entropy f (uniformOn (Set.univ : Set V)) / Real.log (Nat.card K) =
      finrank K (LinearMap.range f) := by
  have hq : (1 : ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
  rw [linear_entropy, mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos hq))]

/-- The conditional version in the paper's base-|K| entropy units. -/
theorem linear_condEntropy_q (f : V →ₗ[K] W) (g : V →ₗ[K] Z) :
    condEntropy f g (uniformOn (Set.univ : Set V)) / Real.log (Nat.card K) =
      (finrank K (LinearMap.range (f.prod g)) : ℝ) - finrank K (LinearMap.range g) := by
  have hq : (1 : ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
  rw [linear_condEntropy, mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos hq))]

variable {T : Type*} [AddCommGroup T] [Module K T]
  [MeasurableSpace T] [DiscreteMeasurableSpace T] [Countable T]

/-- Conditional mutual information is the overlap of ranks modulo conditioning. -/
theorem linear_condMutualInfo (f : V →ₗ[K] W) (g : V →ₗ[K] Z) (h : V →ₗ[K] T) :
    condMutualInfo f g h (uniformOn (Set.univ : Set V)) =
      ((finrank K (LinearMap.range (f.prod h)) : ℝ) +
        finrank K (LinearMap.range (g.prod h)) -
        finrank K (LinearMap.range ((f.prod g).prod h)) -
        finrank K (LinearMap.range h)) * Real.log (Nat.card K) := by
  letI : Finite V := Module.finite_of_finite K
  letI : FiniteRange (f : V → W) := ⟨Set.finite_range f⟩
  letI : FiniteRange (g : V → Z) := ⟨Set.finite_range g⟩
  letI : FiniteRange (h : V → T) := ⟨Set.finite_range h⟩
  rw [condMutualInfo_eq Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete]
  change condEntropy f h _ + condEntropy g h _ - condEntropy (f.prod g) h _ = _
  rw [linear_condEntropy, linear_condEntropy, linear_condEntropy]
  ring

/-- Apply the same single-letter observation independently to each block column. -/
def blockLinear (f : V →ₗ[K] W) (L : ℕ) : (Fin L → V) →ₗ[K] (Fin L → W) where
  toFun x i := f (x i)
  map_add' _ _ := by ext i; simp
  map_smul' _ _ := by ext i; simp

/-- The attainable block alphabet is the product of attainable single-letter alphabets. -/
noncomputable def blockRangeEquiv (f : V →ₗ[K] W) (L : ℕ) :
    LinearMap.range (blockLinear f L) ≃ₗ[K] (Fin L → LinearMap.range f) := by
  let e : LinearMap.range (blockLinear f L) →ₗ[K] (Fin L → LinearMap.range f) :=
    { toFun := fun y i => ⟨y.val i, by
        obtain ⟨x, hx⟩ := y.property
        exact ⟨x i, congrFun hx i⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply LinearEquiv.ofBijective e
  constructor
  · intro a b hab
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hab i)
  · intro y
    choose x hx using fun i => (y i).property
    refine ⟨⟨fun i => (y i).val, ⟨x, ?_⟩⟩, ?_⟩
    · funext i; exact hx i
    · rfl

omit [Finite K] [MeasurableSpace V] [DiscreteMeasurableSpace V]
  [MeasurableSpace W] [DiscreteMeasurableSpace W] [Countable W] in
/-- Blocklength multiplies the actual linear rank by L. -/
theorem blockLinear_rank (f : V →ₗ[K] W) (L : ℕ) :
    finrank K (LinearMap.range (blockLinear f L)) = L * finrank K (LinearMap.range f) := by
  rw [(blockRangeEquiv f L).finrank_eq, Module.finrank_pi_fintype]
  simp

/-- Shannon entropy of the actual L-column uniform source. -/
theorem blockLinear_entropy (f : V →ₗ[K] W) (L : ℕ) :
    entropy (blockLinear f L) (uniformOn (Set.univ : Set (Fin L → V))) =
      (L : ℝ) * finrank K (LinearMap.range f) * Real.log (Nat.card K) := by
  letI : Finite V := Module.finite_of_finite K
  rw [linear_entropy, blockLinear_rank, Nat.cast_mul]

omit [Finite K] [MeasurableSpace V] [DiscreteMeasurableSpace V]
  [MeasurableSpace W] [DiscreteMeasurableSpace W]
  [MeasurableSpace Z] [DiscreteMeasurableSpace Z] [Countable W] [Countable Z] in
theorem blockLinear_joint_rank (f : V →ₗ[K] W) (g : V →ₗ[K] Z) (L : ℕ) :
    finrank K (LinearMap.range ((blockLinear f L).prod (blockLinear g L))) =
      L * finrank K (LinearMap.range (f.prod g)) := by
  have hk : LinearMap.ker ((blockLinear f L).prod (blockLinear g L)) =
      LinearMap.ker (blockLinear (f.prod g) L) := by
    ext x
    change ((fun i => f (x i)), (fun i => g (x i))) = (0, 0) ↔
      (fun i => (f (x i), g (x i))) = 0
    simp only [Prod.mk.injEq, funext_iff, Pi.zero_apply, Prod.mk_eq_zero]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  have h₁ := ((blockLinear f L).prod (blockLinear g L)).finrank_range_add_finrank_ker
  have h₂ := (blockLinear (f.prod g) L).finrank_range_add_finrank_ker
  rw [hk] at h₁
  rw [blockLinear_rank] at h₂
  omega

/-- Rearrange the actual matrix source into its list of source covectors. -/
def sourceColumnsEquiv {F : Type*} [AddCommGroup F] [Module K F] (L : ℕ) :
    Source K F L ≃ₗ[K] (Fin L → (F →ₗ[K] K)) where
  toFun x i := (LinearMap.proj i).comp x
  invFun x := LinearMap.pi x
  left_inv x := by ext b i; rfl
  right_inv x := by ext i b; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Finite K] in
/-- The coordinate change commutes exactly with the paper's observation map. -/
theorem sourceColumns_observe {F : Type*} [AddCommGroup F] [Module K F]
    (B : Submodule K F) (L : ℕ) (x : Source K F L) :
    sourceColumnsEquiv L (observe K F B x) =
      blockLinear (dualObserve B) L (sourceColumnsEquiv L x) := by
  ext i b
  rfl

namespace LinearObservation
variable {F : Type*} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
local instance dualMeasurable (E : Type*) [AddCommGroup E] [Module K E] :
    MeasurableSpace (E →ₗ[K] K) := ⊤
local instance dualDiscrete (E : Type*) [AddCommGroup E] [Module K E] :
    DiscreteMeasurableSpace (E →ₗ[K] K) := ⟨fun _ => trivial⟩
local instance dualFinite (E : Type*) [AddCommGroup E] [Module K E] [FiniteDimensional K E] :
    Finite (E →ₗ[K] K) := Module.finite_of_finite K

local instance sourceMeasurable (E : Type*) [AddCommGroup E] [Module K E] (L : ℕ) :
    MeasurableSpace (Source K E L) := ⊤
local instance sourceDiscrete (E : Type*) [AddCommGroup E] [Module K E] (L : ℕ) :
    DiscreteMeasurableSpace (Source K E L) := ⟨fun _ => trivial⟩

/-- Uniformity of the actual model source is preserved by the column rearrangement. -/
theorem sourceColumns_uniform (L : ℕ) :
    IsUniform Set.univ (sourceColumnsEquiv (K := K) (F := F) L)
      (uniformOn (Set.univ : Set (Source K F L))) := by
  have hh := linear_isUniform (sourceColumnsEquiv (K := K) (F := F) L).toLinearMap
  simpa only [LinearEquiv.coe_coe, EquivLike.range_eq_univ] using hh

/-- The source coordinate equivalence pushes the uniform measure to the uniform measure. -/
theorem sourceColumns_map (L : ℕ) :
    (uniformOn (Set.univ : Set (Source K F L))).map
      (sourceColumnsEquiv (K := K) (F := F) L) =
      uniformOn (Set.univ : Set (Fin L → (F →ₗ[K] K))) := by
  letI : Finite (Source K F L) := Module.finite_of_finite K
  exact (sourceColumns_uniform L).map_eq_uniformOn Measurable.of_discrete
    (Set.toFinite _) (Set.univ_nonempty)

/-- Actual model observations, after the coordinate rearrangement, have exactly
    the law used by the rank--entropy dictionary. -/
theorem observe_identDistrib (B : Submodule K F) (L : ℕ) :
    IdentDistrib (fun x : Source K F L => sourceColumnsEquiv L (observe K F B x))
      (blockLinear (dualObserve B) L)
      (uniformOn (Set.univ : Set (Source K F L)))
      (uniformOn (Set.univ : Set (Fin L → (F →ₗ[K] K)))) := by
  letI : Finite (Source K F L) := Module.finite_of_finite K
  have hi : IdentDistrib (sourceColumnsEquiv (K := K) (F := F) L) id
      (uniformOn (Set.univ : Set (Source K F L)))
      (uniformOn (Set.univ : Set (Fin L → (F →ₗ[K] K)))) :=
    ⟨Measurable.of_discrete.aemeasurable, measurable_id.aemeasurable,
      by rw [Measure.map_id]; exact sourceColumns_map L⟩
  have hh := hi.comp (Measurable.of_discrete (f := blockLinear (dualObserve B) L))
  simpa only [Function.comp_def, sourceColumns_observe, id_eq] using hh

/-- The paper's H(Xᵀ B) = L dim B, for a uniform L-column source. -/
theorem entropy_rank (B : Submodule K F) (L : ℕ) :
    entropy (blockLinear (dualObserve B) L)
      (uniformOn (Set.univ : Set (Fin L → (F →ₗ[K] K)))) / Real.log (Nat.card K) =
      (L : ℝ) * finrank K B := by
  rw [linear_entropy_q, blockLinear_rank, dualObserve_rank, Nat.cast_mul]

/-- The paper's conditional rank--entropy dictionary, with no rank hypothesis. -/
theorem condEntropy_rank (B C : Submodule K F) (L : ℕ) :
    condEntropy (blockLinear (dualObserve C) L) (blockLinear (dualObserve B) L)
      (uniformOn (Set.univ : Set (Fin L → (F →ₗ[K] K)))) / Real.log (Nat.card K) =
      (L : ℝ) * condRank C B := by
  rw [linear_condEntropy_q, blockLinear_joint_rank, blockLinear_rank,
    dualObserve_joint_rank, dualObserve_rank, sup_comm C B]
  have hle : finrank K B ≤ finrank K ↥(B ⊔ C) := Submodule.finrank_mono le_sup_left
  rw [condRank, Nat.cast_sub hle, Nat.cast_mul, Nat.cast_mul, mul_sub]

/-- The paper's I(Xᵀ B;Xᵀ C) = L dim(B∩C). -/
theorem mutualInfo_rank (B C : Submodule K F) (L : ℕ) :
    mutualInfo (blockLinear (dualObserve B) L) (blockLinear (dualObserve C) L)
      (uniformOn (Set.univ : Set (Fin L → (F →ₗ[K] K)))) / Real.log (Nat.card K) =
      (L : ℝ) * finrank K ↥(B ⊓ C) := by
  have hq : (1 : ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
  rw [linear_mutualInfo, mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos hq)),
    blockLinear_joint_rank, blockLinear_rank, blockLinear_rank,
    dualObserve_joint_rank, dualObserve_rank, dualObserve_rank]
  have hr := B.finrank_sup_add_finrank_inf_eq C
  have hr' : (finrank K ↥(B ⊔ C) : ℝ) + finrank K ↥(B ⊓ C) =
      finrank K B + finrank K C := by exact_mod_cast hr
  push_cast
  nlinarith

/-- The entropy dictionary directly for the original model's observation function. -/
theorem model_entropy_rank (B : Submodule K F) (L : ℕ) :
    entropy (observe K F B : Source K F L → Source K B L)
      (uniformOn (Set.univ : Set (Source K F L))) / Real.log (Nat.card K) =
      (L : ℝ) * finrank K B := by
  letI : Finite (Source K B L) := Module.finite_of_finite K
  have hh := (observe_identDistrib B L).entropy_congr
  have he := entropy_comp_of_injective
    (uniformOn (Set.univ : Set (Source K F L)))
    (Measurable.of_discrete (f := (observe K F B : Source K F L → Source K B L)))
    (sourceColumnsEquiv (K := K) (F := B) L) (sourceColumnsEquiv L).injective
  rw [← entropy_rank B L, ← hh]
  congr 1
  exact he.symm

/-- The conditional dictionary directly for the original matrix source model. -/
theorem model_condEntropy_rank (B C : Submodule K F) (L : ℕ) :
    condEntropy (observe K F C : Source K F L → Source K C L) (observe K F B)
      (uniformOn (Set.univ : Set (Source K F L))) / Real.log (Nat.card K) =
      (L : ℝ) * condRank C B := by
  letI : Finite (Source K F L) := Module.finite_of_finite K
  letI : Finite (Source K B L) := Module.finite_of_finite K
  letI : Finite (Source K C L) := Module.finite_of_finite K
  letI : Fintype (Source K B L) := Fintype.ofFinite _
  letI : Fintype (Source K C L) := Fintype.ofFinite _
  letI : Fintype (Fin L → (B →ₗ[K] K)) := Fintype.ofFinite _
  letI : Fintype (Fin L → (C →ₗ[K] K)) := Fintype.ofFinite _
  have hi : IdentDistrib (sourceColumnsEquiv (K := K) (F := F) L) id
      (uniformOn (Set.univ : Set (Source K F L)))
      (uniformOn (Set.univ : Set (Fin L → (F →ₗ[K] K)))) :=
    ⟨Measurable.of_discrete.aemeasurable, measurable_id.aemeasurable,
      by rw [Measure.map_id]; exact sourceColumns_map L⟩
  have hp := hi.comp (Measurable.of_discrete (f :=
    fun x => (blockLinear (dualObserve C) L x, blockLinear (dualObserve B) L x)))
  have he := hp.condEntropy_eq Measurable.of_discrete Measurable.of_discrete
    Measurable.of_discrete Measurable.of_discrete
  change condEntropy (fun x => blockLinear (dualObserve C) L (sourceColumnsEquiv L x))
      (fun x => blockLinear (dualObserve B) L (sourceColumnsEquiv L x)) _ =
    condEntropy (blockLinear (dualObserve C) L) (blockLinear (dualObserve B) L) _ at he
  simp_rw [← sourceColumns_observe] at he
  change condEntropy ((sourceColumnsEquiv L) ∘ (observe K F C))
      ((sourceColumnsEquiv L) ∘ (observe K F B)) _ = _ at he
  rw [condEntropy_comp_of_injective _ Measurable.of_discrete _
    (sourceColumnsEquiv L).injective,
    condEntropy_of_injective' _ Measurable.of_discrete Measurable.of_discrete _
      (sourceColumnsEquiv L).injective Measurable.of_discrete] at he
  rw [he]
  exact condEntropy_rank B C L

/-- The mutual-information dictionary directly for the original matrix source. -/
theorem model_mutualInfo_rank (B C : Submodule K F) (L : ℕ) :
    mutualInfo (observe K F B : Source K F L → Source K B L) (observe K F C)
      (uniformOn (Set.univ : Set (Source K F L))) / Real.log (Nat.card K) =
      (L : ℝ) * finrank K ↥(B ⊓ C) := by
  letI : Finite (Source K F L) := Module.finite_of_finite K
  letI : Finite (Source K B L) := Module.finite_of_finite K
  letI : Finite (Source K C L) := Module.finite_of_finite K
  letI : Fintype (Source K B L) := Fintype.ofFinite _
  letI : Fintype (Source K C L) := Fintype.ofFinite _
  rw [mutualInfo_eq_entropy_sub_condEntropy Measurable.of_discrete Measurable.of_discrete,
    sub_div, model_entropy_rank, model_condEntropy_rank]
  have hle : finrank K C ≤ finrank K ↥(C ⊔ B) := Submodule.finrank_mono le_sup_left
  rw [condRank, Nat.cast_sub hle, sup_comm C B]
  have hr := B.finrank_sup_add_finrank_inf_eq C
  have hr' : (finrank K ↥(B ⊔ C) : ℝ) + finrank K ↥(B ⊓ C) =
      finrank K B + finrank K C := by exact_mod_cast hr
  nlinarith

end LinearObservation
end UploadBroadcast
