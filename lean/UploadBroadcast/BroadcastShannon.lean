import UploadBroadcast.LinearEntropy
import UploadBroadcast.Shannon
import UploadBroadcast.EntropyCoding
import UploadBroadcast.LCBCConverse

/-!
# Shannon realization of the nonlinear broadcast converse

For every positive blocklength and arbitrary finite-alphabet function of the
uniform finite-field source, `entropyInstance` proves the lattice entropy laws
from PFR's actual Shannon entropy. The observations are exactly `Model.observe`.
Normalization is by `L * log |K|`. No linearity of the broadcast, upload
feasibility, or assumed information inequality is required.

The reusable fiber lemmas establish deterministic data processing, functional
submodularity, and diminishing increments directly from the Shannon laws.
`decoder_eq` converts a concrete zero-error decoder into the equality needed
by the fifteen-profile converse.
-/
namespace UploadBroadcast.BroadcastShannon
open MeasureTheory ProbabilityTheory Module

section Fibers
variable {Ω X Y Z : Type*} [Finite Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
 [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X] [Nonempty X]
 [MeasurableSpace Y] [Countable Y] [MeasurableSingletonClass Y] [Nonempty Y]
 [MeasurableSpace Z] [Countable Z] [MeasurableSingletonClass Z] [Nonempty Z]
 (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [Nonempty Y] in
lemma entropy_le_of_fibers (f : Ω → X) (g : Ω → Y)
    (h : Function.FactorsThrough f g) : entropy f μ ≤ entropy g μ := by
  obtain ⟨e, he⟩ := (Function.factorsThrough_iff f).mp h
  rw [he]
  exact entropy_comp_le μ Measurable.of_discrete e

lemma entropy_eq_of_fibers (f : Ω → X) (g : Ω → Y)
    (h : ∀ a b, f a = f b ↔ g a = g b) : entropy f μ = entropy g μ := by
  apply le_antisymm
  · exact entropy_le_of_fibers μ f g (fun a b hab => (h a b).mpr hab)
  · exact entropy_le_of_fibers μ g f (fun a b hab => (h a b).mp hab)

lemma functional_submod (f : Ω → X) (g : Ω → Y) (k : Ω → Z)
    (hf : Function.FactorsThrough k f) (hg : Function.FactorsThrough k g) :
    entropy (fun a => (f a, g a)) μ + entropy k μ ≤ entropy f μ + entropy g μ := by
  have hs := entropy_triple_add_entropy_le μ (X := f) (Y := g) (Z := k)
    Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
  have h₁ := entropy_eq_of_fibers μ (fun a => (f a, k a)) f (by
    intro a b; simp only [Prod.mk.injEq]; exact ⟨And.left, fun h => ⟨h, hf h⟩⟩)
  have h₂ := entropy_eq_of_fibers μ (fun a => (g a, k a)) g (by
    intro a b; simp only [Prod.mk.injEq]; exact ⟨And.left, fun h => ⟨h, hg h⟩⟩)
  have h₃ := entropy_le_of_fibers μ (fun a => (f a, g a)) (fun a => (f a, (g a,k a)))
    (fun a b h => by simpa only [Prod.mk.injEq] using And.intro (congrArg Prod.fst h) (congrArg (fun p => p.2.1) h))
  rw [h₁, h₂] at hs
  linarith

lemma increment (f : Ω → X) (g : Ω → Y) (k : Ω → Z)
    (h : Function.FactorsThrough f g) :
    entropy (fun a => (k a,g a)) μ - entropy (fun a => (k a,f a)) μ ≤
      entropy g μ - entropy f μ := by
  have hs := functional_submod μ (fun a => (k a,f a)) g f
    (fun a b hab => congrArg Prod.snd hab) h
  have he := entropy_eq_of_fibers μ (fun a => ((k a,f a),g a)) (fun a => (k a,g a)) (by
    intro a b; simp only [Prod.mk.injEq]
    exact ⟨fun hh => ⟨hh.1.1,hh.2⟩, fun hh => ⟨⟨hh.1,h hh.2⟩,hh.2⟩⟩)
  rw [he] at hs
  linarith
end Fibers

variable {K F S : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
 [FiniteDimensional K F] [Finite S] [MeasurableSpace S] [MeasurableSingletonClass S]
local instance sourceMeasurable (E : Type*) [AddCommGroup E] [Module K E] (L : ℕ) :
    MeasurableSpace (Source K E L) := ⊤
local instance sourceDiscrete (E : Type*) [AddCommGroup E] [Module K E] (L : ℕ) :
    DiscreteMeasurableSpace (Source K E L) := ⟨fun _ => trivial⟩
local instance sourceFinite (E : Type*) [AddCommGroup E] [Module K E] [FiniteDimensional K E] (L : ℕ) :
    Finite (Source K E L) := Module.finite_of_finite K

variable {L : ℕ}
omit [Finite K] [FiniteDimensional K F] in
lemma obs_fibers {V W : Submodule K F} (h : V ≤ W) :
    Function.FactorsThrough (observe K F V : Source K F L → _) (observe K F W) := by
  intro x y he
  apply LinearMap.ext; intro v
  exact LinearMap.congr_fun he ⟨v.val,h v.property⟩

omit [Finite K] [FiniteDimensional K F] in
lemma obs_sup_fibers (V W : Submodule K F) (x y : Source K F L) :
    observe K F (V ⊔ W) x = observe K F (V ⊔ W) y ↔
      observe K F V x = observe K F V y ∧ observe K F W x = observe K F W y := by
  constructor
  · intro h
    exact ⟨obs_fibers le_sup_left h, obs_fibers le_sup_right h⟩
  · rintro ⟨hv,hw⟩
    apply LinearMap.ext; intro v
    obtain ⟨v,hv'⟩ := v
    change x v = y v
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hv'
    have h₁ := LinearMap.congr_fun hv ⟨a,ha⟩
    have h₂ := LinearMap.congr_fun hw ⟨b,hb⟩
    change x a = y a at h₁
    change x b = y b at h₂
    simp [map_add,h₁,h₂]

noncomputable abbrev μ (L : ℕ) : Measure (Source K F L) := uniformOn Set.univ
noncomputable def joint (s : Source K F L → S) (V : Submodule K F) : ℝ :=
  entropy (fun x => (s x,observe K F V x)) (μ L) / ((L : ℝ) * Real.log (Nat.card K))


lemma denom_pos (hL : 0 < L) : 0 < (L : ℝ) * Real.log (Nat.card K) := by
  have hq : (1 : ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
  exact mul_pos (by exact_mod_cast hL) (Real.log_pos hq)

lemma obs_entropy (V : Submodule K F) (hL : 0 < L) :
    entropy (observe K F V : Source K F L → _) (μ L) /
      ((L : ℝ) * Real.log (Nat.card K)) = finrank K V := by
  have hh := LinearObservation.model_entropy_rank (K := K) V L
  change entropy (observe K F V : Source K F L → _) (μ L) / Real.log (Nat.card K) = _ at hh
  rw [mul_comm, ← div_div, hh]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (Nat.ne_of_gt hL))

noncomputable def entropyInstance (s : Source K F L → S) (hL : 0 < L) :
    LCBCConverse.BroadcastEntropy (K := K) (F := F) := by
  letI : Nonempty S := ⟨s 0⟩
  have hd := denom_pos (K := K) hL
  refine { joint := joint s
           cost := entropy s (μ L) / ((L : ℝ) * Real.log (Nat.card K))
           mono := ?_, submod := ?_, rank_le := ?_, upper := ?_, increment := ?_ }
  · intro V W h
    apply div_le_div_of_nonneg_right _ hd.le
    exact entropy_le_of_fibers (μ L) _ _ (fun x y he =>
      Prod.ext ((Prod.mk.inj he).1) (obs_fibers h ((Prod.mk.inj he).2)))
  · intro V W
    have hs := functional_submod (μ L)
      (fun x => (s x,observe K F V x)) (fun x => (s x,observe K F W x))
      (fun x => (s x,observe K F (V ⊓ W) x))
      (fun x y he => Prod.ext ((Prod.mk.inj he).1) (obs_fibers inf_le_left ((Prod.mk.inj he).2)))
      (fun x y he => Prod.ext ((Prod.mk.inj he).1) (obs_fibers inf_le_right ((Prod.mk.inj he).2)))
    have he := entropy_eq_of_fibers (μ L)
      (fun x => ((s x,observe K F V x),(s x,observe K F W x)))
      (fun x => (s x,observe K F (V ⊔ W) x)) (by
        intro x y
        simp only [Prod.mk.injEq, obs_sup_fibers]
        tauto)
    rw [he] at hs
    simpa only [joint, ← add_div] using div_le_div_of_nonneg_right hs hd.le
  · intro V
    rw [← obs_entropy V hL]
    apply div_le_div_of_nonneg_right _ hd.le
    exact entropy_le_of_fibers (μ L) _ _ (fun x y he => (Prod.mk.inj he).2)
  · intro V
    have hs := entropy_pair_le_add (μ := μ L) (X := s) (Y := observe K F V)
      Measurable.of_discrete Measurable.of_discrete
    rw [← obs_entropy V hL]
    simpa only [joint, ← add_div] using div_le_div_of_nonneg_right hs hd.le
  · intro V W h
    have hs := increment (μ L) (observe K F V) (observe K F W) s (obs_fibers h)
    rw [← obs_entropy V hL, ← obs_entropy W hL]
    simpa only [joint, ← sub_div] using div_le_div_of_nonneg_right hs hd.le

/-- Actual deterministic decoding gives the equality used by the lattice converse. -/
lemma decoder_eq (s : Source K F L → S) (hL : 0 < L)
    (A U : Submodule K F) (ha : A ≤ U)
    (decode : S → Source K A L → Source K U L)
    (he : ∀ x, decode (s x) (observe K F A x) = observe K F U x) :
    (entropyInstance s hL).joint A = (entropyInstance s hL).joint U := by
  letI : Nonempty S := ⟨s 0⟩
  change joint s A = joint s U
  unfold joint
  congr 1
  apply entropy_eq_of_fibers
  intro x y
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hs,ho⟩
    exact ⟨hs, by rw [← he x, ← he y, hs, ho]⟩
  · rintro ⟨hs,ho⟩
    exact ⟨hs, obs_fibers ha ho⟩

end UploadBroadcast.BroadcastShannon
