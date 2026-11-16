import UploadBroadcast.CitedEntropyKernelCertificate
namespace UploadBroadcast.CitedEntropyCounterexample
open FiniteSubspaceCertificate MeasureTheory ProbabilityTheory

theorem kernel_card (t : K) (s : Fin 6 → Bool) :
    Nat.card (LinearMap.ker (joint t s)) =
      (Finset.univ.filter (fun x : V => joint t s x = 0)).card := by
  change Nat.card {x : V // joint t s x = 0} = _
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem all_subset_ranks (s : Fin 6 → Bool) :
    Module.finrank K (LinearMap.range (joint 1 s)) =
      Module.finrank K (LinearMap.range (joint 2 s)) := by
  have hc : Nat.card (LinearMap.ker (joint 1 s)) =
      Nat.card (LinearMap.ker (joint 2 s)) := by
    rw [kernel_card,kernel_card,all_subset_kernel_cards]
  rw [Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker (joint 1 s)),
    Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker (joint 2 s))] at hc
  have hk := (Nat.pow_right_injective (by norm_num [K,Nat.card_eq_fintype_card] :
    2 ≤ Nat.card K)) hc
  have h1 := (joint 1 s).finrank_range_add_finrank_ker
  have h2 := (joint 2 s).finrank_range_add_finrank_ker
  omega

local instance shannonMeasurableV : MeasurableSpace V := ⊤
local instance shannonDiscreteV : DiscreteMeasurableSpace V := ⟨fun _ => trivial⟩
local instance shannonMeasurableOutput : MeasurableSpace (Fin 6 → K) := ⊤
local instance shannonDiscreteOutput : DiscreteMeasurableSpace (Fin 6 → K) := ⟨fun _ => trivial⟩

/-- Equality of the actual Shannon entropies of every subset of the six
original variables, evaluated on the uniform 125-point source. -/
theorem all_subset_entropies (s : Fin 6 → Bool) :
    entropy (joint 1 s) (uniformOn (Set.univ : Set V)) =
      entropy (joint 2 s) (uniformOn (Set.univ : Set V)) := by
  rw [linear_entropy,linear_entropy,all_subset_ranks]

/-- The same equality holds for every independent uniform blocklength. -/
theorem all_block_subset_entropies (s : Fin 6 → Bool) (L : ℕ) :
    entropy (blockLinear (joint 1 s) L) (uniformOn (Set.univ : Set (Fin L → V))) =
      entropy (blockLinear (joint 2 s) L) (uniformOn (Set.univ : Set (Fin L → V))) := by
  rw [blockLinear_entropy,blockLinear_entropy,all_subset_ranks]

end UploadBroadcast.CitedEntropyCounterexample
