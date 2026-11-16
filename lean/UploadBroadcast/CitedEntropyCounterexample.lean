import UploadBroadcast.CitedEntropyShannon
import UploadBroadcast.CitedEntropyProfile
import UploadBroadcast.CitedEntropyModel

/-!
# Corrected witness for the cited entropy-vector insufficiency assertion

The cited F3 pair does not have equal subset entropies. The same six literal
observations over F5 do. This theorem is an independently certified corrected
witness for the frozen manuscript's existential assertion, not a claim that
the cited F3 calculation is correct.
-/
namespace UploadBroadcast.CitedEntropyCounterexample
open MeasureTheory ProbabilityTheory
local instance endpointMeasurableV : MeasurableSpace V := ⊤
local instance endpointDiscreteV : DiscreteMeasurableSpace V := ⟨fun _ => trivial⟩
local instance endpointMeasurableOutput : MeasurableSpace (Fin 6 → K) := ⊤
local instance endpointDiscreteOutput : DiscreteMeasurableSpace (Fin 6 → K) := ⟨fun _ => trivial⟩

/-- One statement containing the actual Shannon and operational parts. -/
theorem corrected_entropy_counterexample :
    (∀ (L : ℕ) (s : Fin 6 → Bool),
      entropy (blockLinear (joint 1 s) L) (uniformOn (Set.univ : Set (Fin L → V))) =
        entropy (blockLinear (joint 2 s) L) (uniformOn (Set.univ : Set (Fin L → V)))) ∧
      broadcastOptimum (task 1).A (task 1).U = 1 ∧
      broadcastOptimum (task 2).A (task 2).U = 3/2 :=
  ⟨fun L s => all_block_subset_entropies s L,broadcastOptima⟩

/-- Hence even all original-variable subset entropies cannot determine D*. -/
theorem equal_subset_entropies_distinct_operational_optima :
    (∀ s : Fin 6 → Bool,
      entropy (joint 1 s) (uniformOn (Set.univ : Set V)) =
        entropy (joint 2 s) (uniformOn (Set.univ : Set V))) ∧
      broadcastOptimum (task 1).A (task 1).U ≠
        broadcastOptimum (task 2).A (task 2).U := by
  refine ⟨all_subset_entropies, ?_⟩
  rw [broadcastOptima.1,broadcastOptima.2]
  norm_num

end UploadBroadcast.CitedEntropyCounterexample
