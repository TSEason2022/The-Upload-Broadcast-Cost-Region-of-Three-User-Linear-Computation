import UploadBroadcast.CitedEntropyData
namespace UploadBroadcast.CitedEntropyCounterexample
open FiniteSubspaceCertificate MeasureTheory ProbabilityTheory
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem all_subset_kernel_cards : ∀ s : Fin 6 → Bool,
    (Finset.univ.filter (fun x : V => joint 1 s x = 0)).card =
      (Finset.univ.filter (fun x : V => joint 2 s x = 0)).card := by
  decide +kernel

end UploadBroadcast.CitedEntropyCounterexample
