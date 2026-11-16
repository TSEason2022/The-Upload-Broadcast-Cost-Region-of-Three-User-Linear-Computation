import UploadBroadcast.GlobalMenuAssembly
import UploadBroadcast.CycleTheorem
import UploadBroadcast.CycleReverseTheorem

namespace UploadBroadcast.CycleFiniteAssembly
open Module GlobalMenuAssembly
variable {K : Type*} [Field K]

def positiveIncrement (r : Fin 6) : ℤ := if r=1 then 1 else 0
def negativeIncrement (r : Fin 6) : ℤ := if r=3 then 1 else 0

theorem positive_realizes (n : ℕ) :
    RealizesMenu (CycleRepair.canonicalTask K n) (3*(n+1)+4)
      (fun (_ : Unit) => firstIncrement positiveIncrement) := by
  intro k
  obtain ⟨hg,hf,hd,hfirst,hsecond⟩ := CycleRepair.canonical_positive_repair K n
  refine ⟨LinearMap.range (CycleRepair.relayMap K (n+1)),hg,hf,hd,?_⟩
  intro r
  rw [Task.inducedRelay_entry]
  change Profile.entry (CycleRepair.canonicalRepairedTask K n) r ≤ _
  cases r with
  | inl r =>
    have hh := hfirst r
    have he : (positiveIncrement r : ℝ) = if r=1 then 1 else 0 := by
      simp only [positiveIncrement]; split <;> simp
    change _ ≤ _+(positiveIncrement r : ℝ)
    rw [he]
    linarith only [hh]
  | inr r =>
    simpa only [firstIncrement,add_zero] using (hsecond r.1 r.2).le

theorem negative_realizes (n : ℕ) :
    RealizesMenu (CycleRepair.canonicalReverseTask K n) (3*(n+1)+4)
      (fun (_ : Unit) => firstIncrement negativeIncrement) := by
  intro k
  obtain ⟨hg,hf,hd,hfirst,hsecond⟩ := CycleRepair.canonical_reverse_repair K n
  refine ⟨LinearMap.range (CycleRepair.reverseRelayMap K (n+1)),hg,hf,hd,?_⟩
  intro r
  rw [Task.inducedRelay_entry]
  change Profile.entry (CycleRepair.canonicalReverseRepairedTask K n) r ≤ _
  cases r with
  | inl r =>
    have hh := hfirst r
    have he : (negativeIncrement r : ℝ) = if r=3 then 1 else 0 := by
      simp only [negativeIncrement]; split <;> simp
    change _ ≤ _+(negativeIncrement r : ℝ)
    rw [he]
    linarith only [hh]
  | inr r =>
    simpa only [firstIncrement,add_zero] using (hsecond r.1 r.2).le

end UploadBroadcast.CycleFiniteAssembly
