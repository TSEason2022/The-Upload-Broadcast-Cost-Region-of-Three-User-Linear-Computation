import UploadBroadcast.LinearEntropy
import UploadBroadcast.Shannon
import UploadBroadcast.EntropyCoding
import UploadBroadcast.LCBCConverse
import UploadBroadcast.BroadcastShannon

/-! Attainable-alphabet conversion for fully informed nonlinear broadcasts.
No hypothesis restricts the broadcast map to be linear or locally generated. -/
namespace UploadBroadcast.BroadcastOperational
open MeasureTheory ProbabilityTheory
variable {K F S : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] [Finite S] [MeasurableSpace S] [MeasurableSingletonClass S]
local instance sourceMeasurable (L : ℕ) : MeasurableSpace (Source K F L) := ⊤
local instance sourceDiscrete (L : ℕ) : DiscreteMeasurableSpace (Source K F L) :=
  ⟨fun _ => trivial⟩
local instance sourceFinite (L : ℕ) : Finite (Source K F L) := Module.finite_of_finite K

/-- Exact alphabet-cost upper bound for the normalized genuine Shannon
entropy of an arbitrary finite-alphabet broadcast map. -/
theorem entropy_le_cost {L : ℕ} (hL : 0 < L) (s : Source K F L → S) :
    entropy s (uniformOn (Set.univ : Set (Source K F L))) /
      ((L : ℝ) * Real.log (Nat.card K)) ≤
      Real.logb (Nat.card K) (Nat.card (Set.range s)) / L := by
  have hq : (1 : ℝ) < Nat.card K := by exact_mod_cast Finite.one_lt_card (α := K)
  have hs := entropy_div_log_le_logb_attainable
    (uniformOn (Set.univ : Set (Source K F L))) s Measurable.of_discrete (Nat.card K) hq
  have hl : (0 : ℝ) < L := by exact_mod_cast hL
  have hr := div_le_div_of_nonneg_right hs (le_of_lt hl)
  simpa only [div_div, mul_comm (Real.log (Nat.card K)) (L : ℝ)] using hr

/-- Specialization to the actual attained broadcast in the upload model. -/
theorem transmitted_entropy_le_broadcastCost {T : Task K F} {L : ℕ}
    {M : Three → Type*} (c : T.Code L M S) (hL : 0 < L) :
    entropy c.transmitted (uniformOn (Set.univ : Set (Source K F L))) /
      ((L : ℝ) * Real.log (Nat.card K)) ≤ c.broadcastCost :=
  entropy_le_cost hL c.transmitted

/-- The fully informed, arbitrary nonlinear, zero-error first-family bound.
The side-information spaces need not jointly span any demand. -/
theorem first_family {L : ℕ} (hL : 0 < L) (s : Source K F L → S)
    (A U : Three → Submodule K F) (ha : ∀ i, A i ≤ U i)
    (decode : ∀ i, S → Source K (A i) L → Source K (U i) L)
    (hz : ∀ x i, decode i (s x) (observe K F (A i) x) = observe K F (U i) x)
    (i j k : Three) :
    (Module.finrank K (U i) : ℝ) + Module.finrank K (U j) + Module.finrank K (U k) -
      (Module.finrank K (A i) + Module.finrank K (A j) + Module.finrank K (A k)) -
      condRank (U i ⊓ U j) (A j) - condRank (U k ⊓ (U i ⊔ U j)) (A k) ≤
      Real.logb (Nat.card K) (Nat.card (Set.range s)) / L := by
  have hd := fun i => BroadcastShannon.decoder_eq s hL (A i) (U i) (ha i) (decode i)
    (fun x => hz x i)
  exact (LCBCConverse.first_bound (BroadcastShannon.entropyInstance s hL)
    (A i) (A j) (A k) (U i) (U j) (U k) (ha i) (ha j) (ha k)
    (hd i) (hd j) (hd k)).trans (entropy_le_cost hL s)

/-- The fully informed, arbitrary nonlinear, zero-error second-family bound.
Choosing each cyclic triple and each ell gives the nine second-family bounds. -/
theorem second_family {L : ℕ} (hL : 0 < L) (s : Source K F L → S)
    (A U : Three → Submodule K F) (ha : ∀ i, A i ≤ U i)
    (decode : ∀ i, S → Source K (A i) L → Source K (U i) L)
    (hz : ∀ x i, decode i (s x) (observe K F (A i) x) = observe K F (U i) x)
    (i j k ell : Three) (he : ell = i ∨ ell = j ∨ ell = k) :
    (Module.finrank K (U i) : ℝ) + Module.finrank K (U j) + Module.finrank K (U k) -
      (Module.finrank K (A i) + Module.finrank K (A j) + Module.finrank K (A k)) -
      ((condRank (U i ⊓ U j ⊓ U k) (A ell) : ℝ) +
        condRank ((U i ⊓ U j) ⊔ (U i ⊓ U k)) (A i) +
        condRank (U k ⊓ (U i ⊔ U j)) (A k) +
        condRank (U j ⊓ (U i ⊔ U k)) (A j)) / 2 ≤
      Real.logb (Nat.card K) (Nat.card (Set.range s)) / L := by
  have hd := fun i => BroadcastShannon.decoder_eq s hL (A i) (U i) (ha i) (decode i)
    (fun x => hz x i)
  have hE : A ell = A i ∨ A ell = A j ∨ A ell = A k := by
    rcases he with rfl | rfl | rfl <;> simp
  exact (LCBCConverse.second_bound (BroadcastShannon.entropyInstance s hL)
    (A i) (A j) (A k) (U i) (U j) (U k) (A ell)
    (hd i) (hd j) (hd k) hE).trans (entropy_le_cost hL s)

/-- Operational lower bound for every nonlinear code in the upload model,
proved by forgetting uploads and using the fully informed broadcast converse. -/
theorem rankBound_le_broadcastCost {T : Task K F} {L : ℕ}
    {M : Three → Type*} (c : T.Code L M S) (hL : 0 < L) :
    Profile.rankBound T ≤ c.broadcastCost := by
  have hd := fun i => BroadcastShannon.decoder_eq c.transmitted hL (T.A i) (T.U i)
    (T.side_le_signal i) (c.decode i) (fun x => c.zero_error x i)
  exact (LCBCConverse.rankBound_le (BroadcastShannon.entropyInstance c.transmitted hL) T hd).trans
    (transmitted_entropy_le_broadcastCost c hL)

end UploadBroadcast.BroadcastOperational

