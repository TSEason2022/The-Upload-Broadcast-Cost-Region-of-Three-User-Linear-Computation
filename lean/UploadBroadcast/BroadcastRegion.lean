import UploadBroadcast.GeneralBroadcastOptimum
import UploadBroadcast.OperationalBounds

namespace UploadBroadcast.Task.Code
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  {T : Task K F} {L : ℕ} {M : Three → Type*} {S : Type*}

/-- A fully informed server simulates every actual possibly nonlinear relay code. -/
def fullyInformed (c : T.Code L M S) : BlockBroadcastCode T.A T.U L S where
  encode := c.transmitted
  decode := c.decode
  zero_error := c.zero_error

theorem fullyInformed_cost (c : T.Code L M S) [Finite K] [FiniteDimensional K F] :
    c.fullyInformed.cost = c.broadcastCost := rfl

variable [Finite K] [FiniteDimensional K F] [Finite S]

theorem broadcastOptimum_le (c : T.Code L M S) (hL : 0 < L) :
    broadcastOptimum T.A T.U ≤ c.broadcastCost := by
  rw [general_broadcastOptimum_eq_rankBound T.A T.U T.side_le_signal]
  exact c.fullyInformed.rankBound_le_cost T.side_le_signal hL

end UploadBroadcast.Task.Code

namespace UploadBroadcast.Task
variable {K F : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] {T : Task K F}

theorem broadcastOptimum_le_of_achievable {L : ℕ} {b : ℝ × ℝ}
    (h : b ∈ T.achievableAt L) : broadcastOptimum T.A T.U ≤ b.2 := by
  obtain ⟨hL,_,_,m,s,c,_,hd⟩ := h
  exact (c.broadcastOptimum_le hL).trans hd

/-- The fully informed broadcast converse holds throughout the actual closed
upload/broadcast region, not just on linear or scalar codes. -/
theorem broadcastOptimum_le_of_costRegion {b : ℝ × ℝ} (hb : b ∈ T.costRegion) :
    broadcastOptimum T.A T.U ≤ b.2 := by
  have hc : IsClosed {b : ℝ × ℝ | broadcastOptimum T.A T.U ≤ b.2} :=
    isClosed_le continuous_const continuous_snd
  apply closure_minimal (s := ⋃ L, T.achievableAt L)
    (t := {b : ℝ × ℝ | broadcastOptimum T.A T.U ≤ b.2}) _ hc hb
  intro b h
  obtain ⟨L,hL⟩ := Set.mem_iUnion.mp h
  exact broadcastOptimum_le_of_achievable hL

/-- With the broadcast converse proved, final region assembly needs only
the upload converse and a genuine simultaneous length-two corner. -/
theorem region_eq_rectangle_of_upload_and_corner (u : ℝ)
    (hcorner : (u,broadcastOptimum T.A T.U) ∈ T.achievableAt 2)
    (hu : ∀ (L : ℕ) (m : Three → ℕ) (s : ℕ)
      (c : T.Code L (fun i => Fin (m i)) (Fin s)), 0 < L → u ≤ c.uploadCost) :
    T.achievableAt 2 = budgetRectangle u (broadcastOptimum T.A T.U) ∧
    T.costRegion = budgetRectangle u (broadcastOptimum T.A T.U) := by
  apply T.region_eq_rectangle_of_corner u (broadcastOptimum T.A T.U) hcorner
  intro L b h
  refine ⟨?_,broadcastOptimum_le_of_achievable h⟩
  obtain ⟨hL,_,_,m,s,c,hcu,_⟩ := h
  exact (hu L m s c hL).trans hcu

end UploadBroadcast.Task
