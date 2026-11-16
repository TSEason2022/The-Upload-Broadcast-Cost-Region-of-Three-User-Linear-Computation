import UploadBroadcast.CodeAlphabet
import UploadBroadcast.Region

namespace UploadBroadcast.Task
variable {K F : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] {T : Task K F}

theorem costRegion_nonneg {b : ℝ × ℝ} (hb : b ∈ T.costRegion) : 0 ≤ b.1 ∧ 0 ≤ b.2 := by
  have hc : IsClosed {b : ℝ × ℝ | 0 ≤ b.1 ∧ 0 ≤ b.2} :=
    (isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_const continuous_snd)
  apply closure_minimal (s := ⋃ L, T.achievableAt L) (t := {b : ℝ × ℝ | 0 ≤ b.1 ∧ 0 ≤ b.2}) _ hc hb
  intro b h
  obtain ⟨L,hL⟩ := Set.mem_iUnion.mp h
  exact ⟨hL.2.1,hL.2.2.1⟩

theorem upload_budget_bddBelow (T : Task K F) :
    BddBelow {u : ℝ | ∃ d : ℝ, 0 ≤ d ∧ (u,d) ∈ T.costRegion} := by
  refine ⟨0,?_⟩
  rintro u ⟨d,_,h⟩
  exact (costRegion_nonneg h).1

/-- Every actual finite code bounds the operational upload infimum from above. -/
theorem Code.uploadOptimum_le {L : ℕ} {M : Three → Type*} {S : Type*}
    [∀ i, Finite (M i)] [Finite S] (c : T.Code L M S) (hL : 0 < L) :
    T.uploadOptimum ≤ c.uploadCost := by
  apply csInf_le (upload_budget_bddBelow T)
  refine ⟨c.broadcastCost,c.costs_nonneg.2,?_⟩
  apply subset_closure
  exact Set.mem_iUnion.mpr ⟨L,c.mem_achievableAt hL⟩

theorem LinearCode.uploadOptimum_le {L : ℕ} {r : Three → ℕ} {s : ℕ}
    (c : T.LinearCode L r s) (hL : 0 < L) : T.uploadOptimum ≤ c.toCode.uploadCost :=
  c.toCode.uploadOptimum_le hL

/-- A universal code converse remains valid after arbitrary blocklengths and closure. -/
theorem upload_lower_on_region (u : ℝ)
    (hlower : ∀ (L : ℕ) (m : Three → ℕ) (s : ℕ)
      (c : T.Code L (fun i => Fin (m i)) (Fin s)), 0 < L → u ≤ c.uploadCost)
    {b : ℝ × ℝ} (hb : b ∈ T.costRegion) : u ≤ b.1 := by
  have hc : IsClosed {b : ℝ × ℝ | u ≤ b.1} := isClosed_le continuous_const continuous_fst
  apply closure_minimal (s := ⋃ L, T.achievableAt L) (t := {b : ℝ × ℝ | u ≤ b.1}) _ hc hb
  intro b h
  obtain ⟨L,hL,_,_,m,s,c,hu,_⟩ := Set.mem_iUnion.mp h
  exact (hlower L m s c hL).trans hu

/-- Exact operational minimum from a genuine achieving code and a universal
code converse, with the regularized closure handled explicitly. -/
theorem uploadOptimum_eq_of_code {L : ℕ} {M : Three → Type*} {S : Type*}
    [∀ i, Finite (M i)] [Finite S] (c : T.Code L M S) (hL : 0 < L) (u : ℝ)
    (hu : c.uploadCost ≤ u)
    (hlower : ∀ (L : ℕ) (m : Three → ℕ) (s : ℕ)
      (c : T.Code L (fun i => Fin (m i)) (Fin s)), 0 < L → u ≤ c.uploadCost) :
    T.uploadOptimum = u := by
  have hm : c.uploadCost ∈ {v : ℝ | ∃ d : ℝ, 0 ≤ d ∧ (v,d) ∈ T.costRegion} := by
    refine ⟨c.broadcastCost,c.costs_nonneg.2,subset_closure ?_⟩
    exact Set.mem_iUnion.mpr ⟨L,c.mem_achievableAt hL⟩
  apply le_antisymm ((c.uploadOptimum_le hL).trans hu)
  apply le_csInf ⟨c.uploadCost,hm⟩
  rintro v ⟨d,_,h⟩
  exact upload_lower_on_region u hlower h

end UploadBroadcast.Task
