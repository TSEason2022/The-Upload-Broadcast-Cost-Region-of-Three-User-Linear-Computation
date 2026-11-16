import UploadBroadcast.LinearCode
import Mathlib.Data.Fintype.EquivFin

namespace UploadBroadcast.Task.Code
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  {T : Task K F} {L : ℕ} {M N : Three → Type*} {S B : Type*}

def relabel (c : T.Code L M S) (em : ∀ i, M i ≃ N i) (es : S ≃ B) : T.Code L N B where
  encode i a := em i (c.encode i a)
  broadcast m := es (c.broadcast (fun i => (em i).symm (m i)))
  decode i b a := c.decode i (es.symm b) a
  zero_error x i := by
    simp only [Equiv.symm_apply_apply]
    exact c.zero_error x i

theorem relabel_transmitted (c : T.Code L M S) (em : ∀ i, M i ≃ N i) (es : S ≃ B) :
    (c.relabel em es).transmitted = es ∘ c.transmitted := by
  funext x
  simp only [transmitted,relabel,Equiv.symm_apply_apply,Function.comp_apply]

variable [Finite K] [FiniteDimensional K F]

theorem relabel_costs (c : T.Code L M S) (em : ∀ i, M i ≃ N i) (es : S ≃ B) :
    (c.relabel em es).uploadCost = c.uploadCost ∧
    (c.relabel em es).broadcastCost = c.broadcastCost := by
  constructor
  · unfold uploadCost
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have h : Set.range ((c.relabel em es).encode i) = em i '' Set.range (c.encode i) :=
      Set.range_comp (em i) (c.encode i)
    rw [h,Nat.card_image_of_injective (em i).injective]
  · unfold broadcastCost
    rw [relabel_transmitted,Set.range_comp,Nat.card_image_of_injective es.injective]

theorem finite_relabel [∀ i, Finite (M i)] [Finite S] (c : T.Code L M S) :
    ∃ m : Three → ℕ, ∃ s : ℕ, ∃ d : T.Code L (fun i => Fin (m i)) (Fin s),
      d.uploadCost = c.uploadCost ∧ d.broadcastCost = c.broadcastCost := by
  letI : ∀ i, Fintype (M i) := fun i => Fintype.ofFinite (M i)
  letI := Fintype.ofFinite S
  exact ⟨fun i => Fintype.card (M i),Fintype.card S,
    c.relabel (fun i => Fintype.equivFin (M i)) (Fintype.equivFin S),c.relabel_costs _ _⟩

private theorem log_range_nonneg {X Y : Type*} [Nonempty X] [Finite Y] (f : X → Y) :
    0 ≤ Real.logb (Nat.card K) (Nat.card (Set.range f)) := by
  have hq : (1 : ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
  apply Real.logb_nonneg hq
  exact_mod_cast (Nat.succ_le_of_lt (Nat.card_pos (α := Set.range f)))

theorem costs_nonneg [∀ i, Finite (M i)] [Finite S] (c : T.Code L M S) :
    0 ≤ c.uploadCost ∧ 0 ≤ c.broadcastCost := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => log_range_nonneg (c.encode i)) (Nat.cast_nonneg _)
  · exact div_nonneg (log_range_nonneg c.transmitted) (Nat.cast_nonneg _)

/-- Every actual finite-alphabet code enters the canonical-alphabet region
without changing either attained-alphabet cost. -/
theorem mem_achievableAt [∀ i, Finite (M i)] [Finite S] (c : T.Code L M S)
    (hL : 0 < L) :
    (c.uploadCost,c.broadcastCost) ∈ T.achievableAt L := by
  obtain ⟨m,s,d,hdu,hdd⟩ := c.finite_relabel
  exact ⟨hL,c.costs_nonneg.1,c.costs_nonneg.2,m,s,d,le_of_eq hdu,le_of_eq hdd⟩

end UploadBroadcast.Task.Code

namespace UploadBroadcast.Task.LinearCode
variable {K F : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] {T : Task K F} {L : ℕ} {r : Three → ℕ} {s : ℕ}

theorem costs_nonneg (c : T.LinearCode L r s) :
    0 ≤ c.toCode.uploadCost ∧ 0 ≤ c.toCode.broadcastCost := by
  rw [uploadCost_eq_rank,broadcastCost_eq_rank]
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem mem_achievableAt (c : T.LinearCode L r s) (hL : 0 < L) :
    (c.toCode.uploadCost,c.toCode.broadcastCost) ∈ T.achievableAt L :=
  c.toCode.mem_achievableAt hL

end UploadBroadcast.Task.LinearCode
