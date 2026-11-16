import UploadBroadcast.CycleUploadOptimality
import UploadBroadcast.RegularExactMenus

/-! Complete source demand-cycle statement on the literal original direct sum,
including the scalar upload count and the nonlinear operational optimum. -/
namespace UploadBroadcast.CycleSourceEndpoint
open Module Profile CycleRepair
variable {K F : Type*} [Field K] [Finite K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- All clauses of the demand-cycle lemma, retaining the actual relay and
an original-field, blocklength-one linear code with exactly d upload symbols. -/
def Repair (T : Task K F) (d : ℕ) (target : Fin 6) : Prop :=
  ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
    T.RelayFeasible P ∧ finrank K P=d ∧ (finrank K P : ℝ)=T.uploadOptimum ∧
    (∀ r : Fin 6, entry (NonzeroDefectRelays.inducedTask T P hl) (.inl r)=
      entry T (.inl r)+(if r=target then 1 else 0)) ∧
    (∀ i l : Three, entry (NonzeroDefectRelays.inducedTask T P hl) (.inr (i,l))=
      entry T (.inr (i,l))) ∧
    ∃ (uploads : Three → ℕ) (c : T.LinearCode 1 uploads d),
      (∑ i, uploads i)=d ∧ c.toCode.uploadCost=(d : ℝ)

private theorem repair_of_relay (T : Task K F) (P : Submodule K F)
    (hl : T.LocallyGenerated P) (hf : T.RelayFeasible P) (target : Fin 6)
    (hu : (finrank K P : ℝ)=T.uploadOptimum)
    (hp : ∀ r : Fin 6, entry (NonzeroDefectRelays.inducedTask T P hl) (.inl r)=
      entry T (.inl r)+(if r=target then 1 else 0))
    (hq : ∀ i l : Three, entry (NonzeroDefectRelays.inducedTask T P hl) (.inr (i,l))=
      entry T (.inr (i,l))) : Repair T (finrank K P) target := by
  obtain ⟨uploads,c,hcount,hcost,_⟩ := RelayLinearComposition.full_relay_linear_code T P hl hf
  refine ⟨P,hl,hf,rfl,hu,hp,hq,uploads,c,hcount,?_⟩
  apply le_antisymm hcost
  rw [hu]
  exact c.uploadOptimum_le (by decide)

variable (K)

theorem positive_canonical (n : ℕ) : Repair (canonicalTask K n) (3*(n+1)+4) 1 := by
  obtain ⟨hl,hf,hd,hp,hq⟩ := canonical_positive_repair K n
  have hh := repair_of_relay (canonicalTask K n) _ hl hf 1
    (CycleUploadOptimality.canonical_positive_optimal K n)
    (fun r => by
      change entry (canonicalRepairedTask K n) (.inl r)=_
      have h := hp r
      linarith only [h]) hq
  rwa [hd] at hh

theorem negative_canonical (n : ℕ) : Repair (canonicalReverseTask K n) (3*(n+1)+4) 3 := by
  obtain ⟨hl,hf,hd,hp,hq⟩ := canonical_reverse_repair K n
  have hh := repair_of_relay (canonicalReverseTask K n) _ hl hf 3
    (CycleUploadOptimality.canonical_reverse_optimal K n)
    (fun r => by
      change entry (canonicalReverseRepairedTask K n) (.inl r)=_
      have h := hp r
      linarith only [h]) hq
  rwa [hd] at hh

variable {K}

theorem repair_of_equiv {G : Type*} [AddCommGroup G] [Module K G] [FiniteDimensional K G]
    (T : Task K F) (S : Task K G) (e : F ≃ₗ[K] G) (he : mapTask e T=S)
    (d : ℕ) (target : Fin 6) (h : Repair S d target) : Repair T d target := by
  obtain ⟨P,hl,hf,hd,hu,hp,hq,_⟩ := h
  let inc : Profile.Index → ℝ := fun r => match r with
    | .inl r => if r=target then 1 else 0
    | .inr _ => 0
  have hi : ∀ r, entry (NonzeroDefectRelays.inducedTask S P hl) r=entry S r+inc r := by
    rintro (r | ⟨i,l⟩)
    · exact hp r
    · simpa only [inc,add_zero] using hq i l
  obtain ⟨Q,hlocal,hfeas,hr,hprofile⟩ :=
    RegularExactMenus.exact_profile_of_equiv T S e he P hl hf inc hi
  have hU : T.uploadOptimum=S.uploadOptimum := by
    have hh := (T.coordinateRetraction e).uploadOptimum_eq
    simpa only [he] using hh
  have hopt : (finrank K Q : ℝ)=T.uploadOptimum := by rw [hr,hu,hU]
  have hrepair := repair_of_relay T Q hlocal hfeas target hopt
    (fun r => hprofile (.inl r))
    (fun i l => by simpa only [inc,add_zero] using hprofile (.inr (i,l)))
  rwa [hr,hd] at hrepair

variable (K)

/-- Literal R_(n+1) plus the positive scalar demand cycle. No activity, chart,
optimality, or profile hypothesis is supplied by the caller. -/
theorem positive_directSum (n : ℕ) :
    Repair (directSum (ResonantRelay.jordanTask K n) (CycleDirectSumCoordinates.cycleTask K))
      (3*(n+1)+4) 1 :=
  repair_of_equiv _ _ (CycleDirectSumCoordinates.coordinates K (n+1))
    (CycleDirectSumCoordinates.map_directSum K (n+1) (JordanResonance.shift K n)
      (JordanResonance.head K n)) _ _ (positive_canonical K n)

/-- The reverse scalar cycle has the exact e4 increment and the same U*. -/
theorem negative_directSum (n : ℕ) :
    Repair (directSum (ResonantRelay.jordanTask K n) (CycleDirectSumCoordinates.reverseCycleTask K))
      (3*(n+1)+4) 3 :=
  repair_of_equiv _ _ (CycleDirectSumCoordinates.coordinates K (n+1))
    (CycleDirectSumCoordinates.map_reverseDirectSum K (n+1) (JordanResonance.shift K n)
      (JordanResonance.head K n)) _ _ (negative_canonical K n)

end UploadBroadcast.CycleSourceEndpoint
