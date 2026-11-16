import UploadBroadcast.RegularRelayOptimality
import UploadBroadcast.ActiveComponentClassification

/-! Every exact resonant menu over the original finite field, transported
through an actual coefficient chart and attaining the nonlinear U*. -/
namespace UploadBroadcast.RegularExactMenus
open Module Profile NonzeroDefectRelays ResidualComponentAdditivity
variable {K F G : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup G] [Module K G] [FiniteDimensional K F] [FiniteDimensional K G]

/-- Exact profile equalities, not just bounds, transport back along a genuine
coefficient chart, with the actual relay rank and all local feasibility data. -/
theorem exact_profile_of_equiv (T : Task K F) (S : Task K G) (e : F ≃ₗ[K] G)
    (he : mapTask e T = S) (P : Submodule K G)
    (hl : S.LocallyGenerated P) (hf : S.RelayFeasible P) (inc : Profile.Index → ℝ)
    (hp : ∀ r, entry (inducedTask S P hl) r = entry S r + inc r) :
    ∃ Q : Submodule K F, ∃ hq : T.LocallyGenerated Q,
      T.RelayFeasible Q ∧ finrank K Q = finrank K P ∧
      ∀ r, entry (inducedTask T Q hq) r = entry T r + inc r := by
  have hb : mapTask e.symm S = T := by
    rw [←he]
    exact ResidualRelayAssembly.mapTask_inverse T e.symm
  have hlocal := (ResidualRelayAssembly.map_relay S e.symm P hl hf).1
  have hfeas := (ResidualRelayAssembly.map_relay S e.symm P hl hf).2
  have hout : ∃ Q : Submodule K F, ∃ hq : (mapTask e.symm S).LocallyGenerated Q,
      (mapTask e.symm S).RelayFeasible Q ∧ finrank K Q = finrank K P ∧
      ∀ r, entry (inducedTask (mapTask e.symm S) Q hq) r = entry (mapTask e.symm S) r + inc r := by
    refine ⟨P.map e.symm.toLinearMap,hlocal,hfeas,e.symm.finrank_map_eq P,?_⟩
    intro r
    rw [RelayCoordinateTransport.inducedTask_map S e.symm P hl hf,
      entry_mapTask,entry_mapTask]
    exact hp r
  simpa only [hb] using hout

variable (K)
/-- The three canonical R_n menus have exact six increments and preserve
every second-family entry, over any field. -/
theorem jordan_exact_profile (n : ℕ) (m : Three) (r : Profile.Index) :
    entry (ResonantRelay.jordanInducedTask K n m) r =
      entry (ResonantRelay.jordanTask K n) r + ResonantFiniteAssembly.increment m r := by
  cases r with
  | inl r =>
    exact (ResonantRelay.jordan_induced_firstProfile K n m r).trans
      (congrArg (fun a : ℝ => a + ResonantRelay.increment m r)
        (ResonantRelay.jordan_full_firstProfile K n r).symm)
  | inr r =>
    obtain ⟨i,l⟩ := r
    have h₁ := ResonantRelay.jordan_induced_secondProfile K n m i l
    have h₂ := ResonantRelay.jordan_full_secondProfile K n i l
    change _ = _ + 0
    linarith only [h₁,h₂]

variable {K}
/-- All three exact menus on the original residual task, with operational
upload optimality; the supplied chart is a literal task equality. -/
theorem from_actual_chart [Finite K] (T : Task K F) (ha : ActiveResidual T) (n : ℕ)
    (e : F ≃ₗ[K] ResonantEndomorphisms.Ambient K (JordanResonance.V K n))
    (he : mapTask e T = ResonantRelay.jordanTask K n) (m : Three) :
    ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P = 3*(n+1)+1 ∧
      (finrank K P : ℝ) = T.uploadOptimum ∧
      (∀ r : Fin 6, entry (inducedTask T P hl) (.inl r) =
        entry T (.inl r) + ResonantRelay.increment m r) ∧
      (∀ i l : Three, entry (inducedTask T P hl) (.inr (i,l)) = entry T (.inr (i,l))) := by
  obtain ⟨hl,hf,hd⟩ := ResonantRelay.jordan_menu_construction K n m
  have hp : ∀ r, entry (inducedTask (ResonantRelay.jordanTask K n)
      (ResonantRelay.jordanRelay K n m) hl) r =
        entry (ResonantRelay.jordanTask K n) r + ResonantFiniteAssembly.increment m r :=
    jordan_exact_profile K n m
  obtain ⟨P,hlocal,hfeas,hr,hprofile⟩ := exact_profile_of_equiv T _ e he _ hl hf _ hp
  have hu := (RegularRelayOptimality.from_actual_chart T ha n e he).1
  refine ⟨P,hlocal,hfeas,hr.trans hd,?_,?_,?_⟩
  · rw [hr,hd]; exact hu
  · intro r
    exact hprofile (.inl r)
  · intro i l
    simpa only [ResonantFiniteAssembly.increment,add_zero] using hprofile (.inr (i,l))

/-- Source-facing regular menu theorem. The original task's indecomposability,
residual activity, zero defect and positive excess construct the chart and
all three exact optimal relays; no family chart is an input oracle. -/
theorem from_actual_regular {K F : Type} [Field K] [Finite K]
    [AddCommGroup F] [Module K F] [FiniteDimensional K F]
    (T : Task K F) (ha : ActiveResidual T)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (hz : ReflectionReduction.defect (EdgeExtraction.configuration T).dimensionVector = 0)
    (hpos : finrank K F < finrank K (T.A 0)+finrank K (T.A 1)+finrank K (T.A 2)) :
    ∃ n : ℕ, ∀ m : Three, ∃ P : Submodule K F, ∃ hl : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P = 3*(n+1)+1 ∧
      (finrank K P : ℝ) = T.uploadOptimum ∧
      (∀ r : Fin 6, entry (inducedTask T P hl) (.inl r) =
        entry T (.inl r) + ResonantRelay.increment m r) ∧
      (∀ i l : Three, entry (inducedTask T P hl) (.inr (i,l)) = entry T (.inr (i,l))) := by
  obtain ⟨n,e,he⟩ := ActiveComponentClassification.regular_assignment T hi hz
    (by simpa only [Task.Spanning,three_iSup] using ha.spanning) hpos
    (exists_nontrivial_demand T ha hi.1)
  exact ⟨n,fun m => from_actual_chart T ha n e he m⟩

end UploadBroadcast.RegularExactMenus
