import UploadBroadcast.FiniteRelayAssembly
import UploadBroadcast.ResidualRelayAssembly

namespace UploadBroadcast.RelayCoordinateTransport
open Module
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem inducedTask_map (T : Task K V) (e : V ≃ₗ[K] W) (P : Submodule K V)
    (hl : T.LocallyGenerated P) (hf : T.RelayFeasible P) :
    NonzeroDefectRelays.inducedTask (Profile.mapTask e T) (P.map e.toLinearMap)
      (ResidualRelayAssembly.map_relay T e P hl hf).1 =
    Profile.mapTask e (NonzeroDefectRelays.inducedTask T P hl) := by
  have ha : (NonzeroDefectRelays.inducedTask (Profile.mapTask e T) (P.map e.toLinearMap)
      (ResidualRelayAssembly.map_relay T e P hl hf).1).A =
      (Profile.mapTask e (NonzeroDefectRelays.inducedTask T P hl)).A := by
    funext i
    exact (Submodule.map_inf _ e.injective).symm
  have hu : (NonzeroDefectRelays.inducedTask (Profile.mapTask e T) (P.map e.toLinearMap)
      (ResidualRelayAssembly.map_relay T e P hl hf).1).U =
      (Profile.mapTask e (NonzeroDefectRelays.inducedTask T P hl)).U := by
    funext i
    exact (Submodule.map_inf _ e.injective).symm
  cases h : NonzeroDefectRelays.inducedTask (Profile.mapTask e T) (P.map e.toLinearMap)
      (ResidualRelayAssembly.map_relay T e P hl hf).1
  cases h' : Profile.mapTask e (NonzeroDefectRelays.inducedTask T P hl)
  simp_all only [Task.mk.injEq]

theorem inducedRelay_entry_map (T : Task K V) (e : V ≃ₗ[K] W) (P : Submodule K V)
    (hl : T.LocallyGenerated P) (hf : T.RelayFeasible P) (r : Profile.Index) :
    Profile.entry ((Profile.mapTask e T).inducedRelay (P.map e.toLinearMap)
      (ResidualRelayAssembly.map_relay T e P hl hf).1) r =
      Profile.entry (T.inducedRelay P hl) r := by
  simp_rw [Task.inducedRelay_entry]
  rw [inducedTask_map T e P hl hf,Profile.entry_mapTask]

/-- An actual decomposition equivalence transports a constructed relay back
to the user's original coefficient task with identical rank and all entries. -/
theorem transport_exists (T : Task K V) (S : Task K W) (e : V ≃ₗ[K] W)
    (he : Profile.mapTask e T=S) (d : ℕ) (budget : Profile.Index → ℝ)
    (h : ∃ P : Submodule K V, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P=d ∧
      ∀ r, Profile.entry (T.inducedRelay P hg) r ≤ budget r) :
    ∃ Q : Submodule K W, ∃ hg : S.LocallyGenerated Q,
      S.RelayFeasible Q ∧ finrank K Q=d ∧
      ∀ r, Profile.entry (S.inducedRelay Q hg) r ≤ budget r := by
  subst S
  obtain ⟨P,hg,hf,hd,hp⟩ := h
  obtain ⟨hgl,hfl⟩ := ResidualRelayAssembly.map_relay T e P hg hf
  refine ⟨P.map e.toLinearMap,hgl,hfl,?_,?_⟩
  · rw [e.finrank_map_eq,hd]
  · intro r
    rw [inducedRelay_entry_map T e P hg hf]
    exact hp r

omit [FiniteDimensional K V] [FiniteDimensional K W] in
/-- Relays also transport along genuine coefficient embeddings. -/
theorem image_relay (T : Task K V) (f : V →ₗ[K] W) (hi : Function.Injective f)
    (P : Submodule K V) (hl : T.LocallyGenerated P) (hf : T.RelayFeasible P) :
    (T.imageTask f).LocallyGenerated (P.map f) ∧ (T.imageTask f).RelayFeasible (P.map f) := by
  constructor
  · change P.map f = ⨆ i, P.map f ⊓ (T.A i).map f
    conv_lhs => rw [show P=⨆ i, P ⊓ T.A i from hl,Submodule.map_iSup]
    congr 1
    funext i
    exact Submodule.map_inf f hi
  · intro i
    exact (Submodule.map_mono (f := f) (hf i)).trans_eq (Submodule.map_sup _ _ _)

omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem inducedTask_image (T : Task K V) (f : V →ₗ[K] W) (hi : Function.Injective f)
    (P : Submodule K V) (hl : T.LocallyGenerated P) (hf : T.RelayFeasible P) :
    NonzeroDefectRelays.inducedTask (T.imageTask f) (P.map f) (image_relay T f hi P hl hf).1 =
      (NonzeroDefectRelays.inducedTask T P hl).imageTask f := by
  have ha : (NonzeroDefectRelays.inducedTask (T.imageTask f) (P.map f) (image_relay T f hi P hl hf).1).A =
      ((NonzeroDefectRelays.inducedTask T P hl).imageTask f).A := by
    funext i
    exact (Submodule.map_inf f hi).symm
  have hu : (NonzeroDefectRelays.inducedTask (T.imageTask f) (P.map f) (image_relay T f hi P hl hf).1).U =
      ((NonzeroDefectRelays.inducedTask T P hl).imageTask f).U := by
    funext i
    exact (Submodule.map_inf f hi).symm
  cases h : NonzeroDefectRelays.inducedTask (T.imageTask f) (P.map f) (image_relay T f hi P hl hf).1
  cases h' : (NonzeroDefectRelays.inducedTask T P hl).imageTask f
  simp_all only [Task.mk.injEq]

theorem inducedRelay_entry_image (T : Task K V) (f : V →ₗ[K] W) (hi : Function.Injective f)
    (P : Submodule K V) (hl : T.LocallyGenerated P) (hf : T.RelayFeasible P) (r : Profile.Index) :
    Profile.entry ((T.imageTask f).inducedRelay (P.map f) (image_relay T f hi P hl hf).1) r =
      Profile.entry (T.inducedRelay P hl) r := by
  simp_rw [Task.inducedRelay_entry]
  rw [inducedTask_image T f hi P hl hf,Profile.entry_imageTask _ f hi]

/-- All properties of a realizing relay survive an actual injective chart. -/
theorem transport_exists_image (T : Task K V) (S : Task K W) (f : V →ₗ[K] W)
    (hi : Function.Injective f) (he : T.imageTask f=S) (d : ℕ) (budget : Profile.Index → ℝ)
    (h : ∃ P : Submodule K V, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P=d ∧
      ∀ r, Profile.entry (T.inducedRelay P hg) r ≤ budget r) :
    ∃ Q : Submodule K W, ∃ hg : S.LocallyGenerated Q,
      S.RelayFeasible Q ∧ finrank K Q=d ∧
      ∀ r, Profile.entry (S.inducedRelay Q hg) r ≤ budget r := by
  subst S
  obtain ⟨P,hg,hf,hd,hp⟩ := h
  obtain ⟨hgl,hfl⟩ := image_relay T f hi P hg hf
  refine ⟨P.map f,hgl,hfl,?_,?_⟩
  · rw [Profile.finrank_map_injective f hi,hd]
  · intro r
    rw [inducedRelay_entry_image T f hi P hg hf]
    exact hp r

end UploadBroadcast.RelayCoordinateTransport
