import UploadBroadcast.PassiveBroadcast
import UploadBroadcast.JointRegionEndpoints
import UploadBroadcast.FiniteProductCoordinates

/-! Lift an actually selected relay through passive deletion, preserving its
rank, all fifteen induced profile entries, and binary separation. -/
namespace UploadBroadcast.PassiveRetraction
open Module
variable {K F V : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup V] [Module K V]
  {T : Task K F} {R : Task K V} (r : PassiveRetraction T R)

theorem embed_injective : Function.Injective r.embed := by
  intro x y h
  have hx := LinearMap.congr_fun r.project_include x
  have hy := LinearMap.congr_fun r.project_include y
  have hh := congrArg r.project h
  change r.project (r.embed x)=x at hx
  change r.project (r.embed y)=y at hy
  rwa [hx,hy] at hh

theorem side_comap_embed (i : Three) : (T.A i).comap r.embed=R.A i := by
  ext x
  constructor
  · intro hx
    have hp := (r.sideProject i ⟨r.embed x,hx⟩).property
    have he := r.sideProject_coe i ⟨r.embed x,hx⟩
    rw [he] at hp
    have hh : r.project (r.embed x)=x := LinearMap.congr_fun r.project_include x
    rwa [hh] at hp
  · intro hx
    have hp := (r.sideInclude i ⟨x,hx⟩).property
    rwa [r.sideInclude_coe] at hp

theorem signal_comap_embed (i : Three) : (T.U i).comap r.embed=R.U i := by
  ext x
  constructor
  · intro hx
    have hp := (r.signalProject i ⟨r.embed x,hx⟩).property
    have he := r.signalProject_coe i ⟨r.embed x,hx⟩
    rw [he] at hp
    have hh : r.project (r.embed x)=x := LinearMap.congr_fun r.project_include x
    rwa [hh] at hp
  · intro hx
    have hp := (r.signalInclude i ⟨x,hx⟩).property
    rwa [r.signalInclude_coe] at hp

theorem embed_relay_locallyGenerated (P : Submodule K V) (hg : R.LocallyGenerated P) :
    T.LocallyGenerated (P.map r.embed) := by
  change P.map r.embed=⨆ i, P.map r.embed ⊓ T.A i
  simp_rw [Submodule.map_inf_eq_map_inf_comap,r.side_comap_embed]
  rw [←Submodule.map_iSup]
  exact congrArg (Submodule.map r.embed) hg

theorem embed_relay_feasible (P : Submodule K V) (hf : R.RelayFeasible P) :
    T.RelayFeasible (P.map r.embed) := by
  intro i x hx
  let u : T.U i := ⟨x,hx⟩
  have hproject : r.project x ∈ R.U i := by
    have hh := (r.signalProject i u).property
    rwa [r.signalProject_coe] at hh
  obtain ⟨a,ha,p,hp,hap⟩ := Submodule.mem_sup.mp (hf i hproject)
  have hea : r.embed a ∈ T.A i := by
    change a ∈ (T.A i).comap r.embed
    rwa [r.side_comap_embed]
  refine Submodule.mem_sup.mpr ⟨r.embed a+(r.localPart i u : F),
    (T.A i).add_mem hea (r.localPart i u).property,r.embed p,⟨p,hp,rfl⟩,?_⟩
  calc
    _ = r.embed (a+p)+(r.localPart i u : F) := by rw [map_add]; abel
    _ = r.embed (r.project x)+(r.localPart i u : F) := by rw [hap]
    _ = x := r.reconstruct i u

/-- Restrict the original injection to the chosen relay coordinates. -/
noncomputable def relayEquiv (P : Submodule K V) : P ≃ₗ[K] P.map r.embed :=
  Submodule.equivMapOfInjective r.embed r.embed_injective P

theorem relayEquiv_subspace (P : Submodule K V) (A : Submodule K V) (B : Submodule K F)
    (h : B.comap r.embed=A) :
    (A.comap P.subtype).map (r.relayEquiv P).toLinearMap=B.comap (P.map r.embed).subtype := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change r.embed x.val ∈ B
    change x.val ∈ B.comap r.embed
    rwa [h]
  · intro hy
    refine ⟨(r.relayEquiv P).symm y,?_,(r.relayEquiv P).apply_symm_apply y⟩
    change ((r.relayEquiv P).symm y).val ∈ A
    rw [←h]
    change r.embed ((r.relayEquiv P).symm y).val ∈ B
    have he := congrArg Subtype.val ((r.relayEquiv P).apply_symm_apply y)
    change r.embed ((r.relayEquiv P).symm y).val=y.val at he
    rw [he]
    exact hy

theorem inducedRelay_map (P : Submodule K V) (hg : R.LocallyGenerated P) :
    Profile.mapTask (r.relayEquiv P) (R.inducedRelay P hg)=
      T.inducedRelay (P.map r.embed) (r.embed_relay_locallyGenerated P hg) := by
  apply FiniteProductCoordinates.task_eq_of_spaces
  · funext i
    exact r.relayEquiv_subspace P (R.A i) (T.A i) (r.side_comap_embed i)
  · funext i
    exact r.relayEquiv_subspace P (R.U i) (T.U i) (r.signal_comap_embed i)

variable [Finite K] [FiniteDimensional K F] [FiniteDimensional K V]

/-- A concrete original-field scalar relay witness survives full passive
restoration, including all fifteen entries and binary separation. -/
noncomputable def restoreRelayWitness {D : ℤ} (w : R.ScalarRelayWitness D) : T.ScalarRelayWitness D where
  space := w.space.map r.embed
  locallyGenerated := r.embed_relay_locallyGenerated w.space w.locallyGenerated
  feasible := r.embed_relay_feasible w.space w.feasible
  upload_optimal := by rw [Profile.finrank_map_injective _ r.embed_injective]; exact w.upload_optimal.trans r.uploadOptimum_eq.symm
  profile_bound j := by
    rw [←r.inducedRelay_map w.space w.locallyGenerated,Profile.entry_mapTask]
    exact w.profile_bound j
  binary_separation hK := by
    obtain ⟨p,hp⟩ := w.binary_separation hK
    refine ⟨p,?_⟩
    have hh := congrArg (Submodule.map (r.relayEquiv w.space).toLinearMap) hp
    rw [Submodule.map_bot,Submodule.map_inf (r.relayEquiv w.space).toLinearMap (r.relayEquiv w.space).injective,Submodule.map_sup] at hh
    simp_rw [r.relayEquiv_subspace w.space _ _ (r.side_comap_embed _)] at hh
    exact hh

include r in
/-- The geometric scalar-selection theorem reduces through the actual
coefficient retraction, rather than assuming original-task optimal relays. -/
theorem scalarRelaySelection_of_reduced (h : R.ScalarRelaySelection) : T.ScalarRelaySelection := by
  intro D hD hU
  rw [r.broadcastOptimum_eq] at hD
  rw [r.uploadOptimum_eq] at hU
  obtain ⟨w⟩ := h D hD hU
  exact ⟨r.restoreRelayWitness w⟩

end UploadBroadcast.PassiveRetraction
