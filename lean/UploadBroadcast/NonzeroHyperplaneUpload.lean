import UploadBroadcast.NonzeroHyperplaneProfiles

/-! Exact local upload cost of the constructed nonzero-defect hyperplanes. -/
namespace UploadBroadcast.NonzeroHyperplaneUpload
open Module Profile NonzeroDefectProfile NonzeroFamilyRanks NonzeroRelationRestrictions
open NonzeroDefectRelays NonzeroHyperplaneProfiles

variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

omit [FiniteDimensional K F] in
/-- Feasibility and pair spanning force the form to remain nonzero on every
remote side, even if that user's residual demand happens to be zero. -/
theorem remote_side_nonzero (T : UploadBroadcast.Task K F) (l : F →ₗ[K] K)
    (hl : l ≠ 0) (hU : T.U 0 ≤ LinearMap.ker l)
    (hf : T.RelayFeasible (LinearMap.ker l))
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j = ⊤) (i : Three) (hi : i ≠ 0) :
    ∃ a ∈ T.A i, l a ≠ 0 := by
  by_contra h
  push_neg at h
  have hA : T.A i ≤ LinearMap.ker l := fun a ha => h a ha
  have hUi : T.U i ≤ LinearMap.ker l := (hf i).trans (sup_le hA le_rfl)
  have htop : (⊤ : Submodule K F) ≤ LinearMap.ker l := by
    rw [←hp 0 i hi.symm]
    exact sup_le hU hUi
  exact hl (LinearMap.ker_eq_top.mp (top_unique htop))

/-- The local upload dimensions sum to the hyperplane dimension when the
original side-space excess is one. -/
theorem hyperplane_upload_of_pair_spans (T : UploadBroadcast.Task K F) (l : F →ₗ[K] K)
    (hl : l ≠ 0) (hU : T.U 0 ≤ LinearMap.ker l)
    (hf : T.RelayFeasible (LinearMap.ker l))
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j = ⊤)
    (hexcess : (∑ i, finrank K (T.A i)) = finrank K F+1) :
    (∑ i, finrank K ↥(LinearMap.ker l ⊓ T.A i)) = finrank K (LinearMap.ker l) := by
  have h0 : finrank K ↥(LinearMap.ker l ⊓ T.A 0) = finrank K (T.A 0) := by
    rw [inf_eq_right.mpr ((T.side_le_signal 0).trans hU)]
  have h1 := hyperplane_intersection_finrank (T.A 1) l
    (remote_side_nonzero T l hl hU hf hp 1 (by decide))
  have h2 := hyperplane_intersection_finrank (T.A 2) l
    (remote_side_nonzero T l hl hU hf hp 2 (by decide))
  rw [inf_comm (T.A 1)] at h1
  rw [inf_comm (T.A 2)] at h2
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hl
  simp only [Fin.sum_univ_three] at hexcess ⊢
  omega

/-- Exact local upload cost for any permuted distinguished arm. -/
theorem hyperplane_upload_permuted (T : UploadBroadcast.Task K F) (p : Equiv.Perm Three)
    (l : F →ₗ[K] K) (hl : l ≠ 0) (hU : T.U (p 0) ≤ LinearMap.ker l)
    (hf : T.RelayFeasible (LinearMap.ker l))
    (hp : ∀ i j, i ≠ j → T.U i ⊔ T.U j = ⊤)
    (hexcess : (∑ i, finrank K (T.A i)) = finrank K F+1) :
    (∑ i, finrank K ↥(LinearMap.ker l ⊓ T.A i)) = finrank K (LinearMap.ker l) := by
  have hf' := (reindex_relayFeasible T p _).mpr hf
  have hp' : ∀ i j, i ≠ j → (reindexTask p T).U i ⊔ (reindexTask p T).U j = ⊤ :=
    fun i j hij => hp (p i) (p j) (p.injective.ne hij)
  have hex' : (∑ i, finrank K ((reindexTask p T).A i)) = finrank K F+1 := by
    change (∑ i, finrank K (T.A (p i))) = finrank K F+1
    exact (Equiv.sum_comp p (fun i => finrank K (T.A i))).trans hexcess
  have hh := hyperplane_upload_of_pair_spans (reindexTask p T) l hl hU hf' hp' hex'
  change (∑ i, finrank K ↥(LinearMap.ker l ⊓ T.A (p i))) = finrank K (LinearMap.ker l) at hh
  exact (Equiv.sum_comp p (fun i => finrank K ↥(LinearMap.ker l ⊓ T.A i))).symm.trans hh

/-- Hyperplane family relays carry no redundant local upload coordinates. -/
theorem full_hyperplane_upload (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (hgne : g ≠ .R2) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n)
    (p : Equiv.Perm Three) (l : F →ₗ[K] K) (hU : T.U (p 0) ≤ LinearMap.ker l)
    (hf : T.RelayFeasible (LinearMap.ker l))
    (hdim : finrank K (LinearMap.ker l)+1 = finrank K F) :
    (∑ i, finrank K ↥(LinearMap.ker l ⊓ T.A i)) = fullAmbient g n-1 := by
  have hl : l ≠ 0 := by
    intro hz
    have hk : LinearMap.ker l = ⊤ := LinearMap.ker_eq_top.mpr hz
    have he : finrank K (LinearMap.ker l) = finrank K F := by rw [hk,finrank_top]
    omega
  have hs : (∑ i, finrank K (T.A i)) = finrank K F+1 := by
    simp only [h.side,h.ambient,Fin.sum_univ_three]
    cases g <;> simp_all [fullSide,fullAmbient] <;> omega
  have he := hyperplane_upload_permuted T p l hl hU hf
    (full_rankConditions T hT g n hn h).pair_span hs
  rw [he]
  rw [h.ambient] at hdim
  omega

/-- Exact hyperplane menus together with their actual local upload cost. -/
theorem exists_full_hyperplane_upload_profile [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : UploadBroadcast.Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (hgne : g ≠ .R2) (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T g n) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P = fullAmbient g n-1 ∧
      (∑ i, finrank K ↥(P ⊓ T.A i)) = fullAmbient g n-1 ∧
      (∀ r : Fin 6, entry (inducedTask T P hg) (.inl r) =
        (fullFirst g n r : ℝ) + (firstIncrement g r : ℝ)) ∧
      (∀ i ell : Three, 2 * entry (inducedTask T P hg) (.inr (i,ell)) =
        (doubledSecond g n : ℝ)) := by
  let p : Equiv.Perm Three := Equiv.swap 0 (hyperplaneArm g)
  have hp : p 0 = hyperplaneArm g := by simp [p]
  obtain ⟨l,hU,hg,hf,hdim,hr1,hr2⟩ := exists_full_hyperplane_with_remote_ranks
    hq T hT g hgne n hn h p hp
  have hprofile := full_hyperplane_profile T hT g hgne n hn h p hp l hU hg hf hdim hr1 hr2
  have hupload := full_hyperplane_upload T hT g hgne n hn h p l hU hf hdim
  exact ⟨LinearMap.ker l,hg,hf,by rw [h.ambient] at hdim; omega,hupload,hprofile⟩

end UploadBroadcast.NonzeroHyperplaneUpload
