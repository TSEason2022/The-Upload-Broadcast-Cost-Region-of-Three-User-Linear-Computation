import UploadBroadcast.ActiveReduction
import UploadBroadcast.PairSelection
import UploadBroadcast.ProfileTransport
import UploadBroadcast.ThreeSubspaceNormalForm

/-!
# Operational first steps of active reduction

These statements start with an arbitrary feasible task. Common-known quotienting
is constructed, rather than assumed as a rate-region identity. The later
simultaneous active-pair and empty-row assembly is not asserted here.
-/
namespace UploadBroadcast
namespace Task
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- The actual three-way common-known coefficient space. -/
def commonKnown (T : Task K F) : Submodule K F := ⨅ i, T.A i

theorem commonKnown_le (T : Task K F) (i : Three) : T.commonKnown ≤ T.A i :=
  iInf_le _ i

/-- Push task coefficient spaces along any linear map. -/
def imageTask {V : Type*} [AddCommGroup V] [Module K V]
    (T : Task K F) (f : F →ₗ[K] V) : Task K V where
  A i := (T.A i).map f
  U i := (T.U i).map f
  side_le_signal i := Submodule.map_mono (T.side_le_signal i)
  feasible i := by
    rw [← Submodule.map_iSup]
    exact Submodule.map_mono (T.feasible i)

/-- Delete the image of an idempotent ambient projection. -/
def complementaryProjection (P : F →ₗ[K] F) (hP : P.comp P = P) :
    F →ₗ[K] LinearMap.ker P :=
  (LinearMap.id - P).codRestrict (LinearMap.ker P) (by
    intro x
    change P (x - P x) = 0
    rw [map_sub, show P (P x) = P x from LinearMap.congr_fun hP x, sub_self])

/-- If all removed signal components are locally known, the idempotent
projection is a genuine nonlinear operational deletion, for arbitrary overlap
among the users' passive side spaces. -/
def idempotentPassiveRetraction (T : Task K F) (P : F →ₗ[K] F)
    (hP : P.comp P = P) (hlocal : ∀ i x, x ∈ T.U i → P x ∈ T.A i) :
    PassiveRetraction T (T.imageTask (complementaryProjection P hP)) := by
  let p := complementaryProjection P hP
  let e := (LinearMap.ker P).subtype
  have hpe : p.comp e = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (x : F) - P x = x
    rw [show P x = 0 from x.property, sub_zero]
  have hepa (i : Three) (x : F) (hx : x ∈ T.A i) : e (p x) ∈ T.A i :=
    (T.A i).sub_mem hx (hlocal i x (T.side_le_signal i hx))
  have hepu (i : Three) (x : F) (hx : x ∈ T.U i) : e (p x) ∈ T.U i :=
    (T.U i).sub_mem hx (T.side_le_signal i (hlocal i x hx))
  exact passiveRetractionOfProjection T (T.imageTask p) p e hpe
    (fun i x hx => ⟨x, hx, rfl⟩)
    (by intro i x hx; obtain ⟨y, hy, rfl⟩ := hx; exact hepa i y hy)
    (fun i x hx => ⟨x, hx, rfl⟩)
    (by intro i x hx; obtain ⟨y, hy, rfl⟩ := hx; exact hepu i y hy)
    (by intro i x hx; change x - (x - P x) ∈ T.A i; simpa using hlocal i x hx)

/-- The private coordinates that occur in at least one remote signal. -/
def remotelyUsedPrivate {V : Type*} [AddCommGroup V] [Module K V]
    (T : Task K F) (i : Three) (p : F →ₗ[K] V) : Submodule K V :=
  ⨆ j, ⨆ (_ : j ≠ i), (T.U j).map p

/-- All private directions unused by remote signals can be removed by an
actual idempotent passive projection. Only the private embedding/retraction
and local knowledge are assumptions, never a code or preservation statement. -/
theorem exists_unusedPrivateProjection {V : Type*} [AddCommGroup V] [Module K V]
    (T : Task K F) (i : Three) (p : F →ₗ[K] V) (e : V →ₗ[K] F)
    (hpe : p.comp e = LinearMap.id) (he : LinearMap.range e ≤ T.A i) :
    ∃ P : F →ₗ[K] F,
      P.comp P = P ∧
      (∀ j x, x ∈ T.U j → P x ∈ T.A j) ∧
      (∀ v, P (e v) = 0 ↔ v ∈ T.remotelyUsedPrivate i p) := by
  classical
  let A := T.remotelyUsedPrivate i p
  obtain ⟨B, hB⟩ := A.exists_isCompl
  let π := B.linearProjOfIsCompl A hB.symm
  let P := e.comp (B.subtype.comp (π.comp p))
  have hpe' (v : V) : p (e v) = v := LinearMap.congr_fun hpe v
  have hinj : Function.Injective e := by
    intro a b hab
    simpa only [hpe'] using congrArg p hab
  have hp (x : F) : P x = e (π (p x)) := rfl
  refine ⟨P, ?_, ?_, ?_⟩
  · ext x
    change e (π (p (e (π (p x))))) = e (π (p x))
    rw [hpe', Submodule.linearProjOfIsCompl_apply_left]
  · intro j x hx
    by_cases hji : j = i
    · subst j
      exact he ⟨π (p x), rfl⟩
    · have hle : (T.U j).map p ≤ A := le_iSup_of_le j (le_iSup_of_le hji le_rfl)
      have ha : p x ∈ A := hle ⟨x, hx, rfl⟩
      have hz := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hB.symm).mpr ha
      rw [hp, hz]
      simp
  · intro v
    rw [hp, hpe']
    constructor
    · intro hz
      have hv : (π v : V) = 0 := hinj (hz.trans e.map_zero.symm)
      exact (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hB.symm).mp
        (Subtype.ext hv)
    · intro hv
      rw [(Submodule.linearProjOfIsCompl_apply_eq_zero_iff hB.symm).mpr hv]
      exact e.map_zero

/-- Removing all unused private directions preserves every fixed-block
region. The removed projection is selected from the actual remote signals. -/
theorem exists_unusedPrivateReduction {V : Type*} [AddCommGroup V] [Module K V]
    [Finite K] [FiniteDimensional K F]
    (T : Task K F) (i : Three) (p : F →ₗ[K] V) (e : V →ₗ[K] F)
    (hpe : p.comp e = LinearMap.id) (he : LinearMap.range e ≤ T.A i) :
    ∃ (P : F →ₗ[K] F) (hP : P.comp P = P),
      (∀ v, P (e v) = 0 ↔ v ∈ T.remotelyUsedPrivate i p) ∧
      (∀ L, T.achievableAt L =
        (T.imageTask (complementaryProjection P hP)).achievableAt L) := by
  obtain ⟨P, hP, hlocal, hused⟩ := T.exists_unusedPrivateProjection i p e hpe he
  exact ⟨P, hP, hused, fun L => (T.idempotentPassiveRetraction P hP hlocal).achievableAt_eq L⟩

/-- Quotient every task space by a common-known subspace. -/
def quotientTask (T : Task K F) (C : Submodule K F) : Task K (F ⧸ C) where
  A i := (T.A i).map C.mkQ
  U i := (T.U i).map C.mkQ
  side_le_signal i := Submodule.map_mono (T.side_le_signal i)
  feasible i := by
    rw [← Submodule.map_iSup]
    exact Submodule.map_mono (T.feasible i)

/-- Any linear section of the quotient map constructs both nonlinear code
transports. The only deleted coefficients are locally known at every user. -/
def quotientRetractionOfSection (T : Task K F) (C : Submodule K F)
    (hC : ∀ i, C ≤ T.A i) (e : (F ⧸ C) →ₗ[K] F)
    (he : C.mkQ.comp e = LinearMap.id) :
    PassiveRetraction T (T.quotientTask C) := by
  have hdiff (x : F) : x - e (C.mkQ x) ∈ C := by
    apply (Submodule.Quotient.mk_eq_zero C).mp
    change C.mkQ (x - e (C.mkQ x)) = 0
    rw [map_sub, show C.mkQ (e (C.mkQ x)) = C.mkQ x from LinearMap.congr_fun he _, sub_self]
  have hmem (X : Submodule K F) (hCX : C ≤ X) (x : F ⧸ C)
      (hx : x ∈ X.map C.mkQ) : e x ∈ X := by
    obtain ⟨y, hy, rfl⟩ := hx
    have hh := X.sub_mem hy (hCX (hdiff y))
    simpa only [sub_sub_cancel] using hh
  exact passiveRetractionOfProjection T (T.quotientTask C) C.mkQ e he
    (fun i x hx => ⟨x, hx, rfl⟩)
    (fun i x hx => hmem _ (hC i) x hx)
    (fun i x hx => ⟨x, hx, rfl⟩)
    (fun i x hx => hmem _ ((hC i).trans (T.side_le_signal i)) x hx)
    (fun i x _ => hC i (hdiff x))

/-- Common quotienting always has concrete deletion and restoration maps. -/
theorem exists_quotientRetraction (T : Task K F) (C : Submodule K F)
    (hC : ∀ i, C ≤ T.A i) : Nonempty (PassiveRetraction T (T.quotientTask C)) := by
  obtain ⟨Q, hQ⟩ := C.exists_isCompl
  let e := Q.subtype.comp (Submodule.quotientEquivOfIsCompl C Q hQ).toLinearMap
  have he : C.mkQ.comp e = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact Submodule.mk_quotientEquivOfIsCompl_apply C Q hQ x
  exact ⟨T.quotientRetractionOfSection C hC e he⟩

/-- Exact arbitrary-nonlinear fixed-block invariance of the common quotient. -/
theorem commonKnown_achievableAt_eq [Finite K] [FiniteDimensional K F]
    (T : Task K F) (L : ℕ) :
    T.achievableAt L = (T.quotientTask T.commonKnown).achievableAt L := by
  obtain ⟨r⟩ := T.exists_quotientRetraction T.commonKnown T.commonKnown_le
  exact r.achievableAt_eq L

theorem commonKnown_costRegion_eq [Finite K] [FiniteDimensional K F]
    (T : Task K F) : T.costRegion = (T.quotientTask T.commonKnown).costRegion := by
  obtain ⟨r⟩ := T.exists_quotientRetraction T.commonKnown T.commonKnown_le
  exact r.costRegion_eq

/-- Ambient coordinate changes also supply concrete two-way code transports. -/
def coordinateRetraction {V : Type*} [AddCommGroup V] [Module K V]
    (T : Task K F) (e : F ≃ₗ[K] V) : PassiveRetraction T (Profile.mapTask e T) :=
  passiveRetractionOfProjection T (Profile.mapTask e T) e.toLinearMap e.symm.toLinearMap
    (by apply LinearMap.ext; intro x; exact e.apply_symm_apply x)
    (fun i x hx => ⟨x, hx, rfl⟩)
    (by intro i x hx; obtain ⟨y, hy, rfl⟩ := hx; simpa using hy)
    (fun i x hx => ⟨x, hx, rfl⟩)
    (by intro i x hx; obtain ⟨y, hy, rfl⟩ := hx; simpa using hy)
    (by intro i x _; simp)

theorem coordinate_achievableAt_eq {V : Type*} [AddCommGroup V] [Module K V]
    [Finite K] [FiniteDimensional K F] [FiniteDimensional K V]
    (T : Task K F) (e : F ≃ₗ[K] V) (L : ℕ) :
    T.achievableAt L = (Profile.mapTask e T).achievableAt L :=
  (T.coordinateRetraction e).achievableAt_eq L

/-- Common quotienting preserves the normalized spanning assumption. -/
theorem quotientTask_spanning (T : Task K F) (hT : T.Spanning) (C : Submodule K F) :
    (T.quotientTask C).Spanning := by
  unfold Spanning quotientTask
  rw [← Submodule.map_iSup, hT, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr C.mkQ_surjective

/-- The common intersection is genuinely zero after quotienting. -/
theorem quotientTask_commonKnown_eq_bot (T : Task K F) :
    (T.quotientTask T.commonKnown).commonKnown = ⊥ := by
  change (⨅ i, (T.A i).map T.commonKnown.mkQ) = ⊥
  rw [← Submodule.map_iInf_of_ker_le T.commonKnown.mkQ_surjective (by
    rw [Submodule.ker_mkQ]; exact le_rfl)]
  exact T.commonKnown.mkQ_map_self

/-- Intersection compatibility of quotienting by a subspace in the second
factor; unlike injective-map intersection lemmas this applies to quotients. -/
theorem quotient_map_inf (C P Q : Submodule K F) (hCQ : C ≤ Q) :
    (P ⊓ Q).map C.mkQ = P.map C.mkQ ⊓ Q.map C.mkQ := by
  apply le_antisymm
  · exact le_inf (Submodule.map_mono inf_le_left) (Submodule.map_mono inf_le_right)
  · rintro y ⟨⟨p, hp, hpy⟩, ⟨q, hq, hqy⟩⟩
    have hpq : p - q ∈ C := by
      apply (Submodule.Quotient.mk_eq_zero C).mp
      change C.mkQ (p - q) = 0
      rw [map_sub, hpy, hqy, sub_self]
    refine ⟨p, ⟨hp, ?_⟩, hpy⟩
    simpa using Q.add_mem (hCQ hpq) hq

/-- Intrinsic pair-active rank, using the original task before quotienting. -/
noncomputable def activePairRank [FiniteDimensional K F] (T : Task K F)
    (i j k : Three) : ℕ :=
  Module.finrank K ↥(T.U i ⊓ T.A j ⊓ T.A k) - Module.finrank K T.commonKnown

/-- The actual intersection after common quotienting has precisely the
manuscript's active-pair rank. No freely assigned parameter occurs here. -/
theorem activePairRank_eq_quotient [FiniteDimensional K F] (T : Task K F)
    (i j k : Three) :
    T.activePairRank i j k = Module.finrank K
      ↥((T.quotientTask T.commonKnown).U i ⊓
        (T.quotientTask T.commonKnown).A j ⊓ (T.quotientTask T.commonKnown).A k) := by
  change _ = Module.finrank K ↥((T.U i).map T.commonKnown.mkQ ⊓
    (T.A j).map T.commonKnown.mkQ ⊓ (T.A k).map T.commonKnown.mkQ)
  rw [← quotient_map_inf _ _ _ (T.commonKnown_le j),
    ← quotient_map_inf _ _ _ (T.commonKnown_le k),
    ← condRank_eq_finrank_quotient_image]
  have hc : T.commonKnown ≤ T.U i ⊓ T.A j ⊓ T.A k :=
    le_inf (le_inf ((T.commonKnown_le i).trans (T.side_le_signal i))
      (T.commonKnown_le j)) (T.commonKnown_le k)
  unfold condRank activePairRank
  rw [sup_eq_right.mpr hc]

/-- Arbitrary normalized tasks admit the proved side-space normal form after
common quotienting. This is an existence theorem, not a normal-form input. -/
theorem exists_commonQuotient_normalForm (T : Task K F) (hT : T.Spanning) :
    ∃ s : ThreeSubspacePeeling
      ((T.quotientTask T.commonKnown).A 0)
      ((T.quotientTask T.commonKnown).A 1)
      ((T.quotientTask T.commonKnown).A 2), s.pair23.HasResidualNormalForm := by
  apply exists_three_subspace_normal_form
  rw [← Profile.three_iSup]
  exact T.quotientTask_spanning hT T.commonKnown

end Task
end UploadBroadcast
