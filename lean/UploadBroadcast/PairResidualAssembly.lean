import UploadBroadcast.ReducedTask

/-!
# Actual omniscience pair summand after pair reduction

Every surviving pair coefficient is demanded by its missing user. Thus the
sum of pair intersections is contained in all three signals, not merely in
an abstract normal-form model.
-/
namespace UploadBroadcast.Task
set_option maxHeartbeats 2000000
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
namespace ActivePairSelection
variable {T : Task K F} (s : T.ActivePairSelection)

theorem pairReduced_side_include (i : Three) (x : LinearMap.ker s.totalPassiveProjection)
    (hx : x ∈ s.pairReducedTask.A i) : (x : F) ∈ T.A i := by
  have hh := (s.pairPassiveRetraction.sideInclude i ⟨x,hx⟩).property
  rw [s.pairPassiveRetraction.sideInclude_coe] at hh
  change (x : F) ∈ (T.A i).map s.simultaneous.toLinearMap at hh
  rwa [s.simultaneous_side] at hh

/-- A surviving pair coefficient has zero passive projection, hence belongs
to the actually selected active pair factor and the missing user's signal. -/
theorem pairReduced_pairKnown_le (i : Three) :
    s.pairReducedTask.pairKnown i ≤ s.pairReducedTask.U i := by
  classical
  intro x hx
  have hpair : (x : F) ∈ T.pairKnown i := by
    apply (Submodule.mem_iInf _).mpr
    intro j
    apply (Submodule.mem_iInf _).mpr
    intro hji
    exact s.pairReduced_side_include j x (s.pairReducedTask.pairKnown_le i j hji hx)
  have htotal : s.totalPassiveProjection x = 0 := x.property
  have hpi : s.passiveProjection i x = 0 := by
    have he : s.totalPassiveProjection x = s.passiveProjection i x := by
      simp only [totalPassiveProjection,LinearMap.sum_apply]
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact s.passiveProjection_own j x (T.pairKnown_le i j hji hpair)
      · simp
    exact he.symm.trans htotal
  let b : T.pairKnown i := ⟨x,hpair⟩
  have hchart : s.chart i (b,0) = (x : F) := s.chart_pair i b
  have hproj : (s.passive i).linearProjOfIsCompl (s.activeFactor i)
      (s.complementary i) b = 0 := by
    rw [s.passiveProjection_apply,← hchart,LinearEquiv.symm_apply_apply] at hpi
    have he := (s.chart i).injective (hpi.trans (s.chart i).map_zero.symm)
    exact Subtype.ext (congrArg Prod.fst he)
  have hb : b ∈ s.activeFactor i :=
    (Submodule.linearProjOfIsCompl_apply_eq_zero_iff (s.complementary i)).mp hproj
  have hm : (b,0) ∈ ((T.U i).map s.simultaneous.toLinearMap).map (s.chart i).symm.toLinearMap := by
    rw [s.simultaneous_separation]
    exact ⟨hb,Submodule.zero_mem _⟩
  obtain ⟨y,hy,he⟩ := hm
  have hyx : y = (x : F) := by
    calc
      y = s.chart i ((s.chart i).symm y) := ((s.chart i).apply_symm_apply y).symm
      _ = s.chart i (b,0) := congrArg (s.chart i) he
      _ = x := hchart
  subst y
  refine ⟨x,hy,?_⟩
  apply Subtype.ext
  change (x : F) - s.totalPassiveProjection x = x
  rw [htotal,sub_zero]

theorem pairReduced_commonKnown_eq_bot (hT : T.commonKnown = ⊥) :
    s.pairReducedTask.commonKnown = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hh : (x : F) ∈ T.commonKnown := by
    apply (Submodule.mem_iInf _).mpr
    intro i
    exact s.pairReduced_side_include i x (s.pairReducedTask.commonKnown_le i hx)
  rw [hT] at hh
  exact Subtype.ext hh
end ActivePairSelection

/-- The surviving pair-known space missing i is contained in its signal,
for every original feasible task and the choice-selected actual reduction. -/
theorem pairReduction_pairKnown_le (T : Task K F) (i : Three) :
    T.pairReduction.pairKnown i ≤ T.pairReduction.U i :=
  T.selectedPairs.pairReduced_pairKnown_le i

theorem pairReduction_commonKnown_eq_bot (T : Task K F) :
    T.pairReduction.commonKnown = ⊥ :=
  T.selectedPairs.pairReduced_commonKnown_eq_bot T.quotientTask_commonKnown_eq_bot

/-- The actual coefficient space jointly formed by the three pair blocks. -/
def pairOmniscience (T : Task K F) : Submodule K F := ⨆ i, T.pairKnown i

/-- Once each pair block is active at its missing user, all users demand
the entire pair space. This identifies the real omniscience summand. -/
theorem pairOmniscience_le_signal (T : Task K F)
    (hactive : ∀ i, T.pairKnown i ≤ T.U i) (i : Three) :
    T.pairOmniscience ≤ T.U i := by
  apply iSup_le
  intro j
  by_cases hji : j = i
  · simpa only [hji] using hactive i
  · exact (T.pairKnown_le j i (Ne.symm hji)).trans (T.side_le_signal i)

theorem pairReduction_pairOmniscience_le (T : Task K F) (i : Three) :
    T.pairReduction.pairOmniscience ≤ T.pairReduction.U i :=
  T.pairReduction.pairOmniscience_le_signal T.pairReduction_pairKnown_le i
end UploadBroadcast.Task

namespace UploadBroadcast.Task.ActivePairSelection
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
variable {T : Task K F} (s : T.ActivePairSelection)

/-- Projection onto a whole intrinsic pair block, rather than just its
passive part. Its chart was constructed from the actual side spaces. -/
def wholePairProjection (i : Three) : F →ₗ[K] F :=
  (s.chart i).toLinearMap.comp ((LinearMap.inl K (T.pairKnown i) (s.residual i)).comp
    ((LinearMap.fst K (T.pairKnown i) (s.residual i)).comp (s.chart i).symm.toLinearMap))

@[simp] theorem wholePairProjection_apply (i : Three) (x : F) :
    s.wholePairProjection i x = s.chart i (((s.chart i).symm x).1,0) := rfl

theorem wholePairProjection_own (i : Three) (x : F) (hx : x ∈ T.A i) :
    s.wholePairProjection i x = 0 := by
  simp [s.chart_own i x hx]

theorem wholePairProjection_range (i : Three) :
    LinearMap.range (s.wholePairProjection i) ≤ T.pairKnown i := by
  rintro _ ⟨x,rfl⟩
  rw [s.wholePairProjection_apply,s.chart_pair]
  exact Subtype.prop _

theorem wholePairProjection_on_pair (i : Three) (x : T.pairKnown i) :
    s.wholePairProjection i x = x := by
  rw [← s.chart_pair i x,s.wholePairProjection_apply,LinearEquiv.symm_apply_apply]

theorem wholePairProjection_idempotent (i : Three) :
    (s.wholePairProjection i).comp (s.wholePairProjection i) = s.wholePairProjection i := by
  apply LinearMap.ext
  intro x
  exact s.wholePairProjection_on_pair i ⟨_,s.wholePairProjection_range i ⟨x,rfl⟩⟩

theorem wholePairProjection_mixed (i j : Three) (hij : i ≠ j) :
    (s.wholePairProjection i).comp (s.wholePairProjection j) = 0 := by
  apply LinearMap.ext
  intro x
  exact s.wholePairProjection_own i _
    (T.pairKnown_le j i hij (s.wholePairProjection_range j ⟨x,rfl⟩))

def totalPairProjection : F →ₗ[K] F := ∑ i, s.wholePairProjection i

theorem totalPairProjection_idempotent :
    s.totalPairProjection.comp s.totalPairProjection = s.totalPairProjection := by
  classical
  apply LinearMap.ext
  intro x
  simp only [totalPairProjection,LinearMap.comp_apply,LinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact LinearMap.congr_fun (s.wholePairProjection_idempotent i) x
  · intro j _ hji
    exact LinearMap.congr_fun (s.wholePairProjection_mixed j i hji) x
  · simp

theorem totalPairProjection_on_pair (i : Three) (x : T.pairKnown i) :
    s.totalPairProjection x = x := by
  classical
  simp only [totalPairProjection,LinearMap.sum_apply]
  rw [Finset.sum_eq_single i]
  · exact s.wholePairProjection_on_pair i x
  · intro j _ hji
    exact s.wholePairProjection_own j x (T.pairKnown_le i j hji x.property)
  · simp

/-- The image of the chosen projection is precisely the intrinsic sum of
pair intersections, so the extracted omniscience space is coordinate-free. -/
theorem totalPairProjection_range :
    LinearMap.range s.totalPairProjection = T.pairOmniscience := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    simp only [totalPairProjection,LinearMap.sum_apply]
    apply (T.pairOmniscience).sum_mem
    intro i _
    exact (le_iSup T.pairKnown i) (s.wholePairProjection_range i ⟨x,rfl⟩)
  · apply iSup_le
    intro i x hx
    exact ⟨x,s.totalPairProjection_on_pair i ⟨x,hx⟩⟩

theorem totalPairProjection_on_omniscience (x : T.pairOmniscience) :
    s.totalPairProjection x = x := by
  have hx : (x : F) ∈ LinearMap.range s.totalPairProjection := by
    rw [s.totalPairProjection_range]
    exact x.property
  obtain ⟨y,hy⟩ := hx
  rw [← hy]
  exact LinearMap.congr_fun s.totalPairProjection_idempotent y

/-- The pair projection preserves every side space simultaneously. -/
theorem totalPairProjection_side (i : Three) (x : F) (hx : x ∈ T.A i) :
    s.totalPairProjection x ∈ T.A i := by
  classical
  simp only [totalPairProjection,LinearMap.sum_apply]
  apply (T.A i).sum_mem
  intro j _
  by_cases hji : j = i
  · subst j
    rw [s.wholePairProjection_own i x hx]
    exact (T.A i).zero_mem
  · exact T.pairKnown_le j i (Ne.symm hji) (s.wholePairProjection_range j ⟨x,rfl⟩)

/-- The actual pair-known sum and the kernel of its projection are
complementary coefficient subspaces. -/
theorem pairResidual_complementary :
    IsCompl T.pairOmniscience (LinearMap.ker s.totalPairProjection) := by
  let p := s.totalPairProjection.codRestrict T.pairOmniscience (by
    intro x
    rw [← s.totalPairProjection_range]
    exact ⟨x,rfl⟩)
  have hp (x : T.pairOmniscience) : p x = x :=
    Subtype.ext (s.totalPairProjection_on_omniscience x)
  have hc := LinearMap.isCompl_of_proj hp
  have hk : LinearMap.ker p = LinearMap.ker s.totalPairProjection := by
    ext x
    constructor
    · intro hx; exact congrArg Subtype.val hx
    · intro hx; exact Subtype.ext hx
  rwa [hk] at hc

/-- The remaining task after projecting out the omniscience pair summand.
This is a structural decomposition, not passive deletion of active demand. -/
def pairResidualTask : Task K (LinearMap.ker s.totalPairProjection) :=
  T.imageTask (Task.complementaryProjection s.totalPairProjection s.totalPairProjection_idempotent)

theorem pairResidualTask_side (i : Three) :
    s.pairResidualTask.A i = (T.A i).comap (LinearMap.ker s.totalPairProjection).subtype := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (T.A i).sub_mem hy (s.totalPairProjection_side i y hy)
  · intro hx
    refine ⟨x,hx,?_⟩
    apply Subtype.ext
    change (x : F) - s.totalPairProjection x = x
    rw [show s.totalPairProjection x = 0 from x.property,sub_zero]

/-- Side and signal coefficients split in the very same ambient complement. -/
theorem pairResidual_side_split (i : Three) :
    T.A i = (T.A i ⊓ T.pairOmniscience) ⊔
      (T.A i ⊓ LinearMap.ker s.totalPairProjection) := by
  apply le_antisymm
  · intro x hx
    refine Submodule.mem_sup.mpr ⟨s.totalPairProjection x,
      ⟨s.totalPairProjection_side i x hx,?_⟩,x-s.totalPairProjection x,⟨?_,?_⟩,?_⟩
    · rw [← s.totalPairProjection_range]
      exact ⟨x,rfl⟩
    · exact (T.A i).sub_mem hx (s.totalPairProjection_side i x hx)
    · change s.totalPairProjection (x-s.totalPairProjection x) = 0
      rw [map_sub,show s.totalPairProjection (s.totalPairProjection x) = s.totalPairProjection x
        from LinearMap.congr_fun s.totalPairProjection_idempotent x,sub_self]
    · abel
  · exact sup_le inf_le_left inf_le_left

theorem pairResidual_signal_split (hactive : ∀ i, T.pairKnown i ≤ T.U i) (i : Three) :
    T.U i = T.pairOmniscience ⊔ (T.U i ⊓ LinearMap.ker s.totalPairProjection) :=
  subspace_split_of_complement _ _ _ s.pairResidual_complementary
    (T.pairOmniscience_le_signal hactive i)
end UploadBroadcast.Task.ActivePairSelection

namespace UploadBroadcast
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Exact product coordinates for any invariant subspace splitting. -/
theorem map_split_coordinates (P Q X : Submodule K F) (hPQ : IsCompl P Q)
    (hX : X = (X ⊓ P) ⊔ (X ⊓ Q)) :
    X.map (Submodule.prodEquivOfIsCompl P Q hPQ).symm.toLinearMap =
      (X.comap P.subtype).prod (X.comap Q.subtype) := by
  let e := Submodule.prodEquivOfIsCompl P Q hPQ
  ext z
  constructor
  · rintro ⟨x,hx,he⟩
    have hz : e z = x := by rw [← he]; exact e.apply_symm_apply x
    exact (invariant_split_membership P Q X hPQ hX z.1 z.2).mp (hz ▸ hx)
  · intro hz
    exact ⟨e z,(invariant_split_membership P Q X hPQ hX z.1 z.2).mpr hz,e.symm_apply_apply z⟩

private theorem task_eq_of_spaces {V : Type*} [AddCommGroup V] [Module K V]
    {T S : Task K V} (hA : T.A = S.A) (hU : T.U = S.U) : T = S := by
  cases T
  cases S
  cases hA
  cases hU
  rfl

namespace Task.ActivePairSelection
variable {T : Task K F} (s : T.ActivePairSelection)

theorem pairResidualTask_signal (hactive : ∀ i, T.pairKnown i ≤ T.U i) (i : Three) :
    s.pairResidualTask.U i = (T.U i).comap (LinearMap.ker s.totalPairProjection).subtype := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    apply (T.U i).sub_mem hy
    apply T.pairOmniscience_le_signal hactive i
    rw [← s.totalPairProjection_range]
    exact ⟨y,rfl⟩
  · intro hx
    refine ⟨x,hx,?_⟩
    apply Subtype.ext
    change (x : F) - s.totalPairProjection x = x
    rw [show s.totalPairProjection x = 0 from x.property,sub_zero]

theorem pairResidualTask_pairKnown_eq_bot (i : Three) :
    s.pairResidualTask.pairKnown i = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hh : (x : F) ∈ T.pairKnown i := by
    apply (Submodule.mem_iInf _).mpr
    intro j
    apply (Submodule.mem_iInf _).mpr
    intro hji
    have h := s.pairResidualTask.pairKnown_le i j hji hx
    rw [s.pairResidualTask_side] at h
    exact h
  change x = 0
  apply Subtype.ext
  exact (s.totalPairProjection_on_pair i ⟨x,hh⟩).symm.trans x.property

/-- No pair intersections remain after the actual omniscience factor is
split off. This concerns the residual task itself, not an assumed model. -/
theorem pairResidualTask_disjoint :
    Disjoint (s.pairResidualTask.A 0) (s.pairResidualTask.A 1) ∧
    Disjoint (s.pairResidualTask.A 0) (s.pairResidualTask.A 2) ∧
    Disjoint (s.pairResidualTask.A 1) (s.pairResidualTask.A 2) := by
  have h₂ := s.pairResidualTask.pairKnown_eq_pair 2 0 1 (by decide) (by decide)
    (by intro l; fin_cases l <;> simp)
  have h₁ := s.pairResidualTask.pairKnown_eq_pair 1 0 2 (by decide) (by decide)
    (by intro l; fin_cases l <;> simp)
  have h₀ := s.pairResidualTask.pairKnown_eq_pair 0 1 2 (by decide) (by decide)
    (by intro l; fin_cases l <;> simp)
  exact ⟨disjoint_iff.mpr (h₂.symm.trans (s.pairResidualTask_pairKnown_eq_bot 2)),
    disjoint_iff.mpr (h₁.symm.trans (s.pairResidualTask_pairKnown_eq_bot 1)),
    disjoint_iff.mpr (h₀.symm.trans (s.pairResidualTask_pairKnown_eq_bot 0))⟩

theorem pairResidualTask_spanning (hT : T.Spanning) : s.pairResidualTask.Spanning := by
  have hT' : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤ := by
    simpa only [Task.Spanning,Profile.three_iSup] using hT
  have h := invariant_complement_spans T.pairOmniscience (LinearMap.ker s.totalPairProjection)
    (T.A 0) (T.A 1) (T.A 2) s.pairResidual_complementary hT'
    ((s.pairResidual_side_split 0).le.trans (sup_le_sup inf_le_right le_rfl))
    ((s.pairResidual_side_split 1).le.trans (sup_le_sup inf_le_right le_rfl))
    ((s.pairResidual_side_split 2).le.trans (sup_le_sup inf_le_right le_rfl))
  simpa only [Task.Spanning,Profile.three_iSup,s.pairResidualTask_side] using h

/-- Actual coefficient map onto the omniscience pair factor. -/
def pairOmniscienceProjection : F →ₗ[K] T.pairOmniscience :=
  s.totalPairProjection.codRestrict T.pairOmniscience (by
    intro x
    rw [← s.totalPairProjection_range]
    exact ⟨x,rfl⟩)

def pairOmniscienceTask : Task K T.pairOmniscience := T.imageTask s.pairOmniscienceProjection

theorem pairOmniscienceTask_side (i : Three) :
    s.pairOmniscienceTask.A i = (T.A i).comap T.pairOmniscience.subtype := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact s.totalPairProjection_side i y hy
  · intro hx
    exact ⟨x,hx,Subtype.ext (s.totalPairProjection_on_omniscience x)⟩

theorem pairOmniscienceTask_signal (hactive : ∀ i, T.pairKnown i ≤ T.U i) (i : Three) :
    s.pairOmniscienceTask.U i = ⊤ := by
  apply top_unique
  intro x _
  exact ⟨x,T.pairOmniscience_le_signal hactive i x.property,
    Subtype.ext (s.totalPairProjection_on_omniscience x)⟩

noncomputable def pairResidualEquivalence :
    (T.pairOmniscience × LinearMap.ker s.totalPairProjection) ≃ₗ[K] F :=
  Submodule.prodEquivOfIsCompl _ _ s.pairResidual_complementary

/-- Both sides and signals split under one actual ambient equivalence; the
first signal factor is omniscience and the second is the pair-free task. -/
theorem pairResidual_mapTask (hactive : ∀ i, T.pairKnown i ≤ T.U i) :
    Profile.mapTask s.pairResidualEquivalence.symm T =
      Profile.directSum s.pairOmniscienceTask s.pairResidualTask := by
  apply task_eq_of_spaces
  · funext i
    change (T.A i).map s.pairResidualEquivalence.symm.toLinearMap =
      (s.pairOmniscienceTask.A i).prod (s.pairResidualTask.A i)
    rw [s.pairOmniscienceTask_side,s.pairResidualTask_side]
    exact map_split_coordinates _ _ _ s.pairResidual_complementary (s.pairResidual_side_split i)
  · funext i
    change (T.U i).map s.pairResidualEquivalence.symm.toLinearMap =
      (s.pairOmniscienceTask.U i).prod (s.pairResidualTask.U i)
    rw [s.pairOmniscienceTask_signal hactive,s.pairResidualTask_signal hactive]
    have hKU := T.pairOmniscience_le_signal hactive i
    have hs : T.U i = (T.U i ⊓ T.pairOmniscience) ⊔
        (T.U i ⊓ LinearMap.ker s.totalPairProjection) := by
      rw [inf_eq_right.mpr hKU]
      exact s.pairResidual_signal_split hactive i
    have hp : (T.U i).comap T.pairOmniscience.subtype = ⊤ := by
      apply top_unique
      intro x _
      exact hKU x.property
    simpa only [hp] using map_split_coordinates _ _ _ s.pairResidual_complementary hs

theorem pairResidual_achievableAt_eq [Finite K] [FiniteDimensional K F]
    (hactive : ∀ i, T.pairKnown i ≤ T.U i) (n : ℕ) :
    T.achievableAt n = (Profile.directSum s.pairOmniscienceTask s.pairResidualTask).achievableAt n := by
  rw [← s.pairResidual_mapTask hactive]
  exact T.coordinate_achievableAt_eq s.pairResidualEquivalence.symm n
end Task.ActivePairSelection
end UploadBroadcast
