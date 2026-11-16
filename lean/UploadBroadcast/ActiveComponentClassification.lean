import UploadBroadcast.RootClassification
import UploadBroadcast.NonzeroFamilyRanks
import UploadBroadcast.RegularResonantClassification
import UploadBroadcast.TaskUserPermutation
import UploadBroadcast.R2PermutedMenus
import UploadBroadcast.ResonantProfile

/-!
# Actual positive-excess component assignment

The input is an actual indecomposable nested-subspace task, not a real-root
certificate. The output retains a concrete user permutation and a natural
family index. The low-index T₂ tripod is kept: unlike the passive and
omniscience endpoints, it can survive as a profile-preserving residual block.
-/
namespace UploadBroadcast.ActiveComponentClassification
open Module Profile NonzeroDefectProfile NonzeroFamilyRanks
variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Exactly the numerical inclusion thresholds, before active reductions. -/
def LegalIndex (g : Family) (n : ℕ) : Prop :=
  (g = .O ∨ g = .H) → 1 ≤ n

/-- A table predicate on the seven dimensions of the actual labeled task. -/
def InTable (T : Task K F) : Prop :=
  RootClassification.TableRow (finrank K F) (finrank K (T.U 0))
    (finrank K (T.U 1)) (finrank K (T.U 2))
    (finrank K (T.A 0)) (finrank K (T.A 1)) (finrank K (T.A 2))

lemma legal_dimensions (T : Task K F) :
    RootClassification.Legal (finrank K F) (finrank K (T.U 0))
      (finrank K (T.U 1)) (finrank K (T.U 2))
      (finrank K (T.A 0)) (finrank K (T.A 1)) (finrank K (T.A 2)) := by
  have ha (i : Three) := Submodule.finrank_mono (T.side_le_signal i)
  have hu (i : Three) := Submodule.finrank_le (T.U i)
  have ha0 := ha 0; have ha1 := ha 1; have ha2 := ha 2
  have hu0 := hu 0; have hu1 := hu 1; have hu2 := hu 2
  unfold RootClassification.Legal
  omega

/-- The numerical arm sorting is realized by a genuine user permutation. -/
theorem exists_table_permutation (T : Task K F)
    (hq : ReflectionReduction.tits (EdgeExtraction.configuration T).dimensionVector = 1)
    (hpos : finrank K F < finrank K (T.A 0) + finrank K (T.A 1) + finrank K (T.A 2)) :
    ∃ p : Equiv.Perm Three, InTable (reindexTask p T) := by
  have h := RootClassification.classification _ _ _ _ _ _ _ (legal_dimensions T)
    hq (by unfold Structural.excess; omega)
  rcases h with h | h | h | h | h | h
  · exact ⟨Equiv.refl _,h⟩
  · refine ⟨Equiv.swap 1 2, ?_⟩
    simpa [InTable,reindexTask,Equiv.swap_apply_def] using h
  · refine ⟨Equiv.swap 0 1, ?_⟩
    simpa [InTable,reindexTask,Equiv.swap_apply_def] using h
  · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2), ?_⟩
    simpa [InTable,reindexTask,Equiv.swap_apply_def] using h
  · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 1 2), ?_⟩
    simpa [InTable,reindexTask,Equiv.swap_apply_def] using h
  · refine ⟨Equiv.swap 0 2, ?_⟩
    simpa [InTable,reindexTask,Equiv.swap_apply_def] using h

omit [FiniteDimensional K F] in
lemma defect_reindex (T : Task K F) (p : Equiv.Perm Three) :
    ReflectionReduction.defect (EdgeExtraction.configuration (reindexTask p T)).dimensionVector =
      ReflectionReduction.defect (EdgeExtraction.configuration T).dimensionVector := by
  have ha := Equiv.sum_comp p (fun i => (finrank K (T.A i) : ℤ))
  have hu := Equiv.sum_comp p (fun i => (finrank K (T.U i) : ℤ))
  simp [Fin.sum_univ_succ] at ha hu
  simp only [ReflectionReduction.defect,TaskDecomposition.Task.dimensionVector,
    EdgeExtraction.configuration,reindexTask]
  omega

omit [FiniteDimensional K F] in
/-- Conversion to the profile library's labeled family order, with natural
indices and the exact O/H threshold. The T₀ row is excluded by actual defect. -/
theorem family_of_table (T : Task K F) (ht : InTable T)
    (hd : ReflectionReduction.defect (EdgeExtraction.configuration T).dimensionVector ≠ 0) :
    ∃ (p : Equiv.Perm Three) (g : Family) (n : ℕ),
      LegalIndex g n ∧ Dimensions (reindexTask p T) g n := by
  obtain ⟨n,h⟩ := ht
  rcases h with h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hn,hf,hu0,hu1,hu2,ha0,ha1,ha2⟩
  all_goals have hm : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
  · refine ⟨Equiv.refl _,.O,n.toNat,by unfold LegalIndex; omega,?_,?_,?_⟩
    · simp only [fullAmbient]; omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSide] <;> omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSignal] <;> omega
  · refine ⟨Equiv.refl _,.H,n.toNat,by unfold LegalIndex; omega,?_,?_,?_⟩
    · simp only [fullAmbient]; omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSide] <;> omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSignal] <;> omega
  · refine ⟨Equiv.refl _,.R0,n.toNat,by simp [LegalIndex],?_,?_,?_⟩
    · simp only [fullAmbient]; omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSide] <;> omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSignal] <;> omega
  · refine ⟨Equiv.refl _,.R1,n.toNat,by simp [LegalIndex],?_,?_,?_⟩
    · simp only [fullAmbient]; omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSide] <;> omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSignal] <;> omega
  · refine ⟨Equiv.refl _,.R2,n.toNat,by simp [LegalIndex],?_,?_,?_⟩
    · simp only [fullAmbient]; omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSide] <;> omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSignal] <;> omega
  · exfalso
    apply hd
    simp only [ReflectionReduction.defect,TaskDecomposition.Task.dimensionVector,
      EdgeExtraction.configuration]
    omega
  · refine ⟨Equiv.swap 0 2,.T1,n.toNat,by simp [LegalIndex],?_,?_,?_⟩
    · simp only [fullAmbient]; omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSide,Equiv.swap_apply_def] <;> omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSignal,Equiv.swap_apply_def] <;> omega
  · refine ⟨Equiv.swap 0 2,.T2,n.toNat,by simp [LegalIndex],?_,?_,?_⟩
    · simp only [fullAmbient]; omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSide,Equiv.swap_apply_def] <;> omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSignal,Equiv.swap_apply_def] <;> omega
  · refine ⟨Equiv.refl _,.T3,n.toNat,by simp [LegalIndex],?_,?_,?_⟩
    · simp only [fullAmbient]; omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSide] <;> omega
    · intro i; fin_cases i <;> simp [reindexTask,fullSignal] <;> omega

/-- Every positive-excess, nonzero-defect indecomposable over the original
field belongs to one of the eight named families. No q=1 oracle is an input. -/
theorem nonzero_defect_assignment (T : Task K F)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (hd : ReflectionReduction.defect (EdgeExtraction.configuration T).dimensionVector ≠ 0)
    (hpos : finrank K F < finrank K (T.A 0) + finrank K (T.A 1) + finrank K (T.A 2)) :
    ∃ (p : Equiv.Perm Three) (g : Family) (n : ℕ),
      LegalIndex g n ∧ Dimensions (reindexTask p T) g n := by
  obtain ⟨p,hp⟩ := exists_table_permutation T
    ((EdgeExtraction.configuration T).nonzero_defect_tits_one hi hd) hpos
  obtain ⟨q,g,n,hn,h⟩ := family_of_table (reindexTask p T) hp
    (by rwa [defect_reindex])
  exact ⟨q.trans p,g,n,hn,h⟩

/-- All six possible actual user permutations are already represented by the
menu transport library's path index. -/
theorem pathPerm_surjective : Function.Surjective R2PermutedMenus.pathPerm := by
  decide

/-- The indexed version consumed by the finite menu assembly. -/
theorem nonzero_defect_indexed_assignment (T : Task K F)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (hd : ReflectionReduction.defect (EdgeExtraction.configuration T).dimensionVector ≠ 0)
    (hpos : finrank K F < finrank K (T.A 0) + finrank K (T.A 1) + finrank K (T.A 2)) :
    ∃ (k : Fin 6) (g : Family) (n : ℕ), LegalIndex g n ∧
      Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) g n := by
  obtain ⟨p,g,n,hn,h⟩ := nonzero_defect_assignment T hi hd hpos
  obtain ⟨k,rfl⟩ := pathPerm_surjective p
  exact ⟨k,g,n,hn,h⟩

lemma passive_zero (T : Task K F) (g : Family) (hg : g = .R0 ∨ g = .R2)
    (h : Dimensions T g 0) : ∀ i, T.A i = T.U i := by
  intro i
  apply Submodule.eq_of_le_of_finrank_eq (T.side_le_signal i)
  rw [h.side,h.signal]
  rcases hg with rfl | rfl <;> fin_cases i <;> rfl

lemma omniscience_zero (T : Task K F) (g : Family) (hg : g = .R1 ∨ g = .T3)
    (h : Dimensions T g 0) : ∀ i, T.U i = ⊤ := by
  intro i
  apply Submodule.eq_of_le_of_finrank_eq le_top
  rw [h.signal,finrank_top,h.ambient]
  rcases hg with rfl | rfl <;> fin_cases i <;> rfl

/-- The only active, non-omniscience zero-index families are exactly the two
tripod boundaries T₁ and T₂. In particular T₂ must not be discarded. -/
theorem active_nonzero_defect_assignment (T : Task K F)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (hd : ReflectionReduction.defect (EdgeExtraction.configuration T).dimensionVector ≠ 0)
    (hpos : finrank K F < finrank K (T.A 0) + finrank K (T.A 1) + finrank K (T.A 2))
    (hactive : ∃ i, T.A i ≠ T.U i) (hnotom : ∃ i, T.U i ≠ ⊤) :
    ∃ k : Fin 6,
      (∃ (g : Family) (n : ℕ), 1 ≤ n ∧
        Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) g n) ∨
      Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) .T1 0 ∨
      Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) .T2 0 := by
  obtain ⟨k,g,n,hn,h⟩ := nonzero_defect_indexed_assignment T hi hd hpos
  refine ⟨k,?_⟩
  by_cases hnpos : 1 ≤ n
  · exact Or.inl ⟨g,n,hnpos,h⟩
  have hn0 : n = 0 := by omega
  subst n
  have hnp : ¬ (g = .R0 ∨ g = .R2) := by
    intro hp
    obtain ⟨i,hi⟩ := hactive
    have hh := passive_zero _ g hp h ((R2PermutedMenus.pathPerm k).symm i)
    exact hi (by simpa [reindexTask] using hh)
  have hno : ¬ (g = .R1 ∨ g = .T3) := by
    intro hp
    obtain ⟨i,hi⟩ := hnotom
    have hh := omniscience_zero _ g hp h ((R2PermutedMenus.pathPerm k).symm i)
    exact hi (by simpa [reindexTask] using hh)
  cases g <;> simp_all [LegalIndex]

omit [FiniteDimensional K F] in
/-- A labeled configuration isomorphism is an actual operational task chart. -/
theorem mapTask_of_configurationIso {G : Type} [AddCommGroup G] [Module K G]
    (T : Task K F) (S : Task K G)
    (h : TaskDecomposition.ConfigurationIso (EdgeExtraction.configuration T).spaces
      (EdgeExtraction.configuration S).spaces) :
    ∃ e : F ≃ₗ[K] G, mapTask e T = S := by
  obtain ⟨e,he,he'⟩ := h
  have hmap (j : Three × Bool) :
      ((EdgeExtraction.configuration T).spaces j).map e.toLinearMap =
        (EdgeExtraction.configuration S).spaces j := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact he j x hx
    · intro hy
      exact ⟨e.symm y,he' j y hy,e.apply_symm_apply y⟩
  have hA : (mapTask e T).A = S.A := by
    funext i
    exact hmap (i,false)
  have hU : (mapTask e T).U = S.U := by
    funext i
    exact hmap (i,true)
  refine ⟨e,?_⟩
  cases S
  cases hm : mapTask e T
  simp_all only [Task.mk.injEq]

/-- The regular branch supplies an actual chart to the operational Jordan
model, with the library index n denoting the manuscript's R_(n+1). -/
theorem regular_assignment [Finite K] (T : Task K F)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (hzero : ReflectionReduction.defect (EdgeExtraction.configuration T).dimensionVector = 0)
    (hspan : T.Spanning)
    (hpos : finrank K F < finrank K (T.A 0) + finrank K (T.A 1) + finrank K (T.A 2))
    (hactive : ∃ i, T.A i ≠ T.U i) :
    ∃ (n : ℕ) (e : F ≃ₗ[K] ResonantEndomorphisms.Ambient K (JordanResonance.V K n)),
      mapTask e T = ResonantRelay.jordanTask K n := by
  have hs : ((EdgeExtraction.configuration T).A 0 ⊔
      (EdgeExtraction.configuration T).A 1) ⊔ (EdgeExtraction.configuration T).A 2 = ⊤ := by
    simpa only [Task.Spanning,three_iSup,EdgeExtraction.configuration] using hspan
  obtain ⟨n,hiso⟩ := RegularResonantClassification.active_classification
    (EdgeExtraction.configuration T) hi hzero hs hpos hactive
  have hiso' : TaskDecomposition.ConfigurationIso (EdgeExtraction.configuration T).spaces
      (EdgeExtraction.configuration (ResonantRelay.jordanTask K n)).spaces := hiso
  obtain ⟨e,he⟩ := mapTask_of_configurationIso T _ hiso'
  exact ⟨n,e,he⟩

/-- Exhaustive original-field classification of an actual active residual
positive-excess indecomposable. Every label, index and chart is constructed;
neither real-root status nor a family-assignment certificate is assumed. -/
theorem active_residual_assignment [Finite K] (T : Task K F)
    (hi : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (hspan : T.Spanning)
    (hpos : finrank K F < finrank K (T.A 0) + finrank K (T.A 1) + finrank K (T.A 2))
    (hactive : ∃ i, T.A i ≠ T.U i) (hnotom : ∃ i, T.U i ≠ ⊤) :
    (∃ k : Fin 6,
      (∃ (g : Family) (n : ℕ), 1 ≤ n ∧
        Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) g n) ∨
      Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) .T1 0 ∨
      Dimensions (reindexTask (R2PermutedMenus.pathPerm k) T) .T2 0) ∨
    (∃ (n : ℕ) (e : F ≃ₗ[K] ResonantEndomorphisms.Ambient K (JordanResonance.V K n)),
      mapTask e T = ResonantRelay.jordanTask K n) := by
  by_cases hd : ReflectionReduction.defect (EdgeExtraction.configuration T).dimensionVector = 0
  · exact Or.inr (regular_assignment T hi hd hspan hpos hactive)
  · exact Or.inl (active_nonzero_defect_assignment T hi hd hpos hactive hnotom)

end UploadBroadcast.ActiveComponentClassification
