import UploadBroadcast.NonzeroR2Wedge
import UploadBroadcast.BinaryMenuAllocation
import UploadBroadcast.TaskUserPermutation

/-! All six path choices in the R₂ binary menu on the same actual task,
without assuming a symmetry isomorphism or a desired profile. -/
namespace UploadBroadcast.R2PermutedMenus
open Module Profile NonzeroDefectRelays NonzeroFamilyRanks NonzeroDefectProfile
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
variable {K F : Type} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

def pathPerm : Fin 6 → Equiv.Perm Three :=
  ![Equiv.swap 1 2,Equiv.refl _,(Equiv.swap 0 1).trans (Equiv.swap 0 2),
    Equiv.swap 0 1,Equiv.swap 0 2,(Equiv.swap 0 2).trans (Equiv.swap 0 1)]

def inverseUser : Fin 6 → Three → Three :=
  ![![0,2,1],![0,1,2],![2,0,1],![1,0,2],![2,1,0],![1,2,0]]

def inverseFirst : Fin 6 → Fin 6 → Fin 6 :=
  ![![1,0,4,5,2,3],![0,1,2,3,4,5],![4,5,1,0,3,2],
    ![2,3,0,1,5,4],![5,4,3,2,1,0],![3,2,5,4,0,1]]

theorem inverseFirst_order (k r : Fin 6) :
    (pathPerm k ((firstOrder (inverseFirst k r)).1),
     pathPerm k ((firstOrder (inverseFirst k r)).2.1),
     pathPerm k ((firstOrder (inverseFirst k r)).2.2)) = firstOrder r := by
  fin_cases k <;> fin_cases r <;> decide

theorem inverseFirst_bound (k r : Fin 6) :
    (if inverseFirst k r=3 ∨ inverseFirst k r=4 then 1 else 0 : ℕ)=
      BinaryMenuAllocation.menu .R2 k r := by
  fin_cases k <;> fin_cases r <;> decide

theorem firstEntry_path_reindex (T : Task K F) (k r : Fin 6) :
    entry (reindexTask (pathPerm k) T) (.inl (inverseFirst k r))=entry T (.inl r) := by
  change firstEntry (reindexTask (pathPerm k) T) _ _ _=firstEntry T _ _ _
  rw [firstEntry_reindexTask]
  have he := inverseFirst_order k r
  rw [show pathPerm k ((firstOrder (inverseFirst k r)).1)=(firstOrder r).1 from congrArg Prod.fst he,
    show pathPerm k ((firstOrder (inverseFirst k r)).2.1)=(firstOrder r).2.1 from congrArg (fun x => x.2.1) he,
    show pathPerm k ((firstOrder (inverseFirst k r)).2.2)=(firstOrder r).2.2 from congrArg (fun x => x.2.2) he]

theorem secondEntry_swap_last (T : Task K F) (i j k ell : Three) :
    secondEntry T i j k ell=secondEntry T i k j ell := by
  unfold secondEntry
  rw [sup_comm (T.U i ⊓ T.U j) (T.U i ⊓ T.U k)]
  ring

theorem secondEntry_path_reindex (T : Task K F) (k : Fin 6) (i ell : Three) :
    entry (reindexTask (pathPerm k) T) (.inr (inverseUser k i,inverseUser k ell))=
      entry T (.inr (i,ell)) := by
  simp only [entry,secondEntry_reindexTask]
  fin_cases k <;> fin_cases i <;> fin_cases ell <;>
    simp [pathPerm,inverseUser,Equiv.swap_apply_def]
  all_goals exact secondEntry_swap_last T _ _ _ _

omit [FiniteDimensional K F] in
/-- The symmetric R₂ dimension data survives every user relabeling. -/
theorem dimensions_reindex (T : Task K F) (p : Equiv.Perm Three) (n : ℕ)
    (h : Dimensions T .R2 n) : Dimensions (reindexTask p T) .R2 n := by
  have ha (i : Three) : fullSide .R2 n i=n+1 := by fin_cases i <;> rfl
  have hu (i : Three) : fullSignal .R2 n i=2*n+1 := by fin_cases i <;> rfl
  refine ⟨h.ambient,?_,?_⟩
  · intro i
    change finrank K (T.A (p i))=fullSide .R2 n i
    rw [h.side,ha,ha]
  · intro i
    change finrank K (T.U (p i))=fullSignal .R2 n i
    rw [h.signal,hu,hu]

/-- Every listed R₂ path increment is achieved on the actual original task.
The relay is over the original field, including F₂. -/
theorem full_binary_R2_menu (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (n : ℕ) (hn : 1 ≤ n) (h : Dimensions T .R2 n) (k : Fin 6) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P=3*n-1 ∧
      (∀ r : Fin 6, entry (inducedTask T P hg) (.inl r) ≤
        entry T (.inl r)+(BinaryMenuAllocation.menu .R2 k r : ℝ)) ∧
      (∀ r : Three × Three, entry (inducedTask T P hg) (.inr r)=entry T (.inr r)) := by
  let p := pathPerm k
  obtain ⟨P,hg,hf,hd,hfirst,hsecond⟩ := NonzeroR2Wedge.full_binary_R2_profile (reindexTask p T)
    (TaskUserPermutation.reindex_indecomposable T p hT) n hn (dimensions_reindex T p n h)
  have hg' : T.LocallyGenerated P := (reindex_locallyGenerated T p P).mp hg
  have hf' : T.RelayFeasible P := (reindex_relayFeasible T p P).mp hf
  have he : inducedTask (reindexTask p T) P hg=reindexTask p (inducedTask T P hg') := rfl
  refine ⟨P,hg',hf',hd,?_,?_⟩
  · intro r
    have hh := hfirst (inverseFirst k r)
    rw [he] at hh
    change entry (reindexTask (pathPerm k) (inducedTask T P hg')) (.inl (inverseFirst k r)) ≤
      entry (reindexTask (pathPerm k) T) (.inl (inverseFirst k r))+_ at hh
    rw [firstEntry_path_reindex,firstEntry_path_reindex] at hh
    have hb : (if inverseFirst k r=3 ∨ inverseFirst k r=4 then 1 else 0 : ℝ)=
        (BinaryMenuAllocation.menu .R2 k r : ℝ) := by
      exact_mod_cast inverseFirst_bound k r
    rwa [hb] at hh
  · rintro ⟨i,ell⟩
    have hh := hsecond (inverseUser k i,inverseUser k ell)
    rw [he] at hh
    change entry (reindexTask (pathPerm k) (inducedTask T P hg'))
      (.inr (inverseUser k i,inverseUser k ell))=
      entry (reindexTask (pathPerm k) T) (.inr (inverseUser k i,inverseUser k ell)) at hh
    simpa only [secondEntry_path_reindex] using hh

/-- The actual R₂ relay fits every integer capacity vector paying its charge. -/
theorem full_binary_R2_fits_capacity (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (n : ℕ) (hn : 2 ≤ n) (h : Dimensions T .R2 n) (c : Fin 6 → ℕ)
    (hcap : ∀ p : Fin 3, 1 ≤ c (BinaryMenuAllocation.pairLeft p)+c (BinaryMenuAllocation.pairRight p)) :
    ∃ P : Submodule K F, ∃ hg : T.LocallyGenerated P,
      T.RelayFeasible P ∧ finrank K P=3*n-1 ∧
      (∀ r : Fin 6, entry (inducedTask T P hg) (.inl r) ≤ entry T (.inl r)+(c r : ℝ)) ∧
      (∀ r : Three × Three, entry (inducedTask T P hg) (.inr r)=entry T (.inr r)) := by
  obtain ⟨k,hk⟩ := BinaryMenuAllocation.menu_fits .R2 c (by
    intro p; have hh := hcap p
    fin_cases p <;> simpa [BinaryMenuAllocation.charge] using hh)
  obtain ⟨P,hg,hf,hd,hfirst,hsecond⟩ := full_binary_R2_menu T hT n (by omega) h k
  exact ⟨P,hg,hf,hd,fun r => (hfirst r).trans (add_le_add_left (by exact_mod_cast hk r) _),hsecond⟩

end UploadBroadcast.R2PermutedMenus
