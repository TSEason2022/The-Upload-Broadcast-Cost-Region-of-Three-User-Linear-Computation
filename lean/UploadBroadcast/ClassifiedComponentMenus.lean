import UploadBroadcast.ActualComponentCapacities
import UploadBroadcast.BoundaryComponentMenus
import UploadBroadcast.NonzeroExceptionalRelays

namespace UploadBroadcast.ClassifiedComponentMenus
open Module Profile GlobalMenuAssembly
open NonzeroDefectProfile

def Legal (g : Family) (n : ℕ) : Prop := 1 ≤ n ∨ n=0 ∧ (g=.T1 ∨ g=.T2)
def Preserving (g : Family) (n : ℕ) : Prop :=
  (n=0 ∧ g=.T2) ∨ (n=1 ∧ (g=.T3 ∨ g=.H ∨ g=.R2))
instance (g : Family) (n : ℕ) : Decidable (Preserving g n) := inferInstanceAs (Decidable (_ ∨ _))

def baseMenu (g : Family) (n : ℕ) (k r : Fin 6) : ℤ :=
  if Preserving g n then 0 else NonzeroFiniteAssembly.menu (PermutedNonzeroAssembly.ofFamily g) k r

def menu (g : Family) (n : ℕ) (p k r : Fin 6) : ℤ :=
  baseMenu g n k (R2PermutedMenus.inverseFirst p r)

def relayRank (g : Family) (n : ℕ) : ℕ := fullAmbient g n-codimension g

theorem rank_eq (g : Family) (n : ℕ) :
    NonzeroFiniteAssembly.rank (PermutedNonzeroAssembly.ofFamily g) n=relayRank g n := by
  cases g <;> simp [NonzeroFiniteAssembly.rank,PermutedNonzeroAssembly.ofFamily,
    NonzeroBinaryMenus.family,relayRank,fullAmbient,codimension]

theorem nonpreserving_charge (g : Family) (n : ℕ) (hlegal : Legal g n)
    (hp : ¬ Preserving g n) (j : Fin 3) :
    ActualComponentCapacities.charge_for_family g n j=
      NonzeroFiniteAssembly.charge (PermutedNonzeroAssembly.ofFamily g) j := by
  by_cases hn : n=0
  · subst n
    rcases hlegal with hh | ⟨_,rfl | rfl⟩
    · omega
    · simp [ActualComponentCapacities.charge_for_family,PermutedNonzeroAssembly.ofFamily]
    · exact False.elim (hp (Or.inl ⟨rfl,rfl⟩))
  · have hh : ¬ (n=1 ∧ (g=.T3 ∨ g=.H ∨ g=.R2)) := fun h => hp (Or.inr h)
    simp only [ActualComponentCapacities.charge_for_family,if_neg hn,if_neg hh]

/-- Every classified family, including all boundary and binary exceptional
indices, fits its derived original-profile integer charge. -/
theorem menu_fits (g : Family) (n : ℕ) (hlegal : Legal g n) (p : Fin 6)
    (c : Fin 6 → ℤ) (hc : ∀ r, 0 ≤ c r)
    (hcap : ∀ j, ActualComponentCapacities.charge g n p j ≤
      c (BinaryMenuAllocation.pairLeft j)+c (BinaryMenuAllocation.pairRight j)) :
    ∃ k, ∀ r, menu g n p k r ≤ c r := by
  by_cases hp : Preserving g n
  · exact ⟨0,fun r => by simpa only [menu,baseMenu,if_pos hp] using hc r⟩
  · have hh : ∀ j, PermutedNonzeroAssembly.charge (PermutedNonzeroAssembly.ofFamily g) p j ≤
        c (BinaryMenuAllocation.pairLeft j)+c (BinaryMenuAllocation.pairRight j) := by
      intro j
      have h := hcap j
      rw [ActualComponentCapacities.charge,nonpreserving_charge g n hlegal hp] at h
      exact h
    obtain ⟨k,hk⟩ := PermutedNonzeroAssembly.menu_fits (PermutedNonzeroAssembly.ofFamily g) p c hc hh
    exact ⟨k,fun r => by simpa only [menu,baseMenu,if_neg hp,PermutedNonzeroAssembly.menu] using hk r⟩

def boundaryChoice : Fin 6 → Three := ![0,1,0,1,0,1]

theorem boundary_choice_menu (k r : Fin 6) :
    (NonzeroSameChartMenus.menuIncrement .T1 (boundaryChoice k) r : ℤ)=
      NonzeroFiniteAssembly.menu (.hyperplane .T1) k r := by
  fin_cases k <;> fin_cases r <;> norm_num [boundaryChoice,
    NonzeroSameChartMenus.menuIncrement,NonzeroFiniteAssembly.menu,NonzeroBinaryMenus.menu]

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem boundary_T1_realizes (T : Task K V)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (h : NonzeroFamilyRanks.Dimensions T .T1 0) :
    RealizesMenu T 1 (fun k => GlobalMenuAssembly.firstIncrement
      (NonzeroFiniteAssembly.menu (.hyperplane .T1) k)) := by
  intro k
  obtain ⟨P,hg,hf,hd,_,hfirst,hsecond⟩ := BoundaryComponentMenus.T1_all_menu_choices T hT h (boundaryChoice k)
  refine ⟨P,hg,hf,hd,?_⟩
  intro r
  rw [Task.inducedRelay_entry]
  cases r with
  | inl r =>
    rw [hfirst]
    have he := congrArg (fun z : ℤ => (z : ℝ)) (boundary_choice_menu k r)
    simp only [Int.cast_natCast] at he
    simpa only [GlobalMenuAssembly.firstIncrement,he] using le_refl
      (entry T (.inl r)+(NonzeroFiniteAssembly.menu (.hyperplane .T1) k r : ℝ))
  | inr r => simpa only [GlobalMenuAssembly.firstIncrement,add_zero] using (hsecond r.1 r.2).le

/-- All classified local menus are realized geometrically on their canonical
actual task; no relay, desired rank, or desired profile is assumed. -/
theorem canonical_realizes (T : Task K V)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hlegal : Legal g n) (h : NonzeroFamilyRanks.Dimensions T g n) :
    RealizesMenu T (relayRank g n) (fun k => GlobalMenuAssembly.firstIncrement (baseMenu g n k)) := by
  by_cases hp : Preserving g n
  · intro k
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,hg⟩
    · obtain ⟨P,hl,hf,hd,_,hprof⟩ := BoundaryComponentMenus.T2_optimal_preserving T hT h
      refine ⟨P,hl,hf,?_,?_⟩
      · simpa [relayRank,fullAmbient,codimension] using hd
      · intro r
        rw [Task.inducedRelay_entry,hprof]
        cases r <;> simp [GlobalMenuAssembly.firstIncrement,baseMenu,Preserving]
    · rcases hg with rfl | rfl | rfl
      · obtain ⟨P,hl,hf,hd,hprof⟩ := NonzeroExceptionalRelays.full_tripod_exception_profile T hT h
        refine ⟨P,hl,hf,?_,?_⟩
        · simpa [relayRank,fullAmbient,codimension] using hd
        · intro r
          rw [Task.inducedRelay_entry]
          cases r <;> simpa [GlobalMenuAssembly.firstIncrement,baseMenu,Preserving] using hprof _
      · obtain ⟨P,hl,hf,hd,hprof⟩ := NonzeroExceptionalRelays.full_small_exception_profile T hT .H (Or.inl rfl) h
        refine ⟨P,hl,hf,?_,?_⟩
        · simpa [relayRank,fullAmbient,codimension] using hd
        · intro r
          rw [Task.inducedRelay_entry]
          cases r <;> simpa [GlobalMenuAssembly.firstIncrement,baseMenu,Preserving] using hprof _
      · obtain ⟨P,hl,hf,hd,hprof⟩ := NonzeroExceptionalRelays.full_small_exception_profile T hT .R2 (Or.inr rfl) h
        refine ⟨P,hl,hf,?_,?_⟩
        · simpa [relayRank,fullAmbient,codimension] using hd
        · intro r
          rw [Task.inducedRelay_entry]
          cases r <;> simpa [GlobalMenuAssembly.firstIncrement,baseMenu,Preserving] using hprof _
  · rcases hlegal with hn | ⟨rfl,rfl | rfl⟩
    · have hm := NonzeroFiniteAssembly.realizes_menu T hT (PermutedNonzeroAssembly.ofFamily g) n hn
        (by simpa only [PermutedNonzeroAssembly.family_ofFamily] using h)
      have hb : baseMenu g n=NonzeroFiniteAssembly.menu (PermutedNonzeroAssembly.ofFamily g) := by
        funext k r
        exact if_neg hp
      rw [hb]
      simpa only [rank_eq] using hm
    · have hm := boundary_T1_realizes T hT h
      simpa [relayRank,fullAmbient,codimension,baseMenu,Preserving,PermutedNonzeroAssembly.ofFamily] using hm
    · exact False.elim (hp (Or.inl ⟨rfl,rfl⟩))

/-- Complete local geometric interface on the original component labels,
including zero-index boundaries and all binary low-index exceptions. -/
theorem realizes_menu (T : Task K V)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (g : Family) (n : ℕ) (hlegal : Legal g n) (p : Fin 6)
    (h : NonzeroFamilyRanks.Dimensions (reindexTask (R2PermutedMenus.pathPerm p) T) g n) :
    RealizesMenu T (relayRank g n) (fun k => GlobalMenuAssembly.firstIncrement (menu g n p k)) :=
  PermutedNonzeroAssembly.menu_pullback T p _ (baseMenu g n)
    (canonical_realizes _ (TaskUserPermutation.reindex_indecomposable T (R2PermutedMenus.pathPerm p) hT)
      g n hlegal h)

end UploadBroadcast.ClassifiedComponentMenus
