import UploadBroadcast.NonzeroFiniteAssembly

namespace UploadBroadcast.PermutedNonzeroAssembly
open Module Profile GlobalMenuAssembly R2PermutedMenus NonzeroDefectRelays
open scoped BigOperators
set_option maxHeartbeats 1000000

def inversePath : Fin 6 → Fin 6 := ![0,1,5,3,4,2]
def forwardFirst (k : Fin 6) : Fin 6 → Fin 6 := inverseFirst (inversePath k)

theorem forward_inverse (k r : Fin 6) : forwardFirst k (inverseFirst k r)=r := by
  fin_cases k <;> fin_cases r <;> decide

/-- Original opposite-pair label mapped into the canonical family's labels. -/
def pairIndex : Fin 6 → Fin 3 → Fin 3 :=
  ![![1,0,2],![0,1,2],![2,0,1],![2,1,0],![0,2,1],![1,2,0]]

def inversePair (p : Fin 6) (j : Fin 3) : Fin 3 := pairIndex (inversePath p) j

theorem pair_inverse (p : Fin 6) (j : Fin 3) : pairIndex p (inversePair p j)=j := by
  fin_cases p <;> fin_cases j <;> decide

theorem forward_pair (p : Fin 6) (j : Fin 3) :
    (forwardFirst p (BinaryMenuAllocation.pairLeft j)=BinaryMenuAllocation.pairLeft (inversePair p j) ∧
     forwardFirst p (BinaryMenuAllocation.pairRight j)=BinaryMenuAllocation.pairRight (inversePair p j)) ∨
    (forwardFirst p (BinaryMenuAllocation.pairLeft j)=BinaryMenuAllocation.pairRight (inversePair p j) ∧
     forwardFirst p (BinaryMenuAllocation.pairRight j)=BinaryMenuAllocation.pairLeft (inversePair p j)) := by
  fin_cases p <;> fin_cases j <;> decide

def menu (g : NonzeroFiniteAssembly.Kind) (p k r : Fin 6) : ℤ :=
  NonzeroFiniteAssembly.menu g k (inverseFirst p r)
def charge (g : NonzeroFiniteAssembly.Kind) (p : Fin 6) (j : Fin 3) : ℤ :=
  NonzeroFiniteAssembly.charge g (pairIndex p j)

theorem charge_nonneg (g : NonzeroFiniteAssembly.Kind) (p : Fin 6) (j : Fin 3) :
    0 ≤ charge g p j := NonzeroFiniteAssembly.charge_nonneg g _

/-- Integer fitting survives the exact user/entry permutation, with the
corresponding permuted opposite-pair charges. -/
theorem menu_fits (g : NonzeroFiniteAssembly.Kind) (p : Fin 6)
    (c : Fin 6 → ℤ) (hc : ∀ j, 0 ≤ c j)
    (hp : ∀ j, charge g p j ≤
      c (BinaryMenuAllocation.pairLeft j)+c (BinaryMenuAllocation.pairRight j)) :
    ∃ k, ∀ j, menu g p k j ≤ c j := by
  let d : Fin 6 → ℤ := fun j => c (forwardFirst p j)
  have hd : ∀ j, 0 ≤ d j := fun j => hc _
  have hdp : ∀ j, NonzeroFiniteAssembly.charge g j ≤
      d (BinaryMenuAllocation.pairLeft j)+d (BinaryMenuAllocation.pairRight j) := by
    intro j
    have hh := hp (inversePair p j)
    rw [charge,pair_inverse] at hh
    dsimp only [d]
    rcases forward_pair p j with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · rw [hl,hr]
      exact hh
    · rw [hl,hr]
      simpa only [add_comm] using hh
  obtain ⟨k,hk⟩ := NonzeroFiniteAssembly.menu_fits g d hd hdp
  refine ⟨k,fun j => ?_⟩
  have hh := hk (inverseFirst p j)
  simpa only [menu,d,forward_inverse] using hh

variable {K F : Type} [Field K] [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- A locally proved menu on the classified user order yields an actual menu
on the original task, with every increment reindexed literally. -/
theorem menu_pullback {C : Type*} (T : Task K F) (p : Fin 6) (d : ℕ)
    (inc : C → Fin 6 → ℤ)
    (hm : RealizesMenu (reindexTask (pathPerm p) T) d (fun k => firstIncrement (inc k))) :
    RealizesMenu T d (fun k => firstIncrement (fun r => inc k (inverseFirst p r))) := by
  intro k
  obtain ⟨P,hg,hf,hd,hprof⟩ := hm k
  have hl : T.LocallyGenerated P := (reindex_locallyGenerated T (pathPerm p) P).mp hg
  have hfeas : T.RelayFeasible P := (reindex_relayFeasible T (pathPerm p) P).mp hf
  have he : inducedTask (reindexTask (pathPerm p) T) P hg =
      reindexTask (pathPerm p) (inducedTask T P hl) := rfl
  refine ⟨P,hl,hfeas,hd,?_⟩
  intro r
  rw [Task.inducedRelay_entry]
  cases r with
  | inl r =>
    have hh := hprof (.inl (inverseFirst p r))
    rw [Task.inducedRelay_entry,he,firstEntry_path_reindex,firstEntry_path_reindex] at hh
    exact hh
  | inr r =>
    obtain ⟨i,l⟩ := r
    have hh := hprof (.inr (inverseUser p i,inverseUser p l))
    rw [Task.inducedRelay_entry,he,secondEntry_path_reindex,secondEntry_path_reindex] at hh
    exact hh

/-- Actual indecomposability plus Dimensions in any classified user order
supplies a geometric menu on the unpermuted original task. -/
theorem realizes_menu (T : Task K F)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤)
    (p : Fin 6) (g : NonzeroFiniteAssembly.Kind) (n : ℕ) (hn : 1 ≤ n)
    (hdims : NonzeroFamilyRanks.Dimensions (reindexTask (pathPerm p) T)
      (NonzeroFiniteAssembly.family g) n) :
    RealizesMenu T (NonzeroFiniteAssembly.rank g n)
      (fun k => firstIncrement (menu g p k)) :=
  menu_pullback T p _ (NonzeroFiniteAssembly.menu g)
    (NonzeroFiniteAssembly.realizes_menu _ (TaskUserPermutation.reindex_indecomposable T (pathPerm p) hT)
      g n hn hdims)

/-- All root-table family names are covered by the concrete binary menu kinds. -/
def ofFamily : NonzeroDefectProfile.Family → NonzeroFiniteAssembly.Kind
  | .T1 => .hyperplane .T1 | .T2 => .hyperplane .T2 | .T3 => .hyperplane .T3
  | .R0 => .hyperplane .R0 | .R1 => .hyperplane .R1 | .R2 => .R2
  | .O => .hyperplane .O | .H => .hyperplane .H

theorem family_ofFamily (g : NonzeroDefectProfile.Family) :
    NonzeroFiniteAssembly.family (ofFamily g)=g := by cases g <;> rfl

end UploadBroadcast.PermutedNonzeroAssembly
