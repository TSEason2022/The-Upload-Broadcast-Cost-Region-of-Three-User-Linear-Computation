import UploadBroadcast.FiniteSubspaceCertificate

/-! A corrected F5 witness for the entropy-vector insufficiency assertion.
The F3 pair in the cited article fails that assertion. This module retains the
same six formulas over F5 and proves the actual Shannon/operational claims. -/
namespace UploadBroadcast.CitedEntropyCounterexample
open FiniteSubspaceCertificate
open MeasureTheory ProbabilityTheory
instance : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
abbrev K := ZMod 5
abbrev V := K × K × K

def vectors (t : K) : Fin 6 → V :=
  ![(1,0,0),(0,1,0),(0,0,1),(0,1,1),(1,0,1),(1,t,0)]

def side (i : Three) : Space (K := K) (V := V) := Space.line (vectors 1 i.castSucc.castSucc.castSucc)

def demand (t : K) (i : Three) : Space (K := K) (V := V) :=
  Space.line (vectors t (⟨i.val+3,by omega⟩ : Fin 6))

def signal (t : K) (i : Three) : Space (K := K) (V := V) :=
  (side i).join (demand t i)

theorem side_spanning : (⨆ i, (side i).submodule) = ⊤ := by
  rw [Profile.three_iSup]
  apply top_unique
  intro x _
  refine Submodule.mem_sup.mpr ⟨(x.1,x.2.1,0), ?_, (0,0,x.2.2), ?_, ?_⟩
  · refine Submodule.mem_sup.mpr ⟨(x.1,0,0), ?_, (0,x.2.1,0), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x.1,Finset.mem_univ _,by simp [vectors]⟩
    · exact Finset.mem_image.mpr ⟨x.2.1,Finset.mem_univ _,by simp [vectors]⟩
    · ext <;> simp
  · exact Finset.mem_image.mpr ⟨x.2.2,Finset.mem_univ _,by simp [vectors]⟩
  · ext <;> simp

def task (t : K) : Task K V where
  A i := (side i).submodule
  U i := (signal t i).submodule
  side_le_signal i := by rw [signal,Space.submodule_join]; exact le_sup_left
  feasible i := by rw [side_spanning]; exact le_top

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem side_card : ∀ i, (side i).points.card = 5 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem signal_card : ∀ (t : Fin 2) i, (signal (t.val+1) i).points.card = 25 := by decide +kernel

theorem side_rank (i : Three) : Module.finrank K ((task 1).A i) = 1 :=
  (side i).finrank_eq 1 (by simpa using side_card i)

theorem signal_rank (t : Fin 2) (i : Three) :
    Module.finrank K ((task (t.val+1)).U i) = 2 :=
  (signal (t.val+1) i).finrank_eq 2 (by simpa using signal_card t i)


/-- Joint values of exactly the selected original observations; unselected
coordinates are constant zero and therefore add no Shannon entropy. -/
def joint (t : K) (s : Fin 6 → Bool) : V →ₗ[K] (Fin 6 → K) where
  toFun x i := if s i then
    ![x.1,x.2.1,x.2.2,x.2.1+x.2.2,x.1+x.2.2,x.1+t*x.2.1] i else 0
  map_add' := by
    intro x y; ext i; fin_cases i <;> simp <;> split_ifs <;> (try simp) <;> ring
  map_smul' := by
    intro c x; ext i; fin_cases i <;> simp <;> split_ifs <;> (try simp) <;> ring


end UploadBroadcast.CitedEntropyCounterexample
