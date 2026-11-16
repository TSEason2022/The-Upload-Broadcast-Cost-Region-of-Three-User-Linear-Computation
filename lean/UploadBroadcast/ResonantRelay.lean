import UploadBroadcast.ResonantEndomorphisms
import UploadBroadcast.Model
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases

/-! The original resonant family, with no directed-cycle summand. Relay order: V,R,T. -/
namespace UploadBroadcast.ResonantRelay
set_option linter.unnecessarySeqFocus false
open ResonantEndomorphisms
variable (K X : Type*) [Field K] [AddCommGroup X] [Module K X]
variable (J : X →ₗ[K] X) (h : X →ₗ[K] K)

abbrev Upload := X × X × X × K

def side : Fin 3 → Submodule K (Ambient K X) := ![side₁ K X, side₂ K X, side₃ K X]
def signal : Fin 3 → Submodule K (Ambient K X) := ![total₁ K X, total₂ K X, total₃ K X J h]

def relayMap (m : Fin 3) : Upload K X →ₗ[K] Ambient K X where
  toFun q := ![(q.1,q.2.1,q.2.2.1,q.2.2.2,0),
    (q.1,q.2.1,q.2.2.1,0,q.2.2.2),
    (q.1,q.2.1,q.2.2.1,h q.1-q.2.2.2,q.2.2.2)] m
  map_add' := by intro a b; fin_cases m <;> simp <;> abel
  map_smul' := by intro a b; fin_cases m <;> simp [smul_sub, mul_sub]

def relayForm (m : Fin 3) : Ambient K X →ₗ[K] K where
  toFun p := ![p.2.2.2.2,p.2.2.2.1,p.2.2.2.1+p.2.2.2.2-h p.1] m
  map_add' := by intro a b; fin_cases m <;> simp <;> ring
  map_smul' := by intro a b; fin_cases m <;> simp <;> ring

def relay (m : Fin 3) : Submodule K (Ambient K X) := LinearMap.range (relayMap K X h m)

theorem relayMap_injective (m : Fin 3) : Function.Injective (relayMap K X h m) := by
  intro p q heq
  have h1 := congrArg (fun z : Ambient K X => z.1) heq
  have h2 := congrArg (fun z : Ambient K X => z.2.1) heq
  have h3 := congrArg (fun z : Ambient K X => z.2.2.1) heq
  have h4 := congrArg (fun z : Ambient K X => z.2.2.2.1) heq
  have h5 := congrArg (fun z : Ambient K X => z.2.2.2.2) heq
  fin_cases m <;> simp [relayMap] at * <;> exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (by assumption)))

theorem relay_eq_kernel (m : Fin 3) : relay K X h m = LinearMap.ker (relayForm K X h m) := by
  ext p
  constructor
  · rintro ⟨q,rfl⟩
    fin_cases m <;> simp [relayMap, relayForm, LinearMap.mem_ker]
  · intro hp
    change relayForm K X h m p = 0 at hp
    fin_cases m
    · refine ⟨(p.1,p.2.1,p.2.2.1,p.2.2.2.1), ?_⟩
      simp [relayForm] at hp
      simp only [relayMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero]
      exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl hp.symm)))
    · refine ⟨(p.1,p.2.1,p.2.2.1,p.2.2.2.2), ?_⟩
      simp [relayForm] at hp
      simp only [relayMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_one]
      exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext hp.symm rfl)))
    · refine ⟨(p.1,p.2.1,p.2.2.1,p.2.2.2.2), ?_⟩
      simp [relayForm] at hp
      change (p.1,p.2.1,p.2.2.1,h p.1-p.2.2.2.2,p.2.2.2.2) = p
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl)))
      linear_combination -hp

theorem relay_finrank [FiniteDimensional K X] (m : Fin 3) :
    Module.finrank K (relay K X h m) = 3 * Module.finrank K X + 1 := by
  rw [relay, LinearMap.finrank_range_of_inj (relayMap_injective K X h m)]
  simp [Upload, Module.finrank_prod]
  omega

def local₁ (m : Fin 3) (q : Upload K X) : Ambient K X :=
  (q.1,0,0,![q.2.2.2,0,h q.1] m,0)
def local₂ (m : Fin 3) (q : Upload K X) : Ambient K X :=
  (0,q.2.1,0,0,![0,q.2.2.2,0] m)
def local₃ (m : Fin 3) (q : Upload K X) : Ambient K X :=
  (0,0,q.2.2.1,![(0:K),0,-q.2.2.2] m,![(0:K),0,q.2.2.2] m)

theorem local_mem (m : Fin 3) (q : Upload K X) :
    local₁ K X h m q ∈ relay K X h m ⊓ side K X 0 ∧
    local₂ K X m q ∈ relay K X h m ⊓ side K X 1 ∧
    local₃ K X m q ∈ relay K X h m ⊓ side K X 2 := by
  rw [relay_eq_kernel]
  fin_cases m <;> simp [local₁, local₂, local₃, side, side₁, side₂, side₃,
    LinearMap.mem_ker, relayForm]

theorem relay_locally_generated (m : Fin 3) :
    relay K X h m = ⨆ i : Fin 3, relay K X h m ⊓ side K X i := by
  apply le_antisymm
  · rintro p ⟨q,rfl⟩
    obtain ⟨h1,h2,h3⟩ := local_mem K X h m q
    have heq : relayMap K X h m q = local₁ K X h m q + local₂ K X m q + local₃ K X m q := by
      fin_cases m <;> simp [relayMap, local₁, local₂, local₃, sub_eq_add_neg]
    rw [heq]
    exact Submodule.add_mem _ (Submodule.add_mem _ ((le_iSup (fun i : Fin 3 => relay K X h m ⊓ side K X i) 0) h1) ((le_iSup (fun i : Fin 3 => relay K X h m ⊓ side K X i) 1) h2)) ((le_iSup (fun i : Fin 3 => relay K X h m ⊓ side K X i) 2) h3)
  · exact iSup_le fun _ => inf_le_left

theorem side_spanning : (⨆ i : Fin 3, side K X i) = ⊤ := by
  apply top_unique
  intro p _
  have h1 : (p.1,0,0,p.2.2.2.1,0) ∈ side K X 0 := by simp [side, side₁]
  have h2 : (0,p.2.1,0,0,p.2.2.2.2) ∈ side K X 1 := by simp [side, side₂]
  have h3 : (0,0,p.2.2.1,0,0) ∈ side K X 2 := by simp [side, side₃]
  have heq : p = (p.1,0,0,p.2.2.2.1,0) + (0,p.2.1,0,0,p.2.2.2.2) + (0,0,p.2.2.1,0,0) := by simp
  rw [heq]
  exact Submodule.add_mem _ (Submodule.add_mem _ ((le_iSup (side K X) 0) h1) ((le_iSup (side K X) 1) h2)) ((le_iSup (side K X) 2) h3)

theorem side_le_signal (i : Fin 3) : side K X i ≤ signal K X J h i := by
  intro p hp
  fin_cases i <;> simp [side, signal, side₁, side₂, side₃, total₁, total₂, total₃] at *
  · exact ⟨hp.1.trans hp.2.1.symm,hp.2.2⟩
  · exact ⟨hp.1.trans hp.2.1.symm,hp.2.2⟩
  · simp [hp.1,hp.2.1,hp.2.2]

def task : Task K (Ambient K X) where
  A := side K X
  U := signal K X J h
  side_le_signal := side_le_signal K X J h
  feasible := by intro i; rw [side_spanning]; exact le_top

def adjustment (m i : Fin 3) (p : Ambient K X) : Ambient K X :=
  ![![(0,0,0,0,0),(0,0,0,0,p.2.2.2.2),(0,0,0,-p.2.2.2.2,p.2.2.2.2)],
    ![(0,0,0,p.2.2.2.1,0),(0,0,0,0,0),(0,0,0,p.2.2.2.1,-p.2.2.2.1)],
    ![(0,0,0,p.2.2.2.1+p.2.2.2.2-h p.1,0),
      (0,0,0,0,p.2.2.2.1+p.2.2.2.2-h p.1),(0,0,0,0,0)]] m i

theorem relay_feasible (m i : Fin 3) : signal K X J h i ≤ side K X i ⊔ relay K X h m := by
  intro p hp
  have ha : adjustment K X h m i p ∈ side K X i := by
    fin_cases m <;> fin_cases i <;> simp [adjustment,side,side₁,side₂,side₃]
  have hb : p - adjustment K X h m i p ∈ relay K X h m := by
    rw [relay_eq_kernel]
    fin_cases m <;> fin_cases i <;>
      simp [signal,total₁,total₂,total₃] at hp <;>
      simp [LinearMap.mem_ker,relayForm,adjustment] <;> try linear_combination hp.2
    all_goals ring
  exact Submodule.mem_sup.mpr ⟨_,ha,_,hb,by abel⟩

def inducedTask (m : Fin 3) : Task K (Ambient K X) where
  A := fun i => side K X i ⊓ relay K X h m
  U := fun i => signal K X J h i ⊓ relay K X h m
  side_le_signal := fun i => inf_le_inf (side_le_signal K X J h i) le_rfl
  feasible := by
    intro i
    have heq : (⨆ j : Fin 3, side K X j ⊓ relay K X h m) = relay K X h m := by
      simpa only [inf_comm] using (relay_locally_generated K X h m).symm
    rw [heq]
    exact inf_le_right

end UploadBroadcast.ResonantRelay
