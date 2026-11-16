import UploadBroadcast.Model
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Explicit demand-cycle repair coordinates

This file develops the scalar construction in `eq:endpoint-upload` for
arbitrary vector length. The coordinate identities below use arbitrary
linear A and h; profile identities and optimality require additional
resonant-family hypotheses and are not asserted by these identities.
-/
namespace UploadBroadcast.CycleRepair

variable (K : Type*) [Field K] (n : ℕ)

abbrev Vec := Fin n → K
/-- Scalar order: V, R, x, y, z. -/
abbrev Ambient := (Fin 3 → Vec K n) × (Fin 5 → K)
/-- Scalar upload order in the positive orientation: z-V, R, y, x. -/
abbrev Upload := (Fin 3 → Vec K n) × (Fin 4 → K)

/-- Coefficient-space map for the positive cycle's listed uploads. -/
def relayMap : Upload K n →ₗ[K] Ambient K n where
  toFun p := (p.1, ![-p.2 0, p.2 1, p.2 3, p.2 2, p.2 0])
  map_add' := by
    intro p q
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp [add_comm]
  map_smul' := by
    intro c p
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp

/-- Hyperplane functional xi_V + xi_z. -/
def relayForm : Ambient K n →ₗ[K] K where
  toFun p := p.2 0 + p.2 4
  map_add' := by intro p q; simp; ring
  map_smul' := by intro c p; simp; ring

theorem relayMap_injective : Function.Injective (relayMap K n) := by
  intro p q h
  apply Prod.ext
  · exact congrArg (fun z : Ambient K n => z.1) h
  · funext i
    have hs := congrArg Prod.snd h
    fin_cases i
    · exact congrFun hs 4
    · exact congrFun hs 1
    · exact congrFun hs 3
    · exact congrFun hs 2

/-- The listed coefficient rows span exactly the announced hyperplane. -/
theorem relay_range_eq_kernel : LinearMap.range (relayMap K n) =
    LinearMap.ker (relayForm K n) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simp [relayMap, relayForm, LinearMap.mem_ker]
  · intro hp
    have hp' : p.2 0 + p.2 4 = 0 := hp
    refine ⟨(p.1, ![p.2 4, p.2 1, p.2 3, p.2 2]), ?_⟩
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp [relayMap]
      linear_combination -hp'

/-- Exactly 3n+4 independent scalar uploads, for every n and every field. -/
theorem relay_finrank : Module.finrank K (LinearMap.range (relayMap K n)) =
    3 * n + 4 := by
  rw [LinearMap.finrank_range_of_inj (relayMap_injective K n)]
  simp [Upload, Vec, Module.finrank_prod, Module.finrank_pi, Module.finrank_pi_fintype]

/-- Coefficient embeddings for each user's private block and two scalar observations. -/
def sideMap (i : Fin 3) : (Vec K n × K × K) →ₗ[K] Ambient K n where
  toFun o := (fun j => if j = i then o.1 else 0,
    ![![o.2.1, 0, 0, 0, o.2.2], ![0, o.2.1, 0, o.2.2, 0],
      ![-o.2.1, o.2.1, o.2.2, 0, 0]] i)
  map_add' := by
    intro p q
    apply Prod.ext
    · funext j
      by_cases hj : j = i <;> simp [hj]
    · funext j
      fin_cases i <;> fin_cases j <;> simp
      all_goals ring
  map_smul' := by
    intro c p
    apply Prod.ext
    · funext j
      by_cases hj : j = i <;> simp [hj]
    · funext j
      fin_cases i <;> fin_cases j <;> simp

def side (i : Fin 3) : Submodule K (Ambient K n) := LinearMap.range (sideMap K n i)

def localPart₁ (p : Upload K n) : Ambient K n :=
  sideMap K n 0 (p.1 0, -p.2 0, p.2 0)
def localPart₂ (p : Upload K n) : Ambient K n :=
  sideMap K n 1 (p.1 1, p.2 1, p.2 2)
def localPart₃ (p : Upload K n) : Ambient K n :=
  sideMap K n 2 (p.1 2, 0, p.2 3)

theorem relay_decomposition (p : Upload K n) :
    relayMap K n p = localPart₁ K n p + localPart₂ K n p + localPart₃ K n p := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [relayMap, localPart₁, localPart₂, localPart₃, sideMap]
  · funext i
    fin_cases i <;> simp [relayMap, localPart₁, localPart₂, localPart₃, sideMap]

/-- Local generation in exactly the subspace form used by the manuscript. -/
theorem relay_locally_generated : LinearMap.range (relayMap K n) =
    ⨆ i : Fin 3, LinearMap.range (relayMap K n) ⊓ side K n i := by
  apply le_antisymm
  · rintro z ⟨p, rfl⟩
    rw [relay_decomposition K n p]
    have h₁ : localPart₁ K n p ∈ LinearMap.range (relayMap K n) ⊓ side K n 0 := by
      constructor
      · rw [relay_range_eq_kernel]
        simp [localPart₁, sideMap, relayForm, LinearMap.mem_ker]
      · exact ⟨(p.1 0, -p.2 0, p.2 0), rfl⟩
    have h₂ : localPart₂ K n p ∈ LinearMap.range (relayMap K n) ⊓ side K n 1 := by
      constructor
      · rw [relay_range_eq_kernel]
        simp [localPart₂, sideMap, relayForm, LinearMap.mem_ker]
      · exact ⟨(p.1 1, p.2 1, p.2 2), rfl⟩
    have h₃ : localPart₃ K n p ∈ LinearMap.range (relayMap K n) ⊓ side K n 2 := by
      constructor
      · rw [relay_range_eq_kernel]
        simp [localPart₃, sideMap, relayForm, LinearMap.mem_ker]
      · exact ⟨(p.1 2, 0, p.2 3), rfl⟩
    exact Submodule.add_mem _ (Submodule.add_mem _
      ((le_iSup (fun i : Fin 3 => LinearMap.range (relayMap K n) ⊓ side K n i) 0) h₁)
      ((le_iSup (fun i : Fin 3 => LinearMap.range (relayMap K n) ⊓ side K n i) 1) h₂))
      ((le_iSup (fun i : Fin 3 => LinearMap.range (relayMap K n) ⊓ side K n i) 2) h₃)
  · exact iSup_le fun _ => inf_le_left

theorem side_spanning : (⨆ i : Fin 3, side K n i) = ⊤ := by
  apply top_unique
  intro p _
  let a := sideMap K n 0 (p.1 0, p.2 0, p.2 4)
  let b := sideMap K n 1 (p.1 1, p.2 1, p.2 3)
  let c := sideMap K n 2 (p.1 2, 0, p.2 2)
  have ha : a ∈ side K n 0 := ⟨_, rfl⟩
  have hb : b ∈ side K n 1 := ⟨_, rfl⟩
  have hc : c ∈ side K n 2 := ⟨_, rfl⟩
  have heq : p = a + b + c := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [a, b, c, sideMap]
    · funext i
      fin_cases i <;> simp [a, b, c, sideMap]
  rw [heq]
  exact Submodule.add_mem _ (Submodule.add_mem _
    ((le_iSup (side K n) 0) ha) ((le_iSup (side K n) 1) hb))
    ((le_iSup (side K n) 2) hc)

variable (Acoeff : Vec K n →ₗ[K] Vec K n) (Hcoeff : Vec K n →ₗ[K] K)

/-- Coefficient embedding of the resonant vector demand and positive-cycle scalar demand. -/
def demandMap (i : Fin 3) : (Vec K n × K) →ₗ[K] Ambient K n where
  toFun o := (![![0, o.1, o.1], ![o.1, 0, o.1], ![o.1, Acoeff o.1, 0]] i,
    ![![0, 0, 0, o.2, 0], ![0, 0, o.2, 0, 0], ![Hcoeff o.1, 0, 0, 0, o.2]] i)
  map_add' := by
    intro p q
    apply Prod.ext
    · funext j
      fin_cases i <;> fin_cases j <;> simp
    · funext j
      fin_cases i <;> fin_cases j <;> simp
  map_smul' := by
    intro c p
    apply Prod.ext
    · funext j
      fin_cases i <;> fin_cases j <;> simp
    · funext j
      fin_cases i <;> fin_cases j <;> simp

def signal (i : Fin 3) : Submodule K (Ambient K n) :=
  side K n i ⊔ LinearMap.range (demandMap K n Acoeff Hcoeff i)

/-- Coefficient-space feasibility of the positive-cycle construction. -/
theorem relay_feasible (i : Fin 3) : signal K n Acoeff Hcoeff i ≤
    side K n i ⊔ LinearMap.range (relayMap K n) := by
  apply sup_le le_sup_left
  rintro v ⟨o, rfl⟩
  fin_cases i
  · apply Submodule.mem_sup_right
    rw [relay_range_eq_kernel]
    simp [demandMap, relayForm, LinearMap.mem_ker]
  · apply Submodule.mem_sup_right
    rw [relay_range_eq_kernel]
    simp [demandMap, relayForm, LinearMap.mem_ker]
  · let a := sideMap K n 2 (0, -(Hcoeff o.1 + o.2), 0)
    have ha : a ∈ side K n 2 := ⟨_, rfl⟩
    have hp : demandMap K n Acoeff Hcoeff 2 o - a ∈ LinearMap.range (relayMap K n) := by
      rw [relay_range_eq_kernel]
      simp [a, sideMap, demandMap, relayForm, LinearMap.mem_ker]
    exact Submodule.mem_sup.mpr ⟨a, ha, _, hp, by simp⟩

/-- The construction instantiated in the repository's common task model. -/
def task : UploadBroadcast.Task K (Ambient K n) where
  A := side K n
  U := signal K n Acoeff Hcoeff
  side_le_signal := fun _ => le_sup_left
  feasible := by
    intro i
    rw [side_spanning]
    exact le_top

theorem task_relay_feasible :
    (task K n Acoeff Hcoeff).RelayFeasible (LinearMap.range (relayMap K n)) :=
  relay_feasible K n Acoeff Hcoeff

theorem task_relay_locally_generated :
    (task K n Acoeff Hcoeff).LocallyGenerated (LinearMap.range (relayMap K n)) :=
  relay_locally_generated K n

/-- User observations in the positive or reversed cycle. -/
def observation₁ (s : Ambient K n) : Vec K n × K × K := (s.1 0, s.2 0, s.2 4)
def observation₂ (s : Ambient K n) : Vec K n × K × K := (s.1 1, s.2 1, s.2 3)
def observation₃ (s : Ambient K n) : Vec K n × K × K :=
  (s.1 2, s.2 1 - s.2 0, s.2 2)

/-- The first encoder uses only user 1's own observation. -/
def encode₁ (o : Vec K n × K × K) : Vec K n × K := (o.1, o.2.2 - o.2.1)
def encode₂ (o : Vec K n × K × K) : Vec K n × K × K := o
def encode₃ (o : Vec K n × K × K) : Vec K n × K := (o.1, o.2.2)

def collected (s : Ambient K n) : Upload K n :=
  let m₁ := encode₁ K n (observation₁ K n s)
  let m₂ := encode₂ K n (observation₂ K n s)
  let m₃ := encode₃ K n (observation₃ K n s)
  (![m₁.1, m₂.1, m₃.1], ![m₁.2, m₂.2.1, m₂.2.2, m₃.2])

variable (A : Vec K n →ₗ[K] Vec K n) (h : Vec K n)

def demand₁ (s : Ambient K n) : Vec K n × K := (s.1 1 + s.1 2, s.2 3)
def demand₂ (s : Ambient K n) : Vec K n × K := (s.1 0 + s.1 2, s.2 2)
def demand₃ (s : Ambient K n) : Vec K n × K :=
  (s.1 0 + A (s.1 1) + s.2 0 • h, s.2 4)

def decode₁ (m : Upload K n) : Vec K n × K := (m.1 1 + m.1 2, m.2 2)
def decode₂ (m : Upload K n) : Vec K n × K := (m.1 0 + m.1 2, m.2 3)
def decode₃ (m : Upload K n) (o : Vec K n × K × K) : Vec K n × K :=
  let v := m.2 1 - o.2.1
  (m.1 0 + A (m.1 1) + v • h, m.2 0 + v)

/-- Positive-cycle decoding, uniformly in the vector length and defining field. -/
theorem decode₁_correct (s : Ambient K n) :
    decode₁ K n (collected K n s) = demand₁ K n s := by
  rfl

theorem decode₂_correct (s : Ambient K n) :
    decode₂ K n (collected K n s) = demand₂ K n s := by
  rfl

theorem decode₃_correct (s : Ambient K n) :
    decode₃ K n A h (collected K n s) (observation₃ K n s) =
      demand₃ K n A h s := by
  simp [decode₃, collected, observation₁, observation₂, observation₃,
    encode₁, encode₂, encode₃, demand₃]

/-- Reverse-cycle coefficient upload order: V, z, y-R, x. -/
def reverseRelayMap : Upload K n →ₗ[K] Ambient K n where
  toFun p := (p.1, ![p.2 0, -p.2 2, p.2 3, p.2 2, p.2 1])
  map_add' := by
    intro p q
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp [add_comm]
  map_smul' := by
    intro c p
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp

def reverseRelayForm : Ambient K n →ₗ[K] K where
  toFun p := p.2 1 + p.2 3
  map_add' := by intro p q; simp; ring
  map_smul' := by intro c p; simp; ring

theorem reverseRelayMap_injective : Function.Injective (reverseRelayMap K n) := by
  intro p q h
  apply Prod.ext
  · exact congrArg (fun z : Ambient K n => z.1) h
  · funext i
    have hs := congrArg Prod.snd h
    fin_cases i
    · exact congrFun hs 0
    · exact congrFun hs 4
    · exact congrFun hs 3
    · exact congrFun hs 2

theorem reverse_relay_range_eq_kernel : LinearMap.range (reverseRelayMap K n) =
    LinearMap.ker (reverseRelayForm K n) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simp [reverseRelayMap, reverseRelayForm, LinearMap.mem_ker]
  · intro hp
    have hp' : p.2 1 + p.2 3 = 0 := hp
    refine ⟨(p.1, ![p.2 0, p.2 4, p.2 3, p.2 2]), ?_⟩
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp [reverseRelayMap]
      linear_combination -hp'

theorem reverse_relay_finrank : Module.finrank K (LinearMap.range (reverseRelayMap K n)) =
    3 * n + 4 := by
  rw [LinearMap.finrank_range_of_inj (reverseRelayMap_injective K n)]
  simp [Upload, Vec, Module.finrank_prod, Module.finrank_pi, Module.finrank_pi_fintype]

def reverseLocalPart₁ (p : Upload K n) : Ambient K n :=
  sideMap K n 0 (p.1 0, p.2 0, p.2 1)
def reverseLocalPart₂ (p : Upload K n) : Ambient K n :=
  sideMap K n 1 (p.1 1, -p.2 2, p.2 2)
def reverseLocalPart₃ (p : Upload K n) : Ambient K n :=
  sideMap K n 2 (p.1 2, 0, p.2 3)

theorem reverse_relay_decomposition (p : Upload K n) :
    reverseRelayMap K n p =
      reverseLocalPart₁ K n p + reverseLocalPart₂ K n p + reverseLocalPart₃ K n p := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [reverseRelayMap, reverseLocalPart₁, reverseLocalPart₂,
      reverseLocalPart₃, sideMap]
  · funext i
    fin_cases i <;> simp [reverseRelayMap, reverseLocalPart₁, reverseLocalPart₂,
      reverseLocalPart₃, sideMap]

theorem reverse_relay_locally_generated : LinearMap.range (reverseRelayMap K n) =
    ⨆ i : Fin 3, LinearMap.range (reverseRelayMap K n) ⊓ side K n i := by
  apply le_antisymm
  · rintro z ⟨p, rfl⟩
    rw [reverse_relay_decomposition K n p]
    have h₁ : reverseLocalPart₁ K n p ∈ LinearMap.range (reverseRelayMap K n) ⊓ side K n 0 := by
      constructor
      · rw [reverse_relay_range_eq_kernel]
        simp [reverseLocalPart₁, sideMap, reverseRelayForm, LinearMap.mem_ker]
      · exact ⟨(p.1 0, p.2 0, p.2 1), rfl⟩
    have h₂ : reverseLocalPart₂ K n p ∈ LinearMap.range (reverseRelayMap K n) ⊓ side K n 1 := by
      constructor
      · rw [reverse_relay_range_eq_kernel]
        simp [reverseLocalPart₂, sideMap, reverseRelayForm, LinearMap.mem_ker]
      · exact ⟨(p.1 1, -p.2 2, p.2 2), rfl⟩
    have h₃ : reverseLocalPart₃ K n p ∈ LinearMap.range (reverseRelayMap K n) ⊓ side K n 2 := by
      constructor
      · rw [reverse_relay_range_eq_kernel]
        simp [reverseLocalPart₃, sideMap, reverseRelayForm, LinearMap.mem_ker]
      · exact ⟨(p.1 2, 0, p.2 3), rfl⟩
    exact Submodule.add_mem _ (Submodule.add_mem _
      ((le_iSup (fun i : Fin 3 => LinearMap.range (reverseRelayMap K n) ⊓ side K n i) 0) h₁)
      ((le_iSup (fun i : Fin 3 => LinearMap.range (reverseRelayMap K n) ⊓ side K n i) 1) h₂))
      ((le_iSup (fun i : Fin 3 => LinearMap.range (reverseRelayMap K n) ⊓ side K n i) 2) h₃)
  · exact iSup_le fun _ => inf_le_left

def reverseDemandMap (i : Fin 3) : (Vec K n × K) →ₗ[K] Ambient K n where
  toFun o := (![![0, o.1, o.1], ![o.1, 0, o.1], ![o.1, Acoeff o.1, 0]] i,
    ![![0, 0, o.2, 0, 0], ![0, 0, 0, 0, o.2], ![Hcoeff o.1, 0, 0, o.2, 0]] i)
  map_add' := by
    intro p q
    apply Prod.ext
    · funext j
      fin_cases i <;> fin_cases j <;> simp
    · funext j
      fin_cases i <;> fin_cases j <;> simp
  map_smul' := by
    intro c p
    apply Prod.ext
    · funext j
      fin_cases i <;> fin_cases j <;> simp
    · funext j
      fin_cases i <;> fin_cases j <;> simp

def reverseSignal (i : Fin 3) : Submodule K (Ambient K n) :=
  side K n i ⊔ LinearMap.range (reverseDemandMap K n Acoeff Hcoeff i)

theorem reverse_relay_feasible (i : Fin 3) : reverseSignal K n Acoeff Hcoeff i ≤
    side K n i ⊔ LinearMap.range (reverseRelayMap K n) := by
  apply sup_le le_sup_left
  rintro v ⟨o, rfl⟩
  fin_cases i
  · apply Submodule.mem_sup_right
    rw [reverse_relay_range_eq_kernel]
    simp [reverseDemandMap, reverseRelayForm, LinearMap.mem_ker]
  · apply Submodule.mem_sup_right
    rw [reverse_relay_range_eq_kernel]
    simp [reverseDemandMap, reverseRelayForm, LinearMap.mem_ker]
  · let a := sideMap K n 2 (0, o.2, 0)
    have ha : a ∈ side K n 2 := ⟨_, rfl⟩
    have hp : reverseDemandMap K n Acoeff Hcoeff 2 o - a ∈
        LinearMap.range (reverseRelayMap K n) := by
      rw [reverse_relay_range_eq_kernel]
      simp [a, sideMap, reverseDemandMap, reverseRelayForm, LinearMap.mem_ker]
    exact Submodule.mem_sup.mpr ⟨a, ha, _, hp, by simp⟩

def reverseTask : UploadBroadcast.Task K (Ambient K n) where
  A := side K n
  U := reverseSignal K n Acoeff Hcoeff
  side_le_signal := fun _ => le_sup_left
  feasible := by
    intro i
    rw [side_spanning]
    exact le_top

theorem reverse_task_relay_feasible :
    (reverseTask K n Acoeff Hcoeff).RelayFeasible (LinearMap.range (reverseRelayMap K n)) :=
  reverse_relay_feasible K n Acoeff Hcoeff

theorem reverse_task_relay_locally_generated :
    (reverseTask K n Acoeff Hcoeff).LocallyGenerated (LinearMap.range (reverseRelayMap K n)) :=
  reverse_relay_locally_generated K n

/-- Reverse-cycle local encoder 2, which mixes only its own y and R. -/
def reverseEncode₂ (o : Vec K n × K × K) : Vec K n × K := (o.1, o.2.2 - o.2.1)

def reverseCollected (s : Ambient K n) : Upload K n :=
  let m₁ := observation₁ K n s
  let m₂ := reverseEncode₂ K n (observation₂ K n s)
  let m₃ := encode₃ K n (observation₃ K n s)
  (![m₁.1, m₂.1, m₃.1], ![m₁.2.1, m₁.2.2, m₂.2, m₃.2])

def reverseDemand₁ (s : Ambient K n) : Vec K n × K := (s.1 1 + s.1 2, s.2 2)
def reverseDemand₂ (s : Ambient K n) : Vec K n × K := (s.1 0 + s.1 2, s.2 4)
def reverseDemand₃ (s : Ambient K n) : Vec K n × K :=
  (s.1 0 + A (s.1 1) + s.2 0 • h, s.2 3)

def reverseDecode₁ (m : Upload K n) : Vec K n × K := (m.1 1 + m.1 2, m.2 3)
def reverseDecode₂ (m : Upload K n) : Vec K n × K := (m.1 0 + m.1 2, m.2 1)
def reverseDecode₃ (m : Upload K n) (o : Vec K n × K × K) : Vec K n × K :=
  (m.1 0 + A (m.1 1) + m.2 0 • h, m.2 2 + (m.2 0 + o.2.1))

theorem reverseDecode₁_correct (s : Ambient K n) :
    reverseDecode₁ K n (reverseCollected K n s) = reverseDemand₁ K n s := by
  rfl

theorem reverseDecode₂_correct (s : Ambient K n) :
    reverseDecode₂ K n (reverseCollected K n s) = reverseDemand₂ K n s := by
  rfl

theorem reverseDecode₃_correct (s : Ambient K n) :
    reverseDecode₃ K n A h (reverseCollected K n s) (observation₃ K n s) =
      reverseDemand₃ K n A h s := by
  simp [reverseDecode₃, reverseCollected, observation₁, observation₂, observation₃,
    reverseEncode₂, encode₃, reverseDemand₃]

end UploadBroadcast.CycleRepair
