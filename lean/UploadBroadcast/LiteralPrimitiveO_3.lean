import UploadBroadcast.LiteralMatrixCertificates
/-! Literal base flags and relay forms, frozen source tables primitive-flags
and primitive-relays. Generated exact integer identities; all ranks and spaces
are certified uniformly over an arbitrary field, including characteristic two. -/
namespace UploadBroadcast.LiteralPrimitiveTables
open Matrix Module LiteralMatrixCertificates NonzeroDefectProfile
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

namespace O_3
def relayForms : Matrix (Fin 1) (Fin 3) ℤ := ![![1, 0, (-1)]]
abbrev relay : Submodule K (Fin 3 → K) := kernel relayForms
lemma rank_441 : (castMatrix (relayForms) : Matrix (Fin 1) (Fin 3) K).rank = 1 := by
  exact rank_int_certificate (relayForms)
    (![![1]]) (![![1, 0, (-1)]]) (![![1]]) (![![1], ![0], ![0]]) (by decide) (by decide)

lemma dim_relay : finrank K ↥(relay (K := K)) = 2 := by
  have h := kernel_finrank (K := K) (relayForms) (rank_441 (K := K))
  exact h

def relayBasis : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 1], ![1, 0], ![0, 1]]
lemma rank_442 : (castMatrix (relayBasis) : Matrix (Fin 3) (Fin 2) K).rank = 2 := by
  exact rank_int_certificate (relayBasis)
    (![![0, 1], ![1, 0], ![0, 1]]) (![![1, 0], ![0, 1]]) (![![0, 1, 0], ![1, 0, 0]]) (![![1, 0], ![0, 1]]) (by decide) (by decide)

lemma relay_columns : columns (K := K) relayBasis = relay := columns_eq_kernel _ _ (by decide) (rank_442 (K := K)) (rank_441 (K := K)) (by decide)

def side0Columns : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![0], ![1]]
def side0Constraints : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 0, 0], ![0, 1, 0]]
lemma rank_443 : (castMatrix (side0Columns) : Matrix (Fin 3) (Fin 1) K).rank = 1 := by
  exact rank_int_certificate (side0Columns)
    (![![0], ![0], ![1]]) (![![1]]) (![![0, 0, 1]]) (![![1]]) (by decide) (by decide)

lemma rank_444 : (castMatrix (side0Constraints) : Matrix (Fin 2) (Fin 3) K).rank = 2 := by
  exact rank_int_certificate (side0Constraints)
    (![![1, 0], ![0, 1]]) (![![1, 0, 0], ![0, 1, 0]]) (![![1, 0], ![0, 1]]) (![![1, 0], ![0, 1], ![0, 0]]) (by decide) (by decide)

lemma side0_literal : columns (K := K) side0Columns = kernel side0Constraints :=
  columns_eq_kernel _ _ (by decide) (rank_443 (K := K)) (rank_444 (K := K)) (by decide)

def side1Columns : Matrix (Fin 3) (Fin 1) ℤ := ![![1], ![0], ![0]]
def side1Constraints : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 1, 0], ![0, 0, 1]]
lemma rank_445 : (castMatrix (side1Columns) : Matrix (Fin 3) (Fin 1) K).rank = 1 := by
  exact rank_int_certificate (side1Columns)
    (![![1], ![0], ![0]]) (![![1]]) (![![1, 0, 0]]) (![![1]]) (by decide) (by decide)

lemma rank_446 : (castMatrix (side1Constraints) : Matrix (Fin 2) (Fin 3) K).rank = 2 := by
  exact rank_int_certificate (side1Constraints)
    (![![1, 0], ![0, 1]]) (![![0, 1, 0], ![0, 0, 1]]) (![![1, 0], ![0, 1]]) (![![0, 0], ![1, 0], ![0, 1]]) (by decide) (by decide)

lemma side1_literal : columns (K := K) side1Columns = kernel side1Constraints :=
  columns_eq_kernel _ _ (by decide) (rank_445 (K := K)) (rank_446 (K := K)) (by decide)

def side2Columns : Matrix (Fin 3) (Fin 2) ℤ := ![![1, 0], ![0, 1], ![1, 0]]
def side2Constraints : Matrix (Fin 1) (Fin 3) ℤ := ![![(-1), 0, 1]]
lemma rank_447 : (castMatrix (side2Columns) : Matrix (Fin 3) (Fin 2) K).rank = 2 := by
  exact rank_int_certificate (side2Columns)
    (![![1, 0], ![0, 1], ![1, 0]]) (![![1, 0], ![0, 1]]) (![![1, 0, 0], ![0, 1, 0]]) (![![1, 0], ![0, 1]]) (by decide) (by decide)

lemma rank_448 : (castMatrix (side2Constraints) : Matrix (Fin 1) (Fin 3) K).rank = 1 := by
  exact rank_int_certificate (side2Constraints)
    (![![(-1)]]) (![![1, 0, (-1)]]) (![![(-1)]]) (![![1], ![0], ![0]]) (by decide) (by decide)

lemma side2_literal : columns (K := K) side2Columns = kernel side2Constraints :=
  columns_eq_kernel _ _ (by decide) (rank_447 (K := K)) (rank_448 (K := K)) (by decide)

def signal0Columns : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![0, 1], ![1, 0]]
def signal0Constraints : Matrix (Fin 1) (Fin 3) ℤ := ![![1, 0, 0]]
lemma rank_449 : (castMatrix (signal0Columns) : Matrix (Fin 3) (Fin 2) K).rank = 2 := by
  exact rank_int_certificate (signal0Columns)
    (![![0, 0], ![0, 1], ![1, 0]]) (![![1, 0], ![0, 1]]) (![![0, 0, 1], ![0, 1, 0]]) (![![1, 0], ![0, 1]]) (by decide) (by decide)

lemma rank_450 : (castMatrix (signal0Constraints) : Matrix (Fin 1) (Fin 3) K).rank = 1 := by
  exact rank_int_certificate (signal0Constraints)
    (![![1]]) (![![1, 0, 0]]) (![![1]]) (![![1], ![0], ![0]]) (by decide) (by decide)

lemma signal0_literal : columns (K := K) signal0Columns = kernel signal0Constraints :=
  columns_eq_kernel _ _ (by decide) (rank_449 (K := K)) (rank_450 (K := K)) (by decide)

def signal1Columns : Matrix (Fin 3) (Fin 2) ℤ := ![![1, 0], ![0, 1], ![0, 1]]
def signal1Constraints : Matrix (Fin 1) (Fin 3) ℤ := ![![0, (-1), 1]]
lemma rank_451 : (castMatrix (signal1Columns) : Matrix (Fin 3) (Fin 2) K).rank = 2 := by
  exact rank_int_certificate (signal1Columns)
    (![![1, 0], ![0, 1], ![0, 1]]) (![![1, 0], ![0, 1]]) (![![1, 0, 0], ![0, 1, 0]]) (![![1, 0], ![0, 1]]) (by decide) (by decide)

lemma rank_452 : (castMatrix (signal1Constraints) : Matrix (Fin 1) (Fin 3) K).rank = 1 := by
  exact rank_int_certificate (signal1Constraints)
    (![![(-1)]]) (![![0, 1, (-1)]]) (![![(-1)]]) (![![0], ![1], ![0]]) (by decide) (by decide)

lemma signal1_literal : columns (K := K) signal1Columns = kernel signal1Constraints :=
  columns_eq_kernel _ _ (by decide) (rank_451 (K := K)) (rank_452 (K := K)) (by decide)

def signal2Columns : Matrix (Fin 3) (Fin 2) ℤ := ![![1, 0], ![0, 1], ![1, 0]]
def signal2Constraints : Matrix (Fin 1) (Fin 3) ℤ := ![![(-1), 0, 1]]
lemma rank_453 : (castMatrix (signal2Columns) : Matrix (Fin 3) (Fin 2) K).rank = 2 := by
  exact rank_int_certificate (signal2Columns)
    (![![1, 0], ![0, 1], ![1, 0]]) (![![1, 0], ![0, 1]]) (![![1, 0, 0], ![0, 1, 0]]) (![![1, 0], ![0, 1]]) (by decide) (by decide)

lemma rank_454 : (castMatrix (signal2Constraints) : Matrix (Fin 1) (Fin 3) K).rank = 1 := by
  exact rank_int_certificate (signal2Constraints)
    (![![(-1)]]) (![![1, 0, (-1)]]) (![![(-1)]]) (![![1], ![0], ![0]]) (by decide) (by decide)

lemma signal2_literal : columns (K := K) signal2Columns = kernel signal2Constraints :=
  columns_eq_kernel _ _ (by decide) (rank_453 (K := K)) (rank_454 (K := K)) (by decide)

def demand0Columns : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![1], ![0]]
lemma signal0_from_demands : signal0Columns = joinColumns side0Columns demand0Columns := by decide

def demand1Columns : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![1], ![1]]
lemma signal1_from_demands : signal1Columns = joinColumns side1Columns demand1Columns := by decide

def demand2Columns : Matrix (Fin 3) (Fin 0) ℤ := ![![], ![], ![]]
lemma signal2_from_demands : signal2Columns = joinColumns side2Columns demand2Columns := by decide

def side : Three → Submodule K (Fin 3 → K) := ![kernel side0Constraints, kernel side1Constraints, kernel side2Constraints]
def signal : Three → Submodule K (Fin 3 → K) := ![kernel signal0Constraints, kernel signal1Constraints, kernel signal2Constraints]

lemma side_le_signal (i : Three) : side (K := K) i ≤ signal i := by
  fin_cases i
  · change kernel side0Constraints ≤ kernel signal0Constraints
    rw [← side0_literal, ← signal0_literal]
    exact columns_le_columns _ _ (![![1], ![0]]) (by decide)
  · change kernel side1Constraints ≤ kernel signal1Constraints
    rw [← side1_literal, ← signal1_literal]
    exact columns_le_columns _ _ (![![1], ![0]]) (by decide)
  · change kernel side2Constraints ≤ kernel signal2Constraints
    rw [← side2_literal, ← signal2_literal]
    exact columns_le_columns _ _ (![![1, 0], ![0, 1]]) (by decide)
lemma rank_455 : (castMatrix (joinColumns (joinColumns side0Columns side1Columns) side2Columns) : Matrix (Fin 3) (Fin 4) K).rank = 3 := by
  exact rank_int_certificate (joinColumns (joinColumns side0Columns side1Columns) side2Columns)
    (![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]]) (![![1, 0, 1, 0], ![0, 1, 1, 0], ![0, 0, 0, 1]]) (![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma side_spanning : (⨆ i, side (K := K) i) = ⊤ := by
  have h := columns_eq_top (K := K) (joinColumns (joinColumns side0Columns side1Columns) side2Columns) (rank_455 (K := K))
  simpa only [columns_join, side0_literal, side1_literal, side2_literal,
    Profile.three_iSup, side, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, sup_assoc] using h

def task : Task K (Fin 3 → K) where
  A := side
  U := signal
  side_le_signal := side_le_signal
  feasible i := by rw [side_spanning]; exact le_top

def inducedSide0Columns : Matrix (Fin 3) (Fin 0) ℤ := ![![], ![], ![]]
lemma rank_456 : (castMatrix (inducedSide0Columns) : Matrix (Fin 3) (Fin 0) K).rank = 0 := by
  exact rank_int_certificate (inducedSide0Columns)
    (![![], ![], ![]]) ((fun i => Fin.elim0 i)) ((fun i => Fin.elim0 i)) ((fun i => Fin.elim0 i)) (by decide) (by decide)

lemma rank_457 : (castMatrix (stack relayForms side0Constraints) : Matrix (Fin 3) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack relayForms side0Constraints)
    (![![1, 0, (-1)], ![1, 0, 0], ![0, 1, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![0, 1, 0], ![0, 0, 1], ![(-1), 1, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma inducedSide0_literal : columns (K := K) inducedSide0Columns = relay ⊓ side 0 := by
  have h := columns_eq_kernel (K := K) inducedSide0Columns (stack relayForms side0Constraints) (by decide) (rank_456 (K := K)) (rank_457 (K := K)) (by decide)
  simpa only [kernel_stack, side, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using h

def inducedSide1Columns : Matrix (Fin 3) (Fin 0) ℤ := ![![], ![], ![]]
lemma rank_458 : (castMatrix (inducedSide1Columns) : Matrix (Fin 3) (Fin 0) K).rank = 0 := by
  exact rank_int_certificate (inducedSide1Columns)
    (![![], ![], ![]]) ((fun i => Fin.elim0 i)) ((fun i => Fin.elim0 i)) ((fun i => Fin.elim0 i)) (by decide) (by decide)

lemma rank_459 : (castMatrix (stack relayForms side1Constraints) : Matrix (Fin 3) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack relayForms side1Constraints)
    (![![1, 0, (-1)], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 1], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma inducedSide1_literal : columns (K := K) inducedSide1Columns = relay ⊓ side 1 := by
  have h := columns_eq_kernel (K := K) inducedSide1Columns (stack relayForms side1Constraints) (by decide) (rank_458 (K := K)) (rank_459 (K := K)) (by decide)
  simpa only [kernel_stack, side, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using h

def inducedSide2Columns : Matrix (Fin 3) (Fin 2) ℤ := ![![1, 0], ![0, 1], ![1, 0]]
lemma rank_460 : (castMatrix (inducedSide2Columns) : Matrix (Fin 3) (Fin 2) K).rank = 2 := by
  exact rank_int_certificate (inducedSide2Columns)
    (![![1, 0], ![0, 1], ![1, 0]]) (![![1, 0], ![0, 1]]) (![![1, 0, 0], ![0, 1, 0]]) (![![1, 0], ![0, 1]]) (by decide) (by decide)

lemma rank_461 : (castMatrix (stack relayForms side2Constraints) : Matrix (Fin 2) (Fin 3) K).rank = 1 := by
  exact rank_int_certificate (stack relayForms side2Constraints)
    (![![1], ![(-1)]]) (![![1, 0, (-1)]]) (![![1, 0]]) (![![1], ![0], ![0]]) (by decide) (by decide)

lemma inducedSide2_literal : columns (K := K) inducedSide2Columns = relay ⊓ side 2 := by
  have h := columns_eq_kernel (K := K) inducedSide2Columns (stack relayForms side2Constraints) (by decide) (rank_460 (K := K)) (rank_461 (K := K)) (by decide)
  simpa only [kernel_stack, side, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using h

lemma rank_462 : (castMatrix (joinColumns (joinColumns inducedSide0Columns inducedSide1Columns) inducedSide2Columns) : Matrix (Fin 3) (Fin 2) K).rank = 2 := by
  exact rank_int_certificate (joinColumns (joinColumns inducedSide0Columns inducedSide1Columns) inducedSide2Columns)
    (![![1, 0], ![0, 1], ![1, 0]]) (![![1, 0], ![0, 1]]) (![![1, 0, 0], ![0, 1, 0]]) (![![1, 0], ![0, 1]]) (by decide) (by decide)

lemma locally_generated : (task (K := K)).LocallyGenerated relay := by
  have h : columns (K := K) (joinColumns (joinColumns inducedSide0Columns inducedSide1Columns) inducedSide2Columns) = ⨆ i, relay ⊓ side i := by
    simp only [columns_join, inducedSide0_literal, inducedSide1_literal,
      inducedSide2_literal, Profile.three_iSup, sup_assoc]
  unfold Task.LocallyGenerated
  change relay = ⨆ i, relay ⊓ side i
  symm
  apply Submodule.eq_of_le_of_finrank_eq (iSup_le fun i => inf_le_left)
  rw [← h, columns_finrank, rank_462, dim_relay]

lemma relay_feasible : (task (K := K)).RelayFeasible relay := by
  intro i
  fin_cases i
  · change kernel signal0Constraints ≤ kernel side0Constraints ⊔ relay
    rw [← side0_literal, ← signal0_literal, ← relay_columns, ← columns_join]
    exact columns_le_columns _ _ (![![1, 0], ![0, 1], ![0, 0]]) (by decide)
  · change kernel signal1Constraints ≤ kernel side1Constraints ⊔ relay
    rw [← side1_literal, ← signal1_literal, ← relay_columns, ← columns_join]
    exact columns_le_columns _ _ (![![1, (-1)], ![0, 1], ![0, 1]]) (by decide)
  · change kernel signal2Constraints ≤ kernel side2Constraints ⊔ relay
    rw [← side2_literal, ← signal2_literal, ← relay_columns, ← columns_join]
    exact columns_le_columns _ _ (![![1, 0], ![0, 1], ![0, 0], ![0, 0]]) (by decide)
def inducedTask : Task K (Fin 3 → K) where
  A i := relay ⊓ side i
  U i := relay ⊓ signal i
  side_le_signal i := inf_le_inf_left _ (side_le_signal i)
  feasible i := by
    change relay ⊓ signal i ≤ ⨆ j, relay ⊓ side j
    have h : relay (K := K) = ⨆ j, relay ⊓ side j := locally_generated
    rw [← h]
    exact inf_le_left

lemma full_side0_dim : finrank K ↥(kernel (K := K) side0Constraints) = 1 := by
  have h := kernel_finrank (K := K) (side0Constraints) (rank_444 (K := K))
  exact h

lemma full_side1_dim : finrank K ↥(kernel (K := K) side1Constraints) = 1 := by
  have h := kernel_finrank (K := K) (side1Constraints) (rank_446 (K := K))
  exact h

lemma full_side2_dim : finrank K ↥(kernel (K := K) side2Constraints) = 2 := by
  have h := kernel_finrank (K := K) (side2Constraints) (rank_448 (K := K))
  exact h

lemma full_signal0_dim : finrank K ↥(kernel (K := K) signal0Constraints) = 2 := by
  have h := kernel_finrank (K := K) (signal0Constraints) (rank_450 (K := K))
  exact h

lemma full_signal1_dim : finrank K ↥(kernel (K := K) signal1Constraints) = 2 := by
  have h := kernel_finrank (K := K) (signal1Constraints) (rank_452 (K := K))
  exact h

lemma full_signal2_dim : finrank K ↥(kernel (K := K) signal2Constraints) = 2 := by
  have h := kernel_finrank (K := K) (signal2Constraints) (rank_454 (K := K))
  exact h

lemma rank_463 : (castMatrix (stack (signal0Constraints) (signal1Constraints)) : Matrix (Fin 2) (Fin 3) K).rank = 2 := by
  exact rank_int_certificate (stack (signal0Constraints) (signal1Constraints))
    (![![1, 0], ![0, (-1)]]) (![![1, 0, 0], ![0, 1, (-1)]]) (![![1, 0], ![0, (-1)]]) (![![1, 0], ![0, 1], ![0, 0]]) (by decide) (by decide)

lemma full_pair01_dim : finrank K ↥((kernel (K := K) signal0Constraints) ⊓ (kernel (K := K) signal1Constraints)) = 1 := by
  have h := kernel_finrank (K := K) (stack (signal0Constraints) (signal1Constraints)) (rank_463 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_464 : (castMatrix (stack (signal0Constraints) (signal2Constraints)) : Matrix (Fin 2) (Fin 3) K).rank = 2 := by
  exact rank_int_certificate (stack (signal0Constraints) (signal2Constraints))
    (![![1, 0], ![(-1), 1]]) (![![1, 0, 0], ![0, 0, 1]]) (![![1, 0], ![1, 1]]) (![![1, 0], ![0, 0], ![0, 1]]) (by decide) (by decide)

lemma full_pair02_dim : finrank K ↥((kernel (K := K) signal0Constraints) ⊓ (kernel (K := K) signal2Constraints)) = 1 := by
  have h := kernel_finrank (K := K) (stack (signal0Constraints) (signal2Constraints)) (rank_464 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_465 : (castMatrix (stack (signal1Constraints) (signal2Constraints)) : Matrix (Fin 2) (Fin 3) K).rank = 2 := by
  exact rank_int_certificate (stack (signal1Constraints) (signal2Constraints))
    (![![0, (-1)], ![(-1), 0]]) (![![1, 0, (-1)], ![0, 1, (-1)]]) (![![0, (-1)], ![(-1), 0]]) (![![1, 0], ![0, 1], ![0, 0]]) (by decide) (by decide)

lemma full_pair12_dim : finrank K ↥((kernel (K := K) signal1Constraints) ⊓ (kernel (K := K) signal2Constraints)) = 1 := by
  have h := kernel_finrank (K := K) (stack (signal1Constraints) (signal2Constraints)) (rank_465 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_466 : (castMatrix (stack (stack (signal0Constraints) (signal1Constraints)) (signal2Constraints)) : Matrix (Fin 3) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (stack (signal0Constraints) (signal1Constraints)) (signal2Constraints))
    (![![1, 0, 0], ![0, (-1), 1], ![(-1), 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 0], ![1, (-1), 1], ![1, 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma full_triple_dim : finrank K ↥(((kernel (K := K) signal0Constraints) ⊓ (kernel (K := K) signal1Constraints)) ⊓ (kernel (K := K) signal2Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (stack (signal0Constraints) (signal1Constraints)) (signal2Constraints)) (rank_466 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_467 : (castMatrix (stack (side1Constraints) (signal0Constraints)) : Matrix (Fin 3) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (side1Constraints) (signal0Constraints))
    (![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma full_sideSignal10_dim : finrank K ↥((kernel (K := K) side1Constraints) ⊓ (kernel (K := K) signal0Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (side1Constraints) (signal0Constraints)) (rank_467 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_468 : (castMatrix (stack (side2Constraints) (signal0Constraints)) : Matrix (Fin 2) (Fin 3) K).rank = 2 := by
  exact rank_int_certificate (stack (side2Constraints) (signal0Constraints))
    (![![(-1), 1], ![1, 0]]) (![![1, 0, 0], ![0, 0, 1]]) (![![0, 1], ![1, 1]]) (![![1, 0], ![0, 0], ![0, 1]]) (by decide) (by decide)

lemma full_sideSignal20_dim : finrank K ↥((kernel (K := K) side2Constraints) ⊓ (kernel (K := K) signal0Constraints)) = 1 := by
  have h := kernel_finrank (K := K) (stack (side2Constraints) (signal0Constraints)) (rank_468 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_469 : (castMatrix (stack (side0Constraints) (signal1Constraints)) : Matrix (Fin 3) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (side0Constraints) (signal1Constraints))
    (![![1, 0, 0], ![0, 1, 0], ![0, (-1), 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 1, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma full_sideSignal01_dim : finrank K ↥((kernel (K := K) side0Constraints) ⊓ (kernel (K := K) signal1Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (side0Constraints) (signal1Constraints)) (rank_469 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_470 : (castMatrix (stack (side2Constraints) (signal1Constraints)) : Matrix (Fin 2) (Fin 3) K).rank = 2 := by
  exact rank_int_certificate (stack (side2Constraints) (signal1Constraints))
    (![![(-1), 0], ![0, (-1)]]) (![![1, 0, (-1)], ![0, 1, (-1)]]) (![![(-1), 0], ![0, (-1)]]) (![![1, 0], ![0, 1], ![0, 0]]) (by decide) (by decide)

lemma full_sideSignal21_dim : finrank K ↥((kernel (K := K) side2Constraints) ⊓ (kernel (K := K) signal1Constraints)) = 1 := by
  have h := kernel_finrank (K := K) (stack (side2Constraints) (signal1Constraints)) (rank_470 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_471 : (castMatrix (stack (side0Constraints) (signal2Constraints)) : Matrix (Fin 3) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (side0Constraints) (signal2Constraints))
    (![![1, 0, 0], ![0, 1, 0], ![(-1), 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![1, 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma full_sideSignal02_dim : finrank K ↥((kernel (K := K) side0Constraints) ⊓ (kernel (K := K) signal2Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (side0Constraints) (signal2Constraints)) (rank_471 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_472 : (castMatrix (stack (side1Constraints) (signal2Constraints)) : Matrix (Fin 3) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (side1Constraints) (signal2Constraints))
    (![![0, 1, 0], ![0, 0, 1], ![(-1), 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![0, 1, (-1)], ![1, 0, 0], ![0, 1, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma full_sideSignal12_dim : finrank K ↥((kernel (K := K) side1Constraints) ⊓ (kernel (K := K) signal2Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (side1Constraints) (signal2Constraints)) (rank_472 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_473 : (castMatrix (stack (stack (stack (signal0Constraints) (signal1Constraints)) (signal2Constraints)) (side0Constraints)) : Matrix (Fin 5) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (stack (stack (signal0Constraints) (signal1Constraints)) (signal2Constraints)) (side0Constraints))
    (![![1, 0, 0], ![0, (-1), 1], ![(-1), 0, 1], ![1, 0, 0], ![0, 1, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 0, 0, 0], ![1, (-1), 1, 0, 0], ![1, 0, 1, 0, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma full_tripleSide0_dim : finrank K ↥((((kernel (K := K) signal0Constraints) ⊓ (kernel (K := K) signal1Constraints)) ⊓ (kernel (K := K) signal2Constraints)) ⊓ (kernel (K := K) side0Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (stack (stack (signal0Constraints) (signal1Constraints)) (signal2Constraints)) (side0Constraints)) (rank_473 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_474 : (castMatrix (stack (stack (stack (signal0Constraints) (signal1Constraints)) (signal2Constraints)) (side1Constraints)) : Matrix (Fin 5) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (stack (stack (signal0Constraints) (signal1Constraints)) (signal2Constraints)) (side1Constraints))
    (![![1, 0, 0], ![0, (-1), 1], ![(-1), 0, 1], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 0, 0, 0], ![1, (-1), 1, 0, 0], ![1, 0, 1, 0, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma full_tripleSide1_dim : finrank K ↥((((kernel (K := K) signal0Constraints) ⊓ (kernel (K := K) signal1Constraints)) ⊓ (kernel (K := K) signal2Constraints)) ⊓ (kernel (K := K) side1Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (stack (stack (signal0Constraints) (signal1Constraints)) (signal2Constraints)) (side1Constraints)) (rank_474 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_475 : (castMatrix (stack (stack (stack (signal0Constraints) (signal1Constraints)) (signal2Constraints)) (side2Constraints)) : Matrix (Fin 4) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (stack (stack (signal0Constraints) (signal1Constraints)) (signal2Constraints)) (side2Constraints))
    (![![1, 0, 0], ![0, (-1), 1], ![(-1), 0, 1], ![(-1), 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 0, 0], ![1, (-1), 1, 0], ![1, 0, 1, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma full_tripleSide2_dim : finrank K ↥((((kernel (K := K) signal0Constraints) ⊓ (kernel (K := K) signal1Constraints)) ⊓ (kernel (K := K) signal2Constraints)) ⊓ (kernel (K := K) side2Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (stack (stack (signal0Constraints) (signal1Constraints)) (signal2Constraints)) (side2Constraints)) (rank_475 (K := K))
  repeat rw [kernel_stack] at h
  exact h

theorem full_rankConditions : RankConditions (task (K := K)) ⊤
    ![1,1,2] ![2,2,2] := by
  apply rankConditions_in_ambient
  · intro i; exact le_top
  · intro i; fin_cases i
    · exact full_side0_dim
    · exact full_side1_dim
    · exact full_side2_dim
  · intro i; fin_cases i
    · exact full_signal0_dim
    · exact full_signal1_dim
    · exact full_signal2_dim
  · intro i j hij; fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change finrank K ↥((kernel (K := K) signal0Constraints) ⊓ (kernel (K := K) signal1Constraints)) + finrank K ↥(⊤ : Submodule K (Fin 3 → K)) = 4
      rw [full_pair01_dim]
      norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((kernel (K := K) signal0Constraints) ⊓ (kernel (K := K) signal2Constraints)) + finrank K ↥(⊤ : Submodule K (Fin 3 → K)) = 4
      rw [full_pair02_dim]
      norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((kernel (K := K) signal1Constraints) ⊓ (kernel (K := K) signal0Constraints)) + finrank K ↥(⊤ : Submodule K (Fin 3 → K)) = 4
      rw [inf_comm]
      rw [full_pair01_dim]
      norm_num [dim_relay, finrank_top, finrank_pi]
    · exact (hij rfl).elim
    · change finrank K ↥((kernel (K := K) signal1Constraints) ⊓ (kernel (K := K) signal2Constraints)) + finrank K ↥(⊤ : Submodule K (Fin 3 → K)) = 4
      rw [full_pair12_dim]
      norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((kernel (K := K) signal2Constraints) ⊓ (kernel (K := K) signal0Constraints)) + finrank K ↥(⊤ : Submodule K (Fin 3 → K)) = 4
      rw [inf_comm]
      rw [full_pair02_dim]
      norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((kernel (K := K) signal2Constraints) ⊓ (kernel (K := K) signal1Constraints)) + finrank K ↥(⊤ : Submodule K (Fin 3 → K)) = 4
      rw [inf_comm]
      rw [full_pair12_dim]
      norm_num [dim_relay, finrank_top, finrank_pi]
    · exact (hij rfl).elim
  · change finrank K ↥(((kernel (K := K) signal0Constraints) ⊓ (kernel (K := K) signal1Constraints)) ⊓ (kernel (K := K) signal2Constraints)) + 2 * finrank K ↥(⊤ : Submodule K (Fin 3 → K)) = 6
    rw [full_triple_dim]; norm_num [dim_relay, finrank_top, finrank_pi]
  · intro i j hij; fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change finrank K ↥((kernel (K := K) side1Constraints) ⊓ (kernel (K := K) signal0Constraints)) = 3 - finrank K ↥(⊤ : Submodule K (Fin 3 → K))
      rw [full_sideSignal10_dim]; norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((kernel (K := K) side2Constraints) ⊓ (kernel (K := K) signal0Constraints)) = 4 - finrank K ↥(⊤ : Submodule K (Fin 3 → K))
      rw [full_sideSignal20_dim]; norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((kernel (K := K) side0Constraints) ⊓ (kernel (K := K) signal1Constraints)) = 3 - finrank K ↥(⊤ : Submodule K (Fin 3 → K))
      rw [full_sideSignal01_dim]; norm_num [dim_relay, finrank_top, finrank_pi]
    · exact (hij rfl).elim
    · change finrank K ↥((kernel (K := K) side2Constraints) ⊓ (kernel (K := K) signal1Constraints)) = 4 - finrank K ↥(⊤ : Submodule K (Fin 3 → K))
      rw [full_sideSignal21_dim]; norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((kernel (K := K) side0Constraints) ⊓ (kernel (K := K) signal2Constraints)) = 3 - finrank K ↥(⊤ : Submodule K (Fin 3 → K))
      rw [full_sideSignal02_dim]; norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((kernel (K := K) side1Constraints) ⊓ (kernel (K := K) signal2Constraints)) = 3 - finrank K ↥(⊤ : Submodule K (Fin 3 → K))
      rw [full_sideSignal12_dim]; norm_num [dim_relay, finrank_top, finrank_pi]
    · exact (hij rfl).elim
  · intro i; fin_cases i
    · exact full_tripleSide0_dim
    · exact full_tripleSide1_dim
    · exact full_tripleSide2_dim

theorem full_first_profile (r : Fin 6) : Profile.entry (task (K := K)) (.inl r) = ![1,1,1,1,0,0] r := by
  change Profile.firstEntry _ (Profile.firstOrder r).1 (Profile.firstOrder r).2.1 (Profile.firstOrder r).2.2 = _
  rw [firstEntry_max _ _ _ _ full_rankConditions _ _ _ (by fin_cases r <;> decide) (by fin_cases r <;> decide) (by fin_cases r <;> decide)]
  fin_cases r <;> norm_num [Profile.firstOrder, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, dim_relay, finrank_top, finrank_pi]

theorem full_second_profile (i ell : Three) : 2 * Profile.entry (task (K := K)) (.inr (i,ell)) = 2 := by
  change 2 * Profile.secondEntry _ i (i+1) (i+2) ell = _
  rw [secondEntry_formula _ _ _ _ full_rankConditions _ _ _ _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, dim_relay, finrank_top, finrank_pi]
lemma induced_side0_dim : finrank K ↥(relay (K := K) ⊓ kernel side0Constraints) = 0 := by
  have h := kernel_finrank (K := K) (stack relayForms side0Constraints) (rank_457 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma induced_side1_dim : finrank K ↥(relay (K := K) ⊓ kernel side1Constraints) = 0 := by
  have h := kernel_finrank (K := K) (stack relayForms side1Constraints) (rank_459 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma induced_side2_dim : finrank K ↥(relay (K := K) ⊓ kernel side2Constraints) = 2 := by
  have h := kernel_finrank (K := K) (stack relayForms side2Constraints) (rank_461 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_476 : (castMatrix (stack relayForms signal0Constraints) : Matrix (Fin 2) (Fin 3) K).rank = 2 := by
  exact rank_int_certificate (stack relayForms signal0Constraints)
    (![![1, (-1)], ![1, 0]]) (![![1, 0, 0], ![0, 0, 1]]) (![![0, 1], ![(-1), 1]]) (![![1, 0], ![0, 0], ![0, 1]]) (by decide) (by decide)

lemma induced_signal0_dim : finrank K ↥(relay (K := K) ⊓ kernel signal0Constraints) = 1 := by
  have h := kernel_finrank (K := K) (stack relayForms signal0Constraints) (rank_476 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_477 : (castMatrix (stack relayForms signal1Constraints) : Matrix (Fin 2) (Fin 3) K).rank = 2 := by
  exact rank_int_certificate (stack relayForms signal1Constraints)
    (![![1, 0], ![0, (-1)]]) (![![1, 0, (-1)], ![0, 1, (-1)]]) (![![1, 0], ![0, (-1)]]) (![![1, 0], ![0, 1], ![0, 0]]) (by decide) (by decide)

lemma induced_signal1_dim : finrank K ↥(relay (K := K) ⊓ kernel signal1Constraints) = 1 := by
  have h := kernel_finrank (K := K) (stack relayForms signal1Constraints) (rank_477 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_478 : (castMatrix (stack relayForms signal2Constraints) : Matrix (Fin 2) (Fin 3) K).rank = 1 := by
  exact rank_int_certificate (stack relayForms signal2Constraints)
    (![![1], ![(-1)]]) (![![1, 0, (-1)]]) (![![1, 0]]) (![![1], ![0], ![0]]) (by decide) (by decide)

lemma induced_signal2_dim : finrank K ↥(relay (K := K) ⊓ kernel signal2Constraints) = 2 := by
  have h := kernel_finrank (K := K) (stack relayForms signal2Constraints) (rank_478 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_479 : (castMatrix (stack (stack relayForms signal0Constraints) (stack relayForms signal1Constraints)) : Matrix (Fin 4) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (stack relayForms signal0Constraints) (stack relayForms signal1Constraints))
    (![![1, 0, (-1)], ![1, 0, 0], ![1, 0, (-1)], ![0, (-1), 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![0, 1, 0, 0], ![(-1), 1, 0, (-1)], ![(-1), 1, 0, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma induced_pair01_dim : finrank K ↥((relay (K := K) ⊓ kernel signal0Constraints) ⊓ (relay (K := K) ⊓ kernel signal1Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (stack relayForms signal0Constraints) (stack relayForms signal1Constraints)) (rank_479 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_480 : (castMatrix (stack (stack relayForms signal0Constraints) (stack relayForms signal2Constraints)) : Matrix (Fin 4) (Fin 3) K).rank = 2 := by
  exact rank_int_certificate (stack (stack relayForms signal0Constraints) (stack relayForms signal2Constraints))
    (![![1, (-1)], ![1, 0], ![1, (-1)], ![(-1), 1]]) (![![1, 0, 0], ![0, 0, 1]]) (![![0, 1, 0, 0], ![(-1), 1, 0, 0]]) (![![1, 0], ![0, 0], ![0, 1]]) (by decide) (by decide)

lemma induced_pair02_dim : finrank K ↥((relay (K := K) ⊓ kernel signal0Constraints) ⊓ (relay (K := K) ⊓ kernel signal2Constraints)) = 1 := by
  have h := kernel_finrank (K := K) (stack (stack relayForms signal0Constraints) (stack relayForms signal2Constraints)) (rank_480 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_481 : (castMatrix (stack (stack relayForms signal1Constraints) (stack relayForms signal2Constraints)) : Matrix (Fin 4) (Fin 3) K).rank = 2 := by
  exact rank_int_certificate (stack (stack relayForms signal1Constraints) (stack relayForms signal2Constraints))
    (![![1, 0], ![0, (-1)], ![1, 0], ![(-1), 0]]) (![![1, 0, (-1)], ![0, 1, (-1)]]) (![![1, 0, 0, 0], ![0, (-1), 0, 0]]) (![![1, 0], ![0, 1], ![0, 0]]) (by decide) (by decide)

lemma induced_pair12_dim : finrank K ↥((relay (K := K) ⊓ kernel signal1Constraints) ⊓ (relay (K := K) ⊓ kernel signal2Constraints)) = 1 := by
  have h := kernel_finrank (K := K) (stack (stack relayForms signal1Constraints) (stack relayForms signal2Constraints)) (rank_481 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_482 : (castMatrix (stack (stack (stack relayForms signal0Constraints) (stack relayForms signal1Constraints)) (stack relayForms signal2Constraints)) : Matrix (Fin 6) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (stack (stack relayForms signal0Constraints) (stack relayForms signal1Constraints)) (stack relayForms signal2Constraints))
    (![![1, 0, (-1)], ![1, 0, 0], ![1, 0, (-1)], ![0, (-1), 1], ![1, 0, (-1)], ![(-1), 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![0, 1, 0, 0, 0, 0], ![(-1), 1, 0, (-1), 0, 0], ![(-1), 1, 0, 0, 0, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma induced_triple_dim : finrank K ↥(((relay (K := K) ⊓ kernel signal0Constraints) ⊓ (relay (K := K) ⊓ kernel signal1Constraints)) ⊓ (relay (K := K) ⊓ kernel signal2Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (stack (stack relayForms signal0Constraints) (stack relayForms signal1Constraints)) (stack relayForms signal2Constraints)) (rank_482 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_483 : (castMatrix (stack (stack relayForms side1Constraints) (stack relayForms signal0Constraints)) : Matrix (Fin 5) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (stack relayForms side1Constraints) (stack relayForms signal0Constraints))
    (![![1, 0, (-1)], ![0, 1, 0], ![0, 0, 1], ![1, 0, (-1)], ![1, 0, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 1, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma induced_sideSignal10_dim : finrank K ↥((relay (K := K) ⊓ kernel side1Constraints) ⊓ (relay (K := K) ⊓ kernel signal0Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (stack relayForms side1Constraints) (stack relayForms signal0Constraints)) (rank_483 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_484 : (castMatrix (stack (stack relayForms side2Constraints) (stack relayForms signal0Constraints)) : Matrix (Fin 4) (Fin 3) K).rank = 2 := by
  exact rank_int_certificate (stack (stack relayForms side2Constraints) (stack relayForms signal0Constraints))
    (![![1, (-1)], ![(-1), 1], ![1, (-1)], ![1, 0]]) (![![1, 0, 0], ![0, 0, 1]]) (![![0, 0, 0, 1], ![(-1), 0, 0, 1]]) (![![1, 0], ![0, 0], ![0, 1]]) (by decide) (by decide)

lemma induced_sideSignal20_dim : finrank K ↥((relay (K := K) ⊓ kernel side2Constraints) ⊓ (relay (K := K) ⊓ kernel signal0Constraints)) = 1 := by
  have h := kernel_finrank (K := K) (stack (stack relayForms side2Constraints) (stack relayForms signal0Constraints)) (rank_484 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_485 : (castMatrix (stack (stack relayForms side0Constraints) (stack relayForms signal1Constraints)) : Matrix (Fin 5) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (stack relayForms side0Constraints) (stack relayForms signal1Constraints))
    (![![1, 0, (-1)], ![1, 0, 0], ![0, 1, 0], ![1, 0, (-1)], ![0, (-1), 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![(-1), 1, 0, 0, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma induced_sideSignal01_dim : finrank K ↥((relay (K := K) ⊓ kernel side0Constraints) ⊓ (relay (K := K) ⊓ kernel signal1Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (stack relayForms side0Constraints) (stack relayForms signal1Constraints)) (rank_485 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_486 : (castMatrix (stack (stack relayForms side2Constraints) (stack relayForms signal1Constraints)) : Matrix (Fin 4) (Fin 3) K).rank = 2 := by
  exact rank_int_certificate (stack (stack relayForms side2Constraints) (stack relayForms signal1Constraints))
    (![![1, 0], ![(-1), 0], ![1, 0], ![0, (-1)]]) (![![1, 0, (-1)], ![0, 1, (-1)]]) (![![1, 0, 0, 0], ![0, 0, 0, (-1)]]) (![![1, 0], ![0, 1], ![0, 0]]) (by decide) (by decide)

lemma induced_sideSignal21_dim : finrank K ↥((relay (K := K) ⊓ kernel side2Constraints) ⊓ (relay (K := K) ⊓ kernel signal1Constraints)) = 1 := by
  have h := kernel_finrank (K := K) (stack (stack relayForms side2Constraints) (stack relayForms signal1Constraints)) (rank_486 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_487 : (castMatrix (stack (stack relayForms side0Constraints) (stack relayForms signal2Constraints)) : Matrix (Fin 5) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (stack relayForms side0Constraints) (stack relayForms signal2Constraints))
    (![![1, 0, (-1)], ![1, 0, 0], ![0, 1, 0], ![1, 0, (-1)], ![(-1), 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![(-1), 1, 0, 0, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma induced_sideSignal02_dim : finrank K ↥((relay (K := K) ⊓ kernel side0Constraints) ⊓ (relay (K := K) ⊓ kernel signal2Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (stack relayForms side0Constraints) (stack relayForms signal2Constraints)) (rank_487 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_488 : (castMatrix (stack (stack relayForms side1Constraints) (stack relayForms signal2Constraints)) : Matrix (Fin 5) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (stack relayForms side1Constraints) (stack relayForms signal2Constraints))
    (![![1, 0, (-1)], ![0, 1, 0], ![0, 0, 1], ![1, 0, (-1)], ![(-1), 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 1, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma induced_sideSignal12_dim : finrank K ↥((relay (K := K) ⊓ kernel side1Constraints) ⊓ (relay (K := K) ⊓ kernel signal2Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (stack relayForms side1Constraints) (stack relayForms signal2Constraints)) (rank_488 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_489 : (castMatrix (stack (stack (stack (stack relayForms signal0Constraints) (stack relayForms signal1Constraints)) (stack relayForms signal2Constraints)) (stack relayForms side0Constraints)) : Matrix (Fin 9) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (stack (stack (stack relayForms signal0Constraints) (stack relayForms signal1Constraints)) (stack relayForms signal2Constraints)) (stack relayForms side0Constraints))
    (![![1, 0, (-1)], ![1, 0, 0], ![1, 0, (-1)], ![0, (-1), 1], ![1, 0, (-1)], ![(-1), 0, 1], ![1, 0, (-1)], ![1, 0, 0], ![0, 1, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![0, 1, 0, 0, 0, 0, 0, 0, 0], ![(-1), 1, 0, (-1), 0, 0, 0, 0, 0], ![(-1), 1, 0, 0, 0, 0, 0, 0, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma induced_tripleSide0_dim : finrank K ↥((((relay (K := K) ⊓ kernel signal0Constraints) ⊓ (relay (K := K) ⊓ kernel signal1Constraints)) ⊓ (relay (K := K) ⊓ kernel signal2Constraints)) ⊓ (relay (K := K) ⊓ kernel side0Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (stack (stack (stack relayForms signal0Constraints) (stack relayForms signal1Constraints)) (stack relayForms signal2Constraints)) (stack relayForms side0Constraints)) (rank_489 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_490 : (castMatrix (stack (stack (stack (stack relayForms signal0Constraints) (stack relayForms signal1Constraints)) (stack relayForms signal2Constraints)) (stack relayForms side1Constraints)) : Matrix (Fin 9) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (stack (stack (stack relayForms signal0Constraints) (stack relayForms signal1Constraints)) (stack relayForms signal2Constraints)) (stack relayForms side1Constraints))
    (![![1, 0, (-1)], ![1, 0, 0], ![1, 0, (-1)], ![0, (-1), 1], ![1, 0, (-1)], ![(-1), 0, 1], ![1, 0, (-1)], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![0, 1, 0, 0, 0, 0, 0, 0, 0], ![(-1), 1, 0, (-1), 0, 0, 0, 0, 0], ![(-1), 1, 0, 0, 0, 0, 0, 0, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma induced_tripleSide1_dim : finrank K ↥((((relay (K := K) ⊓ kernel signal0Constraints) ⊓ (relay (K := K) ⊓ kernel signal1Constraints)) ⊓ (relay (K := K) ⊓ kernel signal2Constraints)) ⊓ (relay (K := K) ⊓ kernel side1Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (stack (stack (stack relayForms signal0Constraints) (stack relayForms signal1Constraints)) (stack relayForms signal2Constraints)) (stack relayForms side1Constraints)) (rank_490 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_491 : (castMatrix (stack (stack (stack (stack relayForms signal0Constraints) (stack relayForms signal1Constraints)) (stack relayForms signal2Constraints)) (stack relayForms side2Constraints)) : Matrix (Fin 8) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack (stack (stack (stack relayForms signal0Constraints) (stack relayForms signal1Constraints)) (stack relayForms signal2Constraints)) (stack relayForms side2Constraints))
    (![![1, 0, (-1)], ![1, 0, 0], ![1, 0, (-1)], ![0, (-1), 1], ![1, 0, (-1)], ![(-1), 0, 1], ![1, 0, (-1)], ![(-1), 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![0, 1, 0, 0, 0, 0, 0, 0], ![(-1), 1, 0, (-1), 0, 0, 0, 0], ![(-1), 1, 0, 0, 0, 0, 0, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma induced_tripleSide2_dim : finrank K ↥((((relay (K := K) ⊓ kernel signal0Constraints) ⊓ (relay (K := K) ⊓ kernel signal1Constraints)) ⊓ (relay (K := K) ⊓ kernel signal2Constraints)) ⊓ (relay (K := K) ⊓ kernel side2Constraints)) = 0 := by
  have h := kernel_finrank (K := K) (stack (stack (stack (stack relayForms signal0Constraints) (stack relayForms signal1Constraints)) (stack relayForms signal2Constraints)) (stack relayForms side2Constraints)) (rank_491 (K := K))
  repeat rw [kernel_stack] at h
  exact h

theorem induced_rankConditions : RankConditions (inducedTask (K := K)) relay
    ![0,0,2] ![1,1,2] := by
  apply rankConditions_in_ambient
  · intro i; exact inf_le_left
  · intro i; fin_cases i
    · exact induced_side0_dim
    · exact induced_side1_dim
    · exact induced_side2_dim
  · intro i; fin_cases i
    · exact induced_signal0_dim
    · exact induced_signal1_dim
    · exact induced_signal2_dim
  · intro i j hij; fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change finrank K ↥((relay (K := K) ⊓ kernel signal0Constraints) ⊓ (relay (K := K) ⊓ kernel signal1Constraints)) + finrank K ↥(relay : Submodule K (Fin 3 → K)) = 2
      rw [induced_pair01_dim]
      norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((relay (K := K) ⊓ kernel signal0Constraints) ⊓ (relay (K := K) ⊓ kernel signal2Constraints)) + finrank K ↥(relay : Submodule K (Fin 3 → K)) = 3
      rw [induced_pair02_dim]
      norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((relay (K := K) ⊓ kernel signal1Constraints) ⊓ (relay (K := K) ⊓ kernel signal0Constraints)) + finrank K ↥(relay : Submodule K (Fin 3 → K)) = 2
      rw [inf_comm]
      rw [induced_pair01_dim]
      norm_num [dim_relay, finrank_top, finrank_pi]
    · exact (hij rfl).elim
    · change finrank K ↥((relay (K := K) ⊓ kernel signal1Constraints) ⊓ (relay (K := K) ⊓ kernel signal2Constraints)) + finrank K ↥(relay : Submodule K (Fin 3 → K)) = 3
      rw [induced_pair12_dim]
      norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((relay (K := K) ⊓ kernel signal2Constraints) ⊓ (relay (K := K) ⊓ kernel signal0Constraints)) + finrank K ↥(relay : Submodule K (Fin 3 → K)) = 3
      rw [inf_comm]
      rw [induced_pair02_dim]
      norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((relay (K := K) ⊓ kernel signal2Constraints) ⊓ (relay (K := K) ⊓ kernel signal1Constraints)) + finrank K ↥(relay : Submodule K (Fin 3 → K)) = 3
      rw [inf_comm]
      rw [induced_pair12_dim]
      norm_num [dim_relay, finrank_top, finrank_pi]
    · exact (hij rfl).elim
  · change finrank K ↥(((relay (K := K) ⊓ kernel signal0Constraints) ⊓ (relay (K := K) ⊓ kernel signal1Constraints)) ⊓ (relay (K := K) ⊓ kernel signal2Constraints)) + 2 * finrank K ↥(relay : Submodule K (Fin 3 → K)) = 4
    rw [induced_triple_dim]; norm_num [dim_relay, finrank_top, finrank_pi]
  · intro i j hij; fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change finrank K ↥((relay (K := K) ⊓ kernel side1Constraints) ⊓ (relay (K := K) ⊓ kernel signal0Constraints)) = 1 - finrank K ↥(relay : Submodule K (Fin 3 → K))
      rw [induced_sideSignal10_dim]; norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((relay (K := K) ⊓ kernel side2Constraints) ⊓ (relay (K := K) ⊓ kernel signal0Constraints)) = 3 - finrank K ↥(relay : Submodule K (Fin 3 → K))
      rw [induced_sideSignal20_dim]; norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((relay (K := K) ⊓ kernel side0Constraints) ⊓ (relay (K := K) ⊓ kernel signal1Constraints)) = 1 - finrank K ↥(relay : Submodule K (Fin 3 → K))
      rw [induced_sideSignal01_dim]; norm_num [dim_relay, finrank_top, finrank_pi]
    · exact (hij rfl).elim
    · change finrank K ↥((relay (K := K) ⊓ kernel side2Constraints) ⊓ (relay (K := K) ⊓ kernel signal1Constraints)) = 3 - finrank K ↥(relay : Submodule K (Fin 3 → K))
      rw [induced_sideSignal21_dim]; norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((relay (K := K) ⊓ kernel side0Constraints) ⊓ (relay (K := K) ⊓ kernel signal2Constraints)) = 2 - finrank K ↥(relay : Submodule K (Fin 3 → K))
      rw [induced_sideSignal02_dim]; norm_num [dim_relay, finrank_top, finrank_pi]
    · change finrank K ↥((relay (K := K) ⊓ kernel side1Constraints) ⊓ (relay (K := K) ⊓ kernel signal2Constraints)) = 2 - finrank K ↥(relay : Submodule K (Fin 3 → K))
      rw [induced_sideSignal12_dim]; norm_num [dim_relay, finrank_top, finrank_pi]
    · exact (hij rfl).elim
  · intro i; fin_cases i
    · exact induced_tripleSide0_dim
    · exact induced_tripleSide1_dim
    · exact induced_tripleSide2_dim

theorem induced_first_profile (r : Fin 6) : Profile.entry (inducedTask (K := K)) (.inl r) = ![2,1,2,1,0,0] r := by
  change Profile.firstEntry _ (Profile.firstOrder r).1 (Profile.firstOrder r).2.1 (Profile.firstOrder r).2.2 = _
  rw [firstEntry_max _ _ _ _ induced_rankConditions _ _ _ (by fin_cases r <;> decide) (by fin_cases r <;> decide) (by fin_cases r <;> decide)]
  fin_cases r <;> norm_num [Profile.firstOrder, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, dim_relay, finrank_top, finrank_pi]

theorem induced_second_profile (i ell : Three) : 2 * Profile.entry (inducedTask (K := K)) (.inr (i,ell)) = 2 := by
  change 2 * Profile.secondEntry _ i (i+1) (i+2) ell = _
  rw [secondEntry_formula _ _ _ _ induced_rankConditions _ _ _ _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, dim_relay, finrank_top, finrank_pi]
def relationBasis : Matrix (Fin 4) (Fin 1) ℤ := ![![(-1)], ![(-1)], ![1], ![0]]
lemma rank_492 : (castMatrix (relationBasis) : Matrix (Fin 4) (Fin 1) K).rank = 1 := by
  exact rank_int_certificate (relationBasis)
    (![![(-1)], ![(-1)], ![1], ![0]]) (![![1]]) (![![(-1), 0, 0, 0]]) (![![1]]) (by decide) (by decide)

lemma relation_space : columns (K := K) relationBasis = kernel (joinColumns (joinColumns side0Columns side1Columns) side2Columns) :=
  columns_eq_kernel _ _ (by decide) (rank_492 (K := K)) (rank_455 (K := K)) (by decide)

def relationSlice0 : Matrix (Fin 1) (Fin 1) ℤ := ![![(-1)]]
def relationComponent0 : Matrix (Fin 3) (Fin 1) ℤ := ![![0], ![0], ![(-1)]]
lemma relationComponent0_from_side : side0Columns * relationSlice0 = relationComponent0 := by decide

lemma relationComponent0_in_side : columns (K := K) relationComponent0 ≤ side 0 := by
  change columns (K := K) relationComponent0 ≤ kernel side0Constraints
  rw [← side0_literal]
  exact columns_le_columns _ _ relationSlice0 relationComponent0_from_side

lemma relation_value0 : (castMatrix relayForms : Matrix (Fin 1) (Fin 3) K) * castMatrix relationComponent0 = castMatrix (![![1]] : Matrix (Fin 1) (Fin 1) ℤ) := by
  have h : relayForms * relationComponent0 = (![![1]] : Matrix (Fin 1) (Fin 1) ℤ) := by decide
  simpa only [castMatrix, ← Matrix.map_mul] using congrArg (fun M => M.map (Int.castRingHom K)) h

def relationSlice1 : Matrix (Fin 1) (Fin 1) ℤ := ![![(-1)]]
def relationComponent1 : Matrix (Fin 3) (Fin 1) ℤ := ![![(-1)], ![0], ![0]]
lemma relationComponent1_from_side : side1Columns * relationSlice1 = relationComponent1 := by decide

lemma relationComponent1_in_side : columns (K := K) relationComponent1 ≤ side 1 := by
  change columns (K := K) relationComponent1 ≤ kernel side1Constraints
  rw [← side1_literal]
  exact columns_le_columns _ _ relationSlice1 relationComponent1_from_side

lemma relation_value1 : (castMatrix relayForms : Matrix (Fin 1) (Fin 3) K) * castMatrix relationComponent1 = castMatrix (![![(-1)]] : Matrix (Fin 1) (Fin 1) ℤ) := by
  have h : relayForms * relationComponent1 = (![![(-1)]] : Matrix (Fin 1) (Fin 1) ℤ) := by decide
  simpa only [castMatrix, ← Matrix.map_mul] using congrArg (fun M => M.map (Int.castRingHom K)) h

def relationSlice2 : Matrix (Fin 2) (Fin 1) ℤ := ![![1], ![0]]
def relationComponent2 : Matrix (Fin 3) (Fin 1) ℤ := ![![1], ![0], ![1]]
lemma relationComponent2_from_side : side2Columns * relationSlice2 = relationComponent2 := by decide

lemma relationComponent2_in_side : columns (K := K) relationComponent2 ≤ side 2 := by
  change columns (K := K) relationComponent2 ≤ kernel side2Constraints
  rw [← side2_literal]
  exact columns_le_columns _ _ relationSlice2 relationComponent2_from_side

lemma relation_value2 : (castMatrix relayForms : Matrix (Fin 1) (Fin 3) K) * castMatrix relationComponent2 = castMatrix (![![0]] : Matrix (Fin 1) (Fin 1) ℤ) := by
  have h : relayForms * relationComponent2 = (![![0]] : Matrix (Fin 1) (Fin 1) ℤ) := by decide
  simpa only [castMatrix, ← Matrix.map_mul] using congrArg (fun M => M.map (Int.castRingHom K)) h

lemma relation_slices_partition : stack (stack relationSlice0 relationSlice1) relationSlice2 = relationBasis := by decide

lemma relation_sum : (castMatrix relationComponent0 : Matrix (Fin 3) (Fin 1) K) + castMatrix relationComponent1 + castMatrix relationComponent2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [castMatrix, relationComponent0, relationComponent1, relationComponent2]

theorem relay_form_vanishes : signal (K := K) 2 ≤ relay := by
  change kernel signal2Constraints ≤ relay
  rw [← signal2_literal, ← relay_columns]
  exact columns_le_columns _ _ (![![0, 1], ![1, 0]]) (by decide)

lemma rank_493 : (castMatrix (stack side0Constraints side1Constraints) : Matrix (Fin 4) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack side0Constraints side1Constraints)
    (![![1, 0, 0], ![0, 1, 0], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma side_pair01_dim : finrank K ↥(kernel (K := K) side0Constraints ⊓ kernel side1Constraints) = 0 := by
  have h := kernel_finrank (K := K) (stack side0Constraints side1Constraints) (rank_493 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_494 : (castMatrix (stack side0Constraints side2Constraints) : Matrix (Fin 3) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack side0Constraints side2Constraints)
    (![![1, 0, 0], ![0, 1, 0], ![(-1), 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![1, 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma side_pair02_dim : finrank K ↥(kernel (K := K) side0Constraints ⊓ kernel side2Constraints) = 0 := by
  have h := kernel_finrank (K := K) (stack side0Constraints side2Constraints) (rank_494 (K := K))
  repeat rw [kernel_stack] at h
  exact h

lemma rank_495 : (castMatrix (stack side1Constraints side2Constraints) : Matrix (Fin 3) (Fin 3) K).rank = 3 := by
  exact rank_int_certificate (stack side1Constraints side2Constraints)
    (![![0, 1, 0], ![0, 0, 1], ![(-1), 0, 1]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (![![0, 1, (-1)], ![1, 0, 0], ![0, 1, 0]]) (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) (by decide) (by decide)

lemma side_pair12_dim : finrank K ↥(kernel (K := K) side1Constraints ⊓ kernel side2Constraints) = 0 := by
  have h := kernel_finrank (K := K) (stack side1Constraints side2Constraints) (rank_495 (K := K))
  repeat rw [kernel_stack] at h
  exact h

theorem side_pairwise_disjoint (i j : Three) (hij : i ≠ j) : Disjoint (side (K := K) i) (side j) := by
  rw [disjoint_iff]
  apply Submodule.finrank_eq_zero.mp
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact side_pair01_dim
  · exact side_pair02_dim
  · change finrank K ↥(kernel (K := K) side1Constraints ⊓ kernel side0Constraints) = 0
    rw [inf_comm]; exact side_pair01_dim
  · exact (hij rfl).elim
  · exact side_pair12_dim
  · change finrank K ↥(kernel (K := K) side2Constraints ⊓ kernel side0Constraints) = 0
    rw [inf_comm]; exact side_pair02_dim
  · change finrank K ↥(kernel (K := K) side2Constraints ⊓ kernel side1Constraints) = 0
    rw [inf_comm]; exact side_pair12_dim
  · exact (hij rfl).elim
end O_3
end UploadBroadcast.LiteralPrimitiveTables
