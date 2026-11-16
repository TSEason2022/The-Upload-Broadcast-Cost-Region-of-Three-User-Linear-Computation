import UploadBroadcast.LinearCode
import UploadBroadcast.LinearAlgebra
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Concrete matrix observations and coefficient-space codes

The source matrix has shape d × L. Observations have shape L × m and are
literally X.transpose * V. No independence assumption is made on columns.
For redundant input columns, costs count the attainable upload alphabet,
not encoder values at side-information matrices which cannot occur.
-/
namespace UploadBroadcast
namespace MatrixFrontend
open Matrix
variable {K : Type*} [Field K]

/-- The transpose convention in the paper: columns of X are instances. -/
def sourceEquiv (d L : ℕ) :
    Matrix (Fin d) (Fin L) K ≃ₗ[K] Source K (Fin d → K) L :=
  (Matrix.transposeLinearEquiv _ _ K K).trans Matrix.toLin'

@[simp] theorem sourceEquiv_apply {d L : ℕ}
    (X : Matrix (Fin d) (Fin L) K) (v : Fin d → K) (l : Fin L) :
    sourceEquiv d L X v l = ∑ k, X k l * v k := rfl

/-- Arbitrary original side and demand matrices, including dependent columns. -/
structure Data (d : ℕ) where
  sideWidth : Three → ℕ
  demandWidth : Three → ℕ
  side : ∀ i, Matrix (Fin d) (Fin (sideWidth i)) K
  demand : ∀ i, Matrix (Fin d) (Fin (demandWidth i)) K
  feasible : ∀ i,
    Submodule.span K (Set.range (side i).col) ⊔
      Submodule.span K (Set.range (demand i).col) ≤
        ⨆ j, Submodule.span K (Set.range (side j).col)

namespace Data
variable {d : ℕ} (D : Data (K := K) d)

def task : Task K (Fin d → K) where
  A i := Submodule.span K (Set.range (D.side i).col)
  U i := Submodule.span K (Set.range (D.side i).col) ⊔
    Submodule.span K (Set.range (D.demand i).col)
  side_le_signal _ := le_sup_left
  feasible := D.feasible

abbrev Side (L : ℕ) (i : Three) := Matrix (Fin L) (Fin (D.sideWidth i)) K
abbrev Demand (L : ℕ) (i : Three) := Matrix (Fin L) (Fin (D.demandWidth i)) K

def sideObs {L : ℕ} (i : Three) (X : Matrix (Fin d) (Fin L) K) : D.Side L i :=
  X.transpose * D.side i

def demandObs {L : ℕ} (i : Three) (X : Matrix (Fin d) (Fin L) K) : D.Demand L i :=
  X.transpose * D.demand i

/-- Evaluate a coefficient-space observation on every original side column. -/
def sideEval (L : ℕ) (i : Three) :
    (D.task.A i →ₗ[K] (Fin L → K)) →ₗ[K] D.Side L i where
  toFun a l j := a ⟨(D.side i).col j, Submodule.subset_span ⟨j, rfl⟩⟩ l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluate a signal observation on every original demand column. -/
def demandEval (L : ℕ) (i : Three) :
    (D.task.U i →ₗ[K] (Fin L → K)) →ₗ[K] D.Demand L i where
  toFun a l j := a ⟨(D.demand i).col j,
    (show Submodule.span K (Set.range (D.demand i).col) ≤ D.task.U i from le_sup_right)
      (Submodule.subset_span ⟨j, rfl⟩)⟩ l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction from the full signal to side information. -/
def signalSide (L : ℕ) (i : Three) :
    (D.task.U i →ₗ[K] (Fin L → K)) →ₗ[K] (D.task.A i →ₗ[K] (Fin L → K)) where
  toFun a := a.comp (Submodule.inclusion (D.task.side_le_signal i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def jointEval (L : ℕ) (i : Three) :
    (D.task.U i →ₗ[K] (Fin L → K)) →ₗ[K] (D.Side L i × D.Demand L i) :=
  ((D.sideEval L i).comp (D.signalSide L i)).prod (D.demandEval L i)

@[simp] theorem sideEval_observe {L : ℕ} (i : Three)
    (X : Matrix (Fin d) (Fin L) K) :
    D.sideEval L i (observe K _ (D.task.A i) (sourceEquiv d L X)) = D.sideObs i X := rfl

@[simp] theorem demandEval_observe {L : ℕ} (i : Three)
    (X : Matrix (Fin d) (Fin L) K) :
    D.demandEval L i (observe K _ (D.task.U i) (sourceEquiv d L X)) = D.demandObs i X := rfl

@[simp] theorem jointEval_observe {L : ℕ} (i : Three)
    (X : Matrix (Fin d) (Fin L) K) :
    D.jointEval L i (observe K _ (D.task.U i) (sourceEquiv d L X)) =
      (D.sideObs i X, D.demandObs i X) := rfl

/-- Even with redundant columns, a local matrix determines the entire side restriction. -/
theorem sideEval_injective (L : ℕ) (i : Three) : Function.Injective (D.sideEval L i) := by
  intro a b hab
  obtain ⟨x, hx⟩ := a.exists_extend
  obtain ⟨y, hy⟩ := b.exists_extend
  have hcol : Set.EqOn x y (Set.range (D.side i).col) := by
    rintro v ⟨j, rfl⟩
    have h := congrArg (fun z : D.Side L i => fun l => z l j) hab
    have hxj := LinearMap.congr_fun hx ⟨(D.side i).col j, Submodule.subset_span ⟨j, rfl⟩⟩
    have hyj := LinearMap.congr_fun hy ⟨(D.side i).col j, Submodule.subset_span ⟨j, rfl⟩⟩
    exact hxj.trans (h.trans hyj.symm)
  ext v l
  have he := LinearMap.eqOn_span hcol v.property
  have hxv := LinearMap.congr_fun hx v
  have hyv := LinearMap.congr_fun hy v
  exact congrFun (hxv.symm.trans (he.trans hyv)) l

/-- Side and demand values jointly determine every signal-space coefficient. -/
theorem jointEval_injective (L : ℕ) (i : Three) : Function.Injective (D.jointEval L i) := by
  intro a b hab
  obtain ⟨x, hx⟩ := a.exists_extend
  obtain ⟨y, hy⟩ := b.exists_extend
  have hside : Set.EqOn x y (Set.range (D.side i).col) := by
    rintro v ⟨j, rfl⟩
    have h := congrArg (fun z : D.Side L i × D.Demand L i => fun l => z.1 l j) hab
    let v : D.task.U i := ⟨(D.side i).col j,
      (D.task.side_le_signal i) (Submodule.subset_span ⟨j, rfl⟩)⟩
    exact (LinearMap.congr_fun hx v).trans (h.trans (LinearMap.congr_fun hy v).symm)
  have hdemand : Set.EqOn x y (Set.range (D.demand i).col) := by
    rintro v ⟨j, rfl⟩
    have h := congrArg (fun z : D.Side L i × D.Demand L i => fun l => z.2 l j) hab
    let v : D.task.U i := ⟨(D.demand i).col j,
      (show Submodule.span K (Set.range (D.demand i).col) ≤ D.task.U i from le_sup_right)
        (Submodule.subset_span ⟨j, rfl⟩)⟩
    exact (LinearMap.congr_fun hx v).trans (h.trans (LinearMap.congr_fun hy v).symm)
  ext v l
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp v.property
  have he : x (v : Fin d → K) = y v := by
    rw [← hpq, map_add, map_add, LinearMap.eqOn_span hside hp,
      LinearMap.eqOn_span hdemand hq]
  exact congrFun ((LinearMap.congr_fun hx v).symm.trans
    (he.trans (LinearMap.congr_fun hy v))) l

/-- Linear total reconstruction; unattainable raw side values may be completed arbitrarily. -/
noncomputable def recoverSide (L : ℕ) (i : Three) :
    D.Side L i →ₗ[K] (D.task.A i →ₗ[K] (Fin L → K)) :=
  Classical.choose ((D.sideEval L i).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (D.sideEval_injective L i)))

/-- Linear joint reconstruction on the entire raw product alphabet. -/
noncomputable def recoverJoint (L : ℕ) (i : Three) :
    (D.Side L i × D.Demand L i) →ₗ[K] (D.task.U i →ₗ[K] (Fin L → K)) :=
  Classical.choose ((D.jointEval L i).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (D.jointEval_injective L i)))

@[simp] theorem recoverSide_sideEval (L : ℕ) (i : Three)
    (a : D.task.A i →ₗ[K] (Fin L → K)) :
    D.recoverSide L i (D.sideEval L i a) = a :=
  LinearMap.congr_fun (Classical.choose_spec ((D.sideEval L i).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (D.sideEval_injective L i)))) a

@[simp] theorem recoverJoint_jointEval (L : ℕ) (i : Three)
    (a : D.task.U i →ₗ[K] (Fin L → K)) :
    D.recoverJoint L i (D.jointEval L i a) = a :=
  LinearMap.congr_fun (Classical.choose_spec ((D.jointEval L i).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (D.jointEval_injective L i)))) a

@[simp] theorem recoverSide_observe {L : ℕ} (i : Three)
    (X : Matrix (Fin d) (Fin L) K) :
    D.recoverSide L i (D.sideObs i X) = observe K _ (D.task.A i) (sourceEquiv d L X) := by
  rw [← D.sideEval_observe, D.recoverSide_sideEval]

@[simp] theorem recoverJoint_observe {L : ℕ} (i : Three)
    (X : Matrix (Fin d) (Fin L) K) :
    D.recoverJoint L i (D.sideObs i X, D.demandObs i X) =
      observe K _ (D.task.U i) (sourceEquiv d L X) := by
  rw [← D.jointEval_observe, D.recoverJoint_jointEval]


/-- Full column rank makes every raw local side-information matrix attainable. -/
theorem sideObs_surjective_of_independent {L : ℕ} (i : Three)
    (h : LinearIndependent K (D.side i).col) : Function.Surjective (D.sideObs (L := L) i) := by
  have hi : Function.Injective (Matrix.toLin' (D.side i)) := Matrix.mulVec_injective_iff.mpr h
  obtain ⟨g, hg⟩ := (Matrix.toLin' (D.side i)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hi)
  let G := LinearMap.toMatrix' g
  have hGV : G * D.side i = 1 := by
    apply Matrix.toLin'.injective
    simpa only [G, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one] using hg
  intro W
  refine ⟨(W * G).transpose, ?_⟩
  simp only [sideObs, Matrix.transpose_transpose, Matrix.mul_assoc, hGV, Matrix.mul_one]

/-- Original matrix code: finite alphabets may be supplied by `Fin`; all maps
here are arbitrary functions and correctness is for every source matrix. -/
structure Code (L : ℕ) (M : Three → Type*) (S : Type*) where
  encode : ∀ i, D.Side L i → M i
  broadcast : (∀ i, M i) → S
  decode : ∀ i, S → D.Side L i → D.Demand L i
  zero_error : ∀ (X : Matrix (Fin d) (Fin L) K) i,
    decode i (broadcast (fun j => encode j (D.sideObs j X))) (D.sideObs i X) =
      D.demandObs i X

namespace Code
variable {D} {L : ℕ} {M : Three → Type*} {S : Type*}

def transmitted (c : D.Code L M S) (X : Matrix (Fin d) (Fin L) K) : S :=
  c.broadcast (fun i => c.encode i (D.sideObs i X))

/-- Exact attained alphabets, including when raw columns are redundant. -/
noncomputable def uploadCost (c : D.Code L M S) : ℝ :=
  (∑ i, Real.logb (Nat.card K)
    (Nat.card (Set.range (fun X : Matrix (Fin d) (Fin L) K =>
      c.encode i (D.sideObs i X))))) / L

noncomputable def broadcastCost (c : D.Code L M S) : ℝ :=
  Real.logb (Nat.card K) (Nat.card (Set.range c.transmitted)) / L

/-- This specializes the attained-upload definition to the paper's formula
im(e_i), once the side columns have been made independent. -/
theorem upload_range_of_independent (c : D.Code L M S) (i : Three)
    (h : LinearIndependent K (D.side i).col) :
    Set.range (fun X : Matrix (Fin d) (Fin L) K => c.encode i (D.sideObs i X)) =
      Set.range (c.encode i) := by
  ext z
  constructor
  · rintro ⟨X, rfl⟩; exact ⟨D.sideObs i X, rfl⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨X, rfl⟩ := D.sideObs_surjective_of_independent i h w
    exact ⟨X, rfl⟩

/-- Matrix demand recovery becomes full signal recovery, without altering
any upload alphabet or the relay map. -/
noncomputable def toTask (c : D.Code L M S) : D.task.Code L M S where
  encode i a := c.encode i (D.sideEval L i a)
  broadcast := c.broadcast
  decode i b a := D.recoverJoint L i
    (D.sideEval L i a, c.decode i b (D.sideEval L i a))
  zero_error x i := by
    obtain ⟨X, rfl⟩ := (sourceEquiv d L).surjective x
    simp only [D.sideEval_observe, c.zero_error, D.recoverJoint_observe]

/-- Conversely, the coefficient-space decoder returns the demanded columns. -/
noncomputable def ofTask (c : D.task.Code L M S) : D.Code L M S where
  encode i w := c.encode i (D.recoverSide L i w)
  broadcast := c.broadcast
  decode i b w := D.demandEval L i (c.decode i b (D.recoverSide L i w))
  zero_error X i := by
    simp only [D.recoverSide_observe, c.zero_error, D.demandEval_observe]

@[simp] theorem toTask_transmitted (c : D.Code L M S)
    (X : Matrix (Fin d) (Fin L) K) :
    c.toTask.transmitted (sourceEquiv d L X) = c.transmitted X := rfl

@[simp] theorem ofTask_transmitted (c : D.task.Code L M S)
    (X : Matrix (Fin d) (Fin L) K) :
    (ofTask c).transmitted X = c.transmitted (sourceEquiv d L X) := by
  simp only [transmitted, ofTask, D.recoverSide_observe, Task.Code.transmitted]

/-- Every abstract side restriction is generated by an actual d × L matrix. -/
theorem exists_source_side (a : D.task.A i →ₗ[K] (Fin L → K)) :
    ∃ X : Matrix (Fin d) (Fin L) K,
      observe K _ (D.task.A i) (sourceEquiv d L X) = a := by
  obtain ⟨x, hx⟩ := a.exists_extend
  obtain ⟨X, rfl⟩ := (sourceEquiv d L).surjective x
  exact ⟨X, hx⟩

/-- Encoder ranges agree exactly, even for nonlinear encoders. -/
theorem toTask_upload_range (c : D.Code L M S) (i : Three) :
    Set.range (c.toTask.encode i) =
      Set.range (fun X : Matrix (Fin d) (Fin L) K => c.encode i (D.sideObs i X)) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨X, hx⟩ := exists_source_side a
    refine ⟨X, ?_⟩
    change c.encode i (D.sideObs i X) = c.encode i (D.sideEval L i a)
    rw [← D.sideEval_observe, hx]
  · rintro ⟨X, rfl⟩
    exact ⟨observe K _ (D.task.A i) (sourceEquiv d L X), rfl⟩

theorem toTask_broadcast_range (c : D.Code L M S) :
    Set.range c.toTask.transmitted = Set.range c.transmitted := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨X, rfl⟩ := (sourceEquiv d L).surjective x
    exact ⟨X, rfl⟩
  · rintro ⟨X, rfl⟩
    exact ⟨sourceEquiv d L X, rfl⟩

@[simp] theorem toTask_uploadCost [Finite K] (c : D.Code L M S) :
    c.toTask.uploadCost = c.uploadCost := by
  unfold Task.Code.uploadCost uploadCost
  simp_rw [toTask_upload_range]

@[simp] theorem toTask_broadcastCost [Finite K] (c : D.Code L M S) :
    c.toTask.broadcastCost = c.broadcastCost := by
  unfold Task.Code.broadcastCost broadcastCost
  rw [toTask_broadcast_range]

@[simp] theorem ofTask_toTask_encode (c : D.task.Code L M S) (i : Three) :
    (ofTask c).toTask.encode i = c.encode i := by
  funext a
  exact congrArg (c.encode i) (D.recoverSide_sideEval L i a)

@[simp] theorem ofTask_uploadCost [Finite K] (c : D.task.Code L M S) :
    (ofTask c).uploadCost = c.uploadCost := by
  rw [← toTask_uploadCost]
  unfold Task.Code.uploadCost
  simp only [ofTask_toTask_encode]

@[simp] theorem ofTask_broadcastCost [Finite K] (c : D.task.Code L M S) :
    (ofTask c).broadcastCost = c.broadcastCost := by
  rw [← toTask_broadcastCost]
  have h : (ofTask c).toTask.transmitted = c.transmitted := by
    funext x
    unfold Task.Code.transmitted
    simp only [ofTask_toTask_encode]
    rfl
  unfold Task.Code.broadcastCost
  rw [h]

end Code

/-- Original matrix-linear code. Vectorization of these finite matrix spaces
is the usual block-linear encoder/decoder convention. -/
structure LinearCode (L : ℕ) (r : Three → ℕ) (s : ℕ) where
  encode : ∀ i, D.Side L i →ₗ[K] (Fin (r i) → K)
  broadcast : (∀ i, Fin (r i) → K) →ₗ[K] (Fin s → K)
  decode : ∀ i, ((Fin s → K) × D.Side L i) →ₗ[K] D.Demand L i
  zero_error : ∀ (X : Matrix (Fin d) (Fin L) K) i,
    decode i (broadcast (fun j => encode j (D.sideObs j X)), D.sideObs i X) =
      D.demandObs i X

namespace LinearCode
variable {D} {L : ℕ} {r : Three → ℕ} {s : ℕ}

def toCode (c : D.LinearCode L r s) : D.Code L (fun i => Fin (r i) → K) (Fin s → K) where
  encode i := c.encode i
  broadcast := c.broadcast
  decode i b a := c.decode i (b, a)
  zero_error := c.zero_error

/-- The matrix-to-task transport is linear when the original code is linear. -/
noncomputable def toTask (c : D.LinearCode L r s) : D.task.LinearCode L r s where
  encode i := (c.encode i).comp (D.sideEval L i)
  broadcast := c.broadcast
  decode i := (D.recoverJoint L i).comp
    (((D.sideEval L i).comp (LinearMap.snd K _ _)).prod
      ((c.decode i).comp (LinearMap.id.prodMap (D.sideEval L i))))
  zero_error := c.toCode.toTask.zero_error

/-- The reverse transport uses a linear side reconstruction and evaluates demands. -/
noncomputable def ofTask (c : D.task.LinearCode L r s) : D.LinearCode L r s where
  encode i := (c.encode i).comp (D.recoverSide L i)
  broadcast := c.broadcast
  decode i := (D.demandEval L i).comp
    ((c.decode i).comp (LinearMap.id.prodMap (D.recoverSide L i)))
  zero_error := (Code.ofTask c.toCode).zero_error

@[simp] theorem toTask_toCode (c : D.LinearCode L r s) :
    c.toTask.toCode = c.toCode.toTask := rfl

@[simp] theorem ofTask_toCode (c : D.task.LinearCode L r s) :
    (ofTask c).toCode = Code.ofTask c.toCode := rfl

@[simp] theorem toTask_uploadCost [Finite K] (c : D.LinearCode L r s) :
    c.toTask.toCode.uploadCost = c.toCode.uploadCost := Code.toTask_uploadCost c.toCode

@[simp] theorem toTask_broadcastCost [Finite K] (c : D.LinearCode L r s) :
    c.toTask.toCode.broadcastCost = c.toCode.broadcastCost := Code.toTask_broadcastCost c.toCode

@[simp] theorem ofTask_uploadCost [Finite K] (c : D.task.LinearCode L r s) :
    (ofTask c).toCode.uploadCost = c.toCode.uploadCost := Code.ofTask_uploadCost c.toCode

@[simp] theorem ofTask_broadcastCost [Finite K] (c : D.task.LinearCode L r s) :
    (ofTask c).toCode.broadcastCost = c.toCode.broadcastCost := Code.ofTask_broadcastCost c.toCode

end LinearCode

/-- Linear feasibility preserves the identical L and transmission lengths. -/
theorem linearCode_nonempty_iff (L : ℕ) (r : Three → ℕ) (s : ℕ) :
    Nonempty (D.LinearCode L r s) ↔ Nonempty (D.task.LinearCode L r s) :=
  ⟨fun ⟨c⟩ => ⟨c.toTask⟩, fun ⟨c⟩ => ⟨LinearCode.ofTask c⟩⟩

/-- Fixed-blocklength matrix cost budgets with arbitrary deterministic codes. -/
def achievableAt (L : ℕ) : Set (ℝ × ℝ) :=
  {b | 0 < L ∧ 0 ≤ b.1 ∧ 0 ≤ b.2 ∧
    ∃ (m : Three → ℕ) (s : ℕ) (c : D.Code L (fun i => Fin (m i)) (Fin s)),
      c.uploadCost ≤ b.1 ∧ c.broadcastCost ≤ b.2}

/-- Complete code-level matrix-to-task equivalence, at each original L. -/
theorem achievableAt_eq [Finite K] (L : ℕ) :
    D.achievableAt L = D.task.achievableAt L := by
  ext b
  constructor
  · rintro ⟨hL, hu, hd, m, s, c, hcu, hcd⟩
    exact ⟨hL, hu, hd, m, s, c.toTask, by simpa using hcu, by simpa using hcd⟩
  · rintro ⟨hL, hu, hd, m, s, c, hcu, hcd⟩
    exact ⟨hL, hu, hd, m, s, Code.ofTask c, by simpa using hcu, by simpa using hcd⟩

/-- Changing side generators and demands while preserving the side and joint
spans preserves the original nonlinear zero-error budget region for every L. -/
theorem redundant_columns_achievableAt_eq [Finite K] (E : Data (K := K) d)
    (hA : ∀ i, Submodule.span K (Set.range (D.side i).col) =
      Submodule.span K (Set.range (E.side i).col))
    (hU : ∀ i,
      Submodule.span K (Set.range (D.side i).col) ⊔
        Submodule.span K (Set.range (D.demand i).col) =
      Submodule.span K (Set.range (E.side i).col) ⊔
        Submodule.span K (Set.range (E.demand i).col)) (L : ℕ) :
    D.achievableAt L = E.achievableAt L := by
  have ht : D.task = E.task := by
    unfold task
    congr
    · exact funext hA
    · exact funext hU
  rw [D.achievableAt_eq, E.achievableAt_eq, ht]


/-- Per-code transport between different matrix presentations preserves exact
costs and the same message types, not merely an infimum or asymptotic limit. -/
theorem code_costs_of_task_eq [Finite K] (E : Data (K := K) d)
    (ht : D.task = E.task) {L : ℕ} {M : Three → Type*} {S : Type*}
    (c : D.Code L M S) :
    ∃ c' : E.Code L M S,
      c'.uploadCost = c.uploadCost ∧ c'.broadcastCost = c.broadcastCost := by
  have hc : ∃ t : E.task.Code L M S,
      t.uploadCost = c.uploadCost ∧ t.broadcastCost = c.broadcastCost := by
    rw [← ht]
    exact ⟨c.toTask, c.toTask_uploadCost, c.toTask_broadcastCost⟩
  obtain ⟨t, hu, hd⟩ := hc
  exact ⟨Code.ofTask t, by simpa using hu, by simpa using hd⟩

/-- This transport also preserves linearity and the original L,r,s exactly. -/
theorem linearCode_costs_of_task_eq [Finite K] (E : Data (K := K) d)
    (ht : D.task = E.task) {L : ℕ} {r : Three → ℕ} {s : ℕ}
    (c : D.LinearCode L r s) :
    ∃ c' : E.LinearCode L r s,
      c'.toCode.uploadCost = c.toCode.uploadCost ∧
      c'.toCode.broadcastCost = c.toCode.broadcastCost := by
  have hc : ∃ t : E.task.LinearCode L r s,
      t.toCode.uploadCost = c.toCode.uploadCost ∧
      t.toCode.broadcastCost = c.toCode.broadcastCost := by
    rw [← ht]
    exact ⟨c.toTask, c.toTask_uploadCost, c.toTask_broadcastCost⟩
  obtain ⟨t, hu, hd⟩ := hc
  exact ⟨LinearCode.ofTask t, by simpa using hu, by simpa using hd⟩

/-- The matrix model has the same regularized closed region as Model.lean. -/
def costRegion : Set (ℝ × ℝ) := closure (⋃ L, D.achievableAt L)

theorem costRegion_eq [Finite K] : D.costRegion = D.task.costRegion := by
  unfold costRegion Task.costRegion
  simp_rw [D.achievableAt_eq]

noncomputable def uploadOptimum : ℝ :=
  sInf {u : ℝ | ∃ v : ℝ, 0 ≤ v ∧ (u, v) ∈ D.costRegion}

theorem uploadOptimum_eq [Finite K] : D.uploadOptimum = D.task.uploadOptimum := by
  unfold uploadOptimum Task.uploadOptimum
  rw [D.costRegion_eq]

/-- Coordinates of a subspace basis as columns of a finite matrix. -/
noncomputable def basisMatrix (P : Submodule K (Fin d → K)) :
    Matrix (Fin d) (Fin (Module.finrank K P)) K :=
  fun k j => (Module.finBasis K P j : Fin d → K) k

theorem basisMatrix_span (P : Submodule K (Fin d → K)) :
    Submodule.span K (Set.range (basisMatrix P).col) = P := by
  change Submodule.span K (Set.range (P.subtype ∘ Module.finBasis K P)) = P
  rw [Set.range_comp, ← Submodule.map_span, Basis.span_eq, Submodule.map_subtype_top]

theorem basisMatrix_independent (P : Submodule K (Fin d → K)) :
    LinearIndependent K (basisMatrix P).col :=
  (Module.finBasis K P).linearIndependent.map' P.subtype P.ker_subtype

/-- A complement in the ambient coordinate space; its intersection with U
provides demand directions independent of all side directions. -/
noncomputable def sideComplement (i : Three) : Submodule K (Fin d → K) :=
  Classical.choose (D.task.A i).exists_isCompl

theorem sideComplement_isCompl (i : Three) : IsCompl (D.task.A i) (D.sideComplement i) :=
  Classical.choose_spec (D.task.A i).exists_isCompl

noncomputable def demandComplement (i : Three) : Submodule K (Fin d → K) :=
  D.task.U i ⊓ D.sideComplement i

theorem demandComplement_sup (i : Three) :
    D.task.A i ⊔ D.demandComplement i = D.task.U i := by
  apply (relay_decomposition _ _ _ (D.task.side_le_signal i) ?_).symm
  rw [(D.sideComplement_isCompl i).codisjoint.eq_top]
  exact le_top

theorem demandComplement_disjoint (i : Three) :
    Disjoint (D.task.A i) (D.demandComplement i) :=
  (D.sideComplement_isCompl i).disjoint.mono_right inf_le_right

/-- A concrete simultaneous side/demand basis normalization. -/
noncomputable def normalized : Data (K := K) d where
  sideWidth i := Module.finrank K (D.task.A i)
  demandWidth i := Module.finrank K (D.demandComplement i)
  side i := basisMatrix (D.task.A i)
  demand i := basisMatrix (D.demandComplement i)
  feasible i := by
    simp only [basisMatrix_span, D.demandComplement_sup]
    exact D.task.feasible i

@[simp] theorem normalized_side_span (i : Three) :
    Submodule.span K (Set.range (D.normalized.side i).col) = D.task.A i :=
  basisMatrix_span _

@[simp] theorem normalized_joint_span (i : Three) :
    Submodule.span K (Set.range (D.normalized.side i).col) ⊔
      Submodule.span K (Set.range (D.normalized.demand i).col) = D.task.U i := by
  change Submodule.span K (Set.range (basisMatrix (D.task.A i)).col) ⊔
    Submodule.span K (Set.range (basisMatrix (D.demandComplement i)).col) = _
  rw [basisMatrix_span, basisMatrix_span, D.demandComplement_sup]

/-- Full column rank of the concatenated normalized side/demand matrices. -/
theorem normalized_joint_independent (i : Three) :
    LinearIndependent K (Sum.elim (D.normalized.side i).col (D.normalized.demand i).col) := by
  apply (basisMatrix_independent (D.task.A i)).sum_type
    (basisMatrix_independent (D.demandComplement i))
  rw [basisMatrix_span, basisMatrix_span]
  exact D.demandComplement_disjoint i

theorem normalized_demandWidth (i : Three) :
    D.normalized.demandWidth i = Module.finrank K (D.task.U i) -
      Module.finrank K (D.task.A i) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (D.task.A i) (D.demandComplement i)
  rw [D.demandComplement_sup, (D.demandComplement_disjoint i).eq_bot,
    finrank_bot, add_zero] at h
  change Module.finrank K (D.demandComplement i) = _
  omega

/-- Normalization is operationally exact for all blocklengths and nonlinear codes. -/
theorem normalized_achievableAt_eq [Finite K] (L : ℕ) :
    D.achievableAt L = D.normalized.achievableAt L :=
  D.redundant_columns_achievableAt_eq D.normalized
    (fun i => (D.normalized_side_span i).symm)
    (fun i => (D.normalized_joint_span i).symm) L


@[simp] theorem normalized_task_eq : D.normalized.task = D.task := by
  have hA : (fun i => Submodule.span K (Set.range (D.normalized.side i).col)) =
      (fun i => Submodule.span K (Set.range (D.side i).col)) :=
    funext fun i => D.normalized_side_span i
  have hU : (fun i => Submodule.span K (Set.range (D.normalized.side i).col) ⊔
      Submodule.span K (Set.range (D.normalized.demand i).col)) =
      (fun i => Submodule.span K (Set.range (D.side i).col) ⊔
      Submodule.span K (Set.range (D.demand i).col)) :=
    funext fun i => D.normalized_joint_span i
  unfold task
  congr

/-- The normalized concatenation has rank m'_i + m_i. -/
theorem normalized_joint_rank (i : Three) :
    Module.finrank K (Submodule.span K
      (Set.range (Sum.elim (D.normalized.side i).col (D.normalized.demand i).col))) =
        D.normalized.sideWidth i + D.normalized.demandWidth i := by
  simpa using finrank_span_eq_card (D.normalized_joint_independent i)

/-- All three source claims are available simultaneously: side dimension,
conditional demand dimension, and full concatenated column rank. -/
theorem normalized_dimensions (i : Three) :
    D.normalized.sideWidth i = Module.finrank K (D.task.A i) ∧
    D.normalized.demandWidth i = Module.finrank K (D.task.U i) -
      Module.finrank K (D.task.A i) ∧
    LinearIndependent K (Sum.elim (D.normalized.side i).col (D.normalized.demand i).col) :=
  ⟨rfl, D.normalized_demandWidth i, D.normalized_joint_independent i⟩

/-- Exact per-code nonlinear normalization, with the same L and message types. -/
theorem normalize_code [Finite K] {L : ℕ} {M : Three → Type*} {S : Type*}
    (c : D.Code L M S) :
    ∃ c' : D.normalized.Code L M S,
      c'.uploadCost = c.uploadCost ∧ c'.broadcastCost = c.broadcastCost :=
  D.code_costs_of_task_eq D.normalized D.normalized_task_eq.symm c

/-- Exact per-code linear normalization, including scalar/vector blocklength. -/
theorem normalize_linearCode [Finite K] {L : ℕ} {r : Three → ℕ} {s : ℕ}
    (c : D.LinearCode L r s) :
    ∃ c' : D.normalized.LinearCode L r s,
      c'.toCode.uploadCost = c.toCode.uploadCost ∧
      c'.toCode.broadcastCost = c.toCode.broadcastCost :=
  D.linearCode_costs_of_task_eq D.normalized D.normalized_task_eq.symm c


/-- Restore an original nonlinear matrix code from the reduced columns. -/
theorem denormalize_code [Finite K] {L : ℕ} {M : Three → Type*} {S : Type*}
    (c : D.normalized.Code L M S) :
    ∃ c' : D.Code L M S,
      c'.uploadCost = c.uploadCost ∧ c'.broadcastCost = c.broadcastCost :=
  D.normalized.code_costs_of_task_eq D D.normalized_task_eq c

/-- Reverse linear normalization also retains the exact original blocklength. -/
theorem denormalize_linearCode [Finite K] {L : ℕ} {r : Three → ℕ} {s : ℕ}
    (c : D.normalized.LinearCode L r s) :
    ∃ c' : D.LinearCode L r s,
      c'.toCode.uploadCost = c.toCode.uploadCost ∧
      c'.toCode.broadcastCost = c.toCode.broadcastCost :=
  D.normalized.linearCode_costs_of_task_eq D D.normalized_task_eq c


/-- One may literally retain original side columns and original demand columns:
choose an independent side subset, then extend it inside side ∪ demand. The
additional columns are all demands. This does not require replacing original
columns by newly invented coefficient directions. -/
theorem exists_retained_column_sets (i : Three) :
    ∃ (a b : Set (Fin d → K)),
      a ⊆ Set.range (D.side i).col ∧ b ⊆ Set.range (D.demand i).col ∧
      a.Finite ∧ b.Finite ∧ Disjoint a b ∧
      Submodule.span K a = D.task.A i ∧
      Submodule.span K (a ∪ b) = D.task.U i ∧
      LinearIndepOn K id (a ∪ b) := by
  obtain ⟨a, ha, hspan, hli⟩ := exists_linearIndependent K (Set.range (D.side i).col)
  have haind : LinearIndepOn K id a := hli
  obtain ⟨c, hc, hac, hcover, hci⟩ :=
    exists_linearIndepOn_id_extension haind
      (show a ⊆ a ∪ Set.range (D.demand i).col from Set.subset_union_left)
  have hu : a ∪ (c \ a) = c := Set.union_diff_cancel hac
  have hb : c \ a ⊆ Set.range (D.demand i).col := by
    intro x hx
    exact (hc hx.1).resolve_left hx.2
  have hcspan : Submodule.span K c = D.task.U i := by
    have he : Submodule.span K c = Submodule.span K (a ∪ Set.range (D.demand i).col) :=
      le_antisymm (Submodule.span_mono hc) (Submodule.span_le.mpr hcover)
    rw [he, Submodule.span_union, hspan]
    rfl
  refine ⟨a, c \ a, ha, hb, (Set.finite_range _).subset ha,
    (Set.finite_range _).subset hb, ?_, hspan, ?_, ?_⟩
  · exact Set.disjoint_left.mpr fun x hx hy => hy.2 hx
  · rwa [hu]
  · rwa [hu]


omit [Field K] in
/-- Enumerate a finite set as nonrepeating columns of a finite matrix. -/
theorem finite_set_matrix (a : Set (Fin d → K)) (ha : a.Finite) :
    ∃ (m : ℕ) (V : Matrix (Fin d) (Fin m) K),
      Set.range V.col = a ∧ Function.Injective V.col := by
  classical
  letI := ha.fintype
  let e := (Fintype.equivFin a).symm
  let V : Matrix (Fin d) (Fin (Fintype.card a)) K := fun k j => (e j : Fin d → K) k
  refine ⟨Fintype.card a, V, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨j, rfl⟩; exact (e j).property
    · intro hv
      refine ⟨e.symm ⟨v, hv⟩, ?_⟩
      change (e (e.symm ⟨v, hv⟩) : Fin d → K) = v
      simp
  · exact Subtype.val_injective.comp e.injective

/-- The retained-column choice is represented by actual finite matrices,
with all columns taken from the corresponding original side/demand matrices. -/
theorem exists_retained_matrices (i : Three) :
    ∃ (ma mb : ℕ) (V : Matrix (Fin d) (Fin ma) K) (W : Matrix (Fin d) (Fin mb) K),
      Set.range V.col ⊆ Set.range (D.side i).col ∧
      Set.range W.col ⊆ Set.range (D.demand i).col ∧
      Submodule.span K (Set.range V.col) = D.task.A i ∧
      Submodule.span K (Set.range V.col) ⊔ Submodule.span K (Set.range W.col) = D.task.U i ∧
      LinearIndependent K (Sum.elim V.col W.col) := by
  obtain ⟨a, b, ha, hb, hfa, hfb, hab, hA, hU, hli⟩ := D.exists_retained_column_sets i
  obtain ⟨ma, V, hV, hiV⟩ := finite_set_matrix a hfa
  obtain ⟨mb, W, hW, hiW⟩ := finite_set_matrix b hfb
  have hi : Function.Injective (Sum.elim V.col W.col) :=
    hiV.sumElim hiW (by
      intro j k he
      have hv : V.col j ∈ a := hV ▸ Set.mem_range_self j
      have hw : W.col k ∈ b := hW ▸ Set.mem_range_self k
      exact Set.disjoint_left.mp hab hv (he.symm ▸ hw))
  refine ⟨ma, mb, V, W, hV ▸ ha, hW ▸ hb, hV ▸ hA, ?_, ?_⟩
  · rw [hV, hW, ← Submodule.span_union]
    exact hU
  · apply (linearIndepOn_id_range_iff hi).mp
    rwa [Set.Sum.elim_range, hV, hW]

/-- Literal removal of redundant columns is possible simultaneously for all
three users and preserves every fixed-L region. The matrix transports above
also give exact per-code and same-blocklength linear transports through the
returned equality of coefficient tasks. -/
theorem exists_retained_normalization [Finite K] :
    ∃ E : Data (K := K) d,
      E.task = D.task ∧
      (∀ i, Set.range (E.side i).col ⊆ Set.range (D.side i).col ∧
        Set.range (E.demand i).col ⊆ Set.range (D.demand i).col ∧
        LinearIndependent K (Sum.elim (E.side i).col (E.demand i).col)) ∧
      ∀ L, E.achievableAt L = D.achievableAt L := by
  classical
  choose ma mb V W hV hW hA hU hli using D.exists_retained_matrices
  let E : Data (K := K) d := {
    sideWidth := ma
    demandWidth := mb
    side := V
    demand := W
    feasible := by
      intro i
      rw [hU i]
      have h := iSup_congr hA
      rw [h]
      exact D.task.feasible i }
  have ht : E.task = D.task := by
    unfold task
    congr
    · exact funext hA
    · exact funext hU
  refine ⟨E, ht, fun i => ⟨hV i, hW i, hli i⟩, ?_⟩
  intro L
  rw [E.achievableAt_eq, D.achievableAt_eq, ht]

end Data
end MatrixFrontend
end UploadBroadcast
