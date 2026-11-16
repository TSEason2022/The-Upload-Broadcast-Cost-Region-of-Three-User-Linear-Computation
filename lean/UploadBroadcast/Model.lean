import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Coordinate-free model of three-user upload--broadcast computation

Source: `eq:task-spaces`, `eq:model-code`, `eq:costs`.
A source block is a linear map from the coefficient space to `K^L`.
This is exactly the matrix model after choosing a basis, with no source
probability distribution. Decoding recovers the complete signal space,
which is equivalent to demand recovery in the presence of side information.
-/
namespace UploadBroadcast

abbrev Three := Fin 3

variable (K F : Type*) [Field K] [AddCommGroup F] [Module K F]

/-- A feasible three-user coefficient-space task. The optional normalization
`iSup A = top` is stated separately so induced relay tasks are also covered. -/
structure Task where
  A : Three → Submodule K F
  U : Three → Submodule K F
  side_le_signal : ∀ i, A i ≤ U i
  feasible : ∀ i, U i ≤ ⨆ j, A j

/-- The block source in the paper's coefficient-space convention. -/
abbrev Source (L : ℕ) := F →ₗ[K] (Fin L → K)

/-- Observing every coefficient in a subspace, without a choice of basis. -/
def observe {L : ℕ} (A : Submodule K F) (x : Source K F L) :
    A →ₗ[K] (Fin L → K) := x.comp A.subtype

variable {K F}

/-- Conditional rank, `dim(B+C)-dim B`, in q-ary symbols per instance. -/
noncomputable def condRank [FiniteDimensional K F]
    (C B : Submodule K F) : ℕ :=
  Module.finrank K ↥(B ⊔ C) - Module.finrank K B

namespace Task

variable (T : Task K F)

/-- Normalized ambient space used in the paper after removing unused directions. -/
def Spanning : Prop := (⨆ i, T.A i) = ⊤

/-- Relay feasibility is exactly `eq:relay-feasible`; this does not assert
local generation, which is a separate property. -/
def RelayFeasible (P : Submodule K F) : Prop := ∀ i, T.U i ≤ T.A i ⊔ P

/-- A relay space can be produced from local linear uploads. -/
def LocallyGenerated (P : Submodule K F) : Prop := P = ⨆ i, P ⊓ T.A i

/-- Fixed-length deterministic zero-error code. Message types are arbitrary,
so nonlinear encoders and decoders are included. Finite alphabets are imposed
by `FiniteCode` below. -/
structure Code (L : ℕ) (M : Three → Type*) (S : Type*) where
  encode : ∀ i, (T.A i →ₗ[K] (Fin L → K)) → M i
  broadcast : (∀ i, M i) → S
  decode : ∀ i, S → (T.A i →ₗ[K] (Fin L → K)) →
    (T.U i →ₗ[K] (Fin L → K))
  zero_error : ∀ (x : Source K F L) i,
    decode i (broadcast (fun j => encode j (observe K F (T.A j) x)))
      (observe K F (T.A i) x) = observe K F (T.U i) x

/-- Finiteness and positive blocklength are part of an admissible code. -/
structure FiniteCode (L : ℕ) (M : Three → Type*) (S : Type*)
    extends T.Code L M S where
  positive_blocklength : 0 < L
  finite_upload : ∀ i, Finite (M i)
  finite_broadcast : Finite S

namespace Code
variable {T} {L : ℕ} {M : Three → Type*} {S : Type*}

/-- Attainable broadcast as a function of the source, rather than all formal
upload tuples (some tuples need not be jointly attainable). -/
def transmitted (c : T.Code L M S) (x : Source K F L) : S :=
  c.broadcast (fun i => c.encode i (observe K F (T.A i) x))

/-- Exact logarithmic alphabet cost (not entropy). -/
noncomputable def uploadCost [Finite K] [FiniteDimensional K F] (c : T.Code L M S) : ℝ :=
  (∑ i, Real.logb (Nat.card K) (Nat.card (Set.range (c.encode i)))) / L

/-- Exact logarithmic attainable broadcast cost. -/
noncomputable def broadcastCost [Finite K] [FiniteDimensional K F] (c : T.Code L M S) : ℝ :=
  Real.logb (Nat.card K) (Nat.card (Set.range c.transmitted)) / L

/-- Given its own side information, a user reconstructs its own upload;
therefore only the other uploads need be arguments to the upload-only decoder.
This proves the necessity direction of `eq:upload-only-feasibility`. -/
theorem exists_upload_only_decoder (c : T.Code L M S) :
    ∃ d : ∀ i, (T.A i →ₗ[K] (Fin L → K)) →
      (∀ j, j ≠ i → M j) → (T.U i →ₗ[K] (Fin L → K)),
      ∀ (x : Source K F L) i,
        d i (observe K F (T.A i) x)
          (fun j _ => c.encode j (observe K F (T.A j) x)) =
            observe K F (T.U i) x := by
  classical
  let d := fun i (a : T.A i →ₗ[K] (Fin L → K)) (m : ∀ j, j ≠ i → M j) =>
    c.decode i (c.broadcast (fun j => if h : j = i then h.symm ▸ c.encode i a
      else m j h)) a
  refine ⟨d, ?_⟩
  intro x i
  have ht : (fun j => if h : j = i then
      h.symm ▸ c.encode i (observe K F (T.A i) x)
      else c.encode j (observe K F (T.A j) x)) =
      (fun j => c.encode j (observe K F (T.A j) x)) := by
    funext j
    split_ifs with h
    · subst j; rfl
    · rfl
  simpa only [d, ht] using c.zero_error x i

end Code

/-- Sufficiency of `eq:upload-only-feasibility`: broadcast the upload tuple.
The relay has no source input other than these uploads. -/
def codeOfUploadOnly {L : ℕ} {M : Three → Type*}
    (e : ∀ i, (T.A i →ₗ[K] (Fin L → K)) → M i)
    (d : ∀ i, (T.A i →ₗ[K] (Fin L → K)) →
      (∀ j, j ≠ i → M j) → (T.U i →ₗ[K] (Fin L → K)))
    (hd : ∀ (x : Source K F L) i,
      d i (observe K F (T.A i) x)
        (fun j _ => e j (observe K F (T.A j) x)) = observe K F (T.U i) x) :
    T.Code L M (∀ i, M i) where
  encode := e
  broadcast := id
  decode := fun i m a => d i a (fun j _ => m j)
  zero_error := hd

variable [Finite K] [FiniteDimensional K F]

/-- Blocklength-L cost budgets, using canonical finite alphabets. Every
finite alphabet is equivalent to one of these `Fin` types. -/
def achievableAt [Finite K] [FiniteDimensional K F] (L : ℕ) : Set (ℝ × ℝ) :=
  {b | 0 < L ∧ 0 ≤ b.1 ∧ 0 ≤ b.2 ∧
    ∃ (m : Three → ℕ) (s : ℕ) (c : T.Code L (fun i => Fin (m i)) (Fin s)),
      c.uploadCost ≤ b.1 ∧ c.broadcastCost ≤ b.2}

/-- The closed regularized cost region, `eq:regularized-region`. -/
def costRegion : Set (ℝ × ℝ) := closure (⋃ L, T.achievableAt L)

/-- Optimal total upload with unconstrained broadcast, `eq:ustar-definition`. -/
noncomputable def uploadOptimum : ℝ :=
  sInf {u : ℝ | ∃ d : ℝ, 0 ≤ d ∧ (u, d) ∈ T.costRegion}

/-- Budgets are upward closed at each fixed blocklength. -/
theorem achievableAt_mono {L : ℕ} {b b' : ℝ × ℝ}
    (hb : b ∈ T.achievableAt L) (hu : b.1 ≤ b'.1) (hd : b.2 ≤ b'.2) :
    b' ∈ T.achievableAt L := by
  rcases hb with ⟨hL, hU, hD, m, s, c, hcu, hcd⟩
  exact ⟨hL, hU.trans hu, hD.trans hd, m, s, c, hcu.trans hu, hcd.trans hd⟩

end Task
end UploadBroadcast
