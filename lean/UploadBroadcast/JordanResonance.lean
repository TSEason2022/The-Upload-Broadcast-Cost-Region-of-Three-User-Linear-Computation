import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring

/-! Concrete coefficient-coordinate resonant Jordan block over an arbitrary field.
The manuscript's source-coordinate block is the transpose of `shift`: take the
source block with ones below the diagonal, and h = e₀. Then hᵀ = `head`.
The parameter `n` here corresponds to manuscript block size n + 1.
-/
namespace UploadBroadcast.JordanResonance
variable (K : Type*) [Field K] (n : ℕ)
abbrev V := Fin (n + 1) → K

/-- Upper Jordan shift, with zero in the last coordinate. -/
def shift : V K n →ₗ[K] V K n where
  toFun w i := if h : i.val + 1 < n + 1 then w ⟨i.val + 1, h⟩ else 0
  map_add' x y := by ext i; dsimp; split <;> simp
  map_smul' a x := by ext i; dsimp; split <;> simp

def automorphism : V K n →ₗ[K] V K n := LinearMap.id + shift K n

def head : V K n →ₗ[K] K where
  toFun w := w 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem shift_last (w : V K n) : shift K n w (Fin.last n) = 0 := by
  simp [shift]

@[simp] theorem shift_castSucc (w : V K n) (i : Fin n) :
    shift K n w i.castSucc = w i.succ := by
  simp [shift, Nat.succ_lt_succ_iff, i.isLt]
  rfl

@[simp] theorem automorphism_apply (w : V K n) (i : Fin (n+1)) :
    automorphism K n w i = w i + shift K n w i := rfl

@[simp] theorem head_apply (w : V K n) : head K n w = w 0 := rfl

theorem automorphism_injective : Function.Injective (automorphism K n) := by
  intro x y h
  funext i
  induction i using Fin.reverseInduction with
  | last => simpa using congrFun h (Fin.last n)
  | cast i ih =>
    have hi := congrFun h i.castSucc
    simpa [ih] using hi

theorem automorphism_surjective : Function.Surjective (automorphism K n) :=
  LinearMap.injective_iff_surjective.mp (automorphism_injective K n)

noncomputable def equivalence : V K n ≃ₗ[K] V K n :=
  LinearEquiv.ofBijective (automorphism K n)
    ⟨automorphism_injective K n, automorphism_surjective K n⟩

theorem head_surjective : Function.Surjective (head K n) := by
  intro a
  exact ⟨fun _ => a, rfl⟩

theorem fixed_head_eq_zero (w : V K n)
    (hw : automorphism K n w = w) (hh : head K n w = 0) : w = 0 := by
  funext i
  refine Fin.cases hh (fun j => ?_) i
  have hj := congrFun hw j.castSucc
  simpa using hj

/-- Source-coordinate Jordan block, transpose of the coefficient shift. -/
def sourceShift : V K n →ₗ[K] V K n where
  toFun w := Fin.cases 0 (fun i => w i.castSucc)
  map_add' x y := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' a x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rfl

/-- The manuscript's chosen column h and normalized left-kernel row. -/
def sourceColumn : V K n := Fin.cases 1 (fun _ => 0)

theorem head_sourceShift (w : V K n) : head K n (sourceShift K n w) = 0 := rfl

theorem head_sourceColumn : head K n (sourceColumn K n) = 1 := rfl

theorem sourceColumn_not_mem_range : sourceColumn K n ∉ LinearMap.range (sourceShift K n) := by
  rintro ⟨w, hw⟩
  have he := congrArg (head K n) hw
  change (0 : K) = 1 at he
  exact zero_ne_one he

/-- The pairing verifies the actual transpose relation, independently of coordinates. -/
theorem transpose_pairing (x y : V K n) :
    (∑ i, x i * sourceShift K n y i) = ∑ i, shift K n x i * y i := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [sourceShift, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.cases_zero, Fin.cases_succ, mul_zero, zero_add, shift_last,
    zero_mul, add_zero, shift_castSucc]

theorem shift_power_vanish (k : ℕ) (w : V K n) (i : Fin (n+1))
    (hi : n + 1 ≤ i.val + k) : ((shift K n)^k) w i = 0 := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    rw [pow_succ']
    change shift K n (((shift K n)^k) w) i = 0
    dsimp [shift]
    split
    · apply ih
      simp only [Fin.val_mk]
      omega
    · rfl

theorem shift_nilpotent : (shift K n)^(n+1) = 0 := by
  apply LinearMap.ext
  intro w
  funext i
  exact shift_power_vanish K n (n+1) w i (by omega)

end UploadBroadcast.JordanResonance
