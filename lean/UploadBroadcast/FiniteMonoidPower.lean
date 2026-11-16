import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.WLOG

namespace UploadBroadcast.FiniteMonoidPower

/-- Every element of a finite monoid has a positive idempotent power. -/
theorem exists_pos_pow_add_eq {M : Type*} [Monoid M] [Finite M] (a : M) :
    ∃ n : ℕ, 0 < n ∧ a ^ (n + n) = a ^ n := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)
  wlog hlt : i < j generalizing i j
  · exact this j i (Ne.symm hij) heq.symm (by omega)
  let d := j - i
  have hd : 0 < d := by dsimp [d]; omega
  have hbase : a ^ (i + d) = a ^ i := by
    have : i + d = j := by dsimp [d]; omega
    rw [this]
    exact heq.symm
  have hperiod (t : ℕ) (ht : i ≤ t) : a ^ (t + d) = a ^ t := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    calc
      a ^ (i + s + d) = a ^ (i + d + s) := by congr 1; omega
      _ = a ^ (i + d) * a ^ s := pow_add _ _ _
      _ = a ^ i * a ^ s := by rw [hbase]
      _ = a ^ (i + s) := (pow_add _ _ _).symm
  let n := (i + 1) * d
  have hn : 0 < n := Nat.mul_pos (by omega) hd
  have hin : i ≤ n := by dsimp [n]; nlinarith
  have hmulti (k : ℕ) : a ^ (n + k * d) = a ^ n := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc, hperiod (n + k * d) (by omega)]
      exact ih
  exact ⟨n, hn, hmulti (i + 1)⟩

end UploadBroadcast.FiniteMonoidPower
