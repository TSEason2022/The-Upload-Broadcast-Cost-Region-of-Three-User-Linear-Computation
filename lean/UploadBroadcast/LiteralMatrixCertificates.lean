import UploadBroadcast.NonzeroFamilyRanks
import Mathlib.Data.Matrix.Rank

/-! Small exact matrix certificates for literal source coordinates.
Every displayed integer equality is checked by Lean's kernel and then
transported by the integer ring homomorphism to an arbitrary field. -/
namespace UploadBroadcast.LiteralMatrixCertificates
open Matrix Module
variable {K : Type*} [Field K]

abbrev castMatrix {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin m) (Fin n) K := M.map (Int.castRingHom K)

/-- A factorization bounds rank above, and a split unit minor bounds it below. -/
theorem rank_certificate {m n r : ℕ} (M : Matrix (Fin m) (Fin n) K)
    (X : Matrix (Fin m) (Fin r) K) (Y : Matrix (Fin r) (Fin n) K)
    (L : Matrix (Fin r) (Fin m) K) (R : Matrix (Fin n) (Fin r) K)
    (hfac : X * Y = M) (hminor : L * M * R = 1) : M.rank = r := by
  apply Nat.le_antisymm
  · rw [← hfac]
    exact (rank_mul_le_left X Y).trans (rank_le_width X)
  · have h1 := rank_mul_le_left (L * M) R
    have h2 := rank_mul_le_right L M
    rw [hminor, rank_one, Fintype.card_fin] at h1
    exact h1.trans h2

/-- Integer certificates prove the same rank simultaneously in every characteristic. -/
theorem rank_int_certificate {m n r : ℕ} (M : Matrix (Fin m) (Fin n) ℤ)
    (X : Matrix (Fin m) (Fin r) ℤ) (Y : Matrix (Fin r) (Fin n) ℤ)
    (L : Matrix (Fin r) (Fin m) ℤ) (R : Matrix (Fin n) (Fin r) ℤ)
    (hfac : X * Y = M) (hminor : L * M * R = 1) :
    (castMatrix M : Matrix (Fin m) (Fin n) K).rank = r := by
  apply rank_certificate _ (castMatrix X) (castMatrix Y) (castMatrix L) (castMatrix R)
  · simpa only [castMatrix, ← Matrix.map_mul] using congrArg (fun M => M.map (Int.castRingHom K)) hfac
  · simpa only [castMatrix, ← Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using
      congrArg (fun M => M.map (Int.castRingHom K)) hminor

/-- The literal columns in the manuscript, interpreted in an arbitrary field. -/
def columns {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) : Submodule K (Fin m → K) :=
  LinearMap.range (castMatrix M).mulVecLin

/-- The common kernel of the literal integer functionals. -/
def kernel {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) : Submodule K (Fin n → K) :=
  LinearMap.ker (castMatrix M).mulVecLin

lemma columns_eq_span {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) :
    columns (K := K) M = Submodule.span K (Set.range (castMatrix M).col) :=
  Matrix.range_mulVecLin _

lemma columns_finrank {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) :
    finrank K (columns (K := K) M) = (castMatrix M : Matrix (Fin m) (Fin n) K).rank := rfl

lemma kernel_finrank {m n r : ℕ} (M : Matrix (Fin m) (Fin n) ℤ)
    (h : (castMatrix M : Matrix (Fin m) (Fin n) K).rank = r) :
    finrank K (kernel (K := K) M) = n-r := by
  have hh := LinearMap.finrank_range_add_finrank_ker (castMatrix M : Matrix (Fin m) (Fin n) K).mulVecLin
  change (castMatrix M : Matrix (Fin m) (Fin n) K).rank +
    finrank K (kernel (K := K) M) = finrank K (Fin n → K) at hh
  rw [h, finrank_pi, Fintype.card_fin] at hh
  omega

/-- Vertical concatenation of two lists of constraints. -/
def stack {a b n : ℕ} (M : Matrix (Fin a) (Fin n) ℤ)
    (N : Matrix (Fin b) (Fin n) ℤ) : Matrix (Fin (a+b)) (Fin n) ℤ := Fin.append M N

lemma kernel_stack {a b n : ℕ} (M : Matrix (Fin a) (Fin n) ℤ)
    (N : Matrix (Fin b) (Fin n) ℤ) :
    kernel (K := K) (stack M N) = kernel M ⊓ kernel N := by
  ext v
  simp only [kernel, LinearMap.mem_ker, Submodule.mem_inf]
  constructor
  · intro h
    constructor
    · ext i
      simpa [castMatrix, stack, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using congrFun h (Fin.castAdd b i)
    · ext i
      simpa [castMatrix, stack, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using congrFun h (Fin.natAdd a i)
  · rintro ⟨hm, hn⟩
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [castMatrix, stack, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using congrFun hm j
    · simpa [castMatrix, stack, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using congrFun hn j

lemma columns_eq_kernel {n a b r : ℕ} (M : Matrix (Fin n) (Fin a) ℤ)
    (N : Matrix (Fin b) (Fin n) ℤ) (hz : N * M = 0)
    (hM : (castMatrix M : Matrix (Fin n) (Fin a) K).rank = a)
    (hN : (castMatrix N : Matrix (Fin b) (Fin n) K).rank = r)
    (hab : a+r=n) : columns (K := K) M = kernel N := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply LinearMap.range_le_ker_iff.mpr
    rw [← Matrix.mulVecLin_mul]
    have hh : (castMatrix N : Matrix (Fin b) (Fin n) K) * (castMatrix M : Matrix (Fin n) (Fin a) K) = 0 := by
      rw [castMatrix, castMatrix, ← Matrix.map_mul, hz]
      exact Matrix.map_zero _ (map_zero _)
    rw [hh, Matrix.mulVecLin_zero]
  · rw [columns_finrank, hM, kernel_finrank N hN]
    omega

lemma inf_finrank {a b n r : ℕ} (M : Matrix (Fin a) (Fin n) ℤ)
    (N : Matrix (Fin b) (Fin n) ℤ)
    (h : (castMatrix (stack M N) : Matrix (Fin (a+b)) (Fin n) K).rank = r) :
    finrank K ↥(kernel (K := K) M ⊓ kernel N) = n-r := by
  rw [← kernel_stack]
  exact kernel_finrank _ h


/-- Horizontal concatenation of literal column lists. -/
def joinColumns {n a b : ℕ} (M : Matrix (Fin n) (Fin a) ℤ)
    (N : Matrix (Fin n) (Fin b) ℤ) : Matrix (Fin n) (Fin (a+b)) ℤ :=
  fun i => Fin.append (M i) (N i)

lemma columns_join {n a b : ℕ} (M : Matrix (Fin n) (Fin a) ℤ)
    (N : Matrix (Fin n) (Fin b) ℤ) :
    columns (K := K) (joinColumns M N) = columns M ⊔ columns N := by
  simp only [columns_eq_span, ← Submodule.span_union]
  congr 1
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Or.inl ⟨j, by ext k; simp [castMatrix, joinColumns, Matrix.col]⟩
    · exact Or.inr ⟨j, by ext k; simp [castMatrix, joinColumns, Matrix.col]⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd b j, by ext k; simp [castMatrix, joinColumns, Matrix.col]⟩
    · exact ⟨Fin.natAdd a j, by ext k; simp [castMatrix, joinColumns, Matrix.col]⟩

lemma columns_le_columns {n a b : ℕ} (M : Matrix (Fin n) (Fin a) ℤ)
    (N : Matrix (Fin n) (Fin b) ℤ) (C : Matrix (Fin b) (Fin a) ℤ)
    (h : N*C=M) : columns (K := K) M ≤ columns N := by
  have hh : (castMatrix M : Matrix (Fin n) (Fin a) K).mulVecLin =
      (castMatrix N : Matrix (Fin n) (Fin b) K).mulVecLin.comp
      (castMatrix C : Matrix (Fin b) (Fin a) K).mulVecLin := by
    rw [← Matrix.mulVecLin_mul]
    congr 1
    rw [castMatrix, castMatrix, castMatrix, ← Matrix.map_mul, h]
  change LinearMap.range _ ≤ LinearMap.range _
  rw [hh]
  exact LinearMap.range_comp_le_range _ _

lemma columns_eq_top {n a : ℕ} (M : Matrix (Fin n) (Fin a) ℤ)
    (h : (castMatrix M : Matrix (Fin n) (Fin a) K).rank = n) :
    columns (K := K) M = ⊤ := by
  apply Submodule.eq_of_le_of_finrank_eq le_top
  simpa only [columns_finrank, finrank_top, finrank_pi, Fintype.card_fin] using h


section Ambient
variable {F : Type*} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
open NonzeroDefectProfile IntersectionProbes
theorem rankConditions_in_ambient
    (T : UploadBroadcast.Task K F) (V : Submodule K F) (a u : Three → ℕ)
    (hV : ∀ i, T.U i ≤ V)
    (ha : ∀ i, finrank K ↥(T.A i) = a i)
    (hu : ∀ i, finrank K ↥(T.U i) = u i)
    (hpair : ∀ i j, i ≠ j →
      finrank K ↥(T.U i ⊓ T.U j) + finrank K V = u i + u j)
    (htriple : finrank K ↥(T.U 0 ⊓ T.U 1 ⊓ T.U 2) + 2 * finrank K V =
      u 0 + u 1 + u 2)
    (has : ∀ i j, i ≠ j → finrank K ↥(T.A j ⊓ T.U i) = a j + u i - finrank K V)
    (hat : ∀ i, finrank K ↥((T.U 0 ⊓ T.U 1 ⊓ T.U 2) ⊓ T.A i) = 0) :
    RankConditions T V a u := by
  have hpairSpan (i j : Three) (hij : i ≠ j) : T.U i ⊔ T.U j = V := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le (hV i) (hV j))
    have hh := Submodule.finrank_sup_add_finrank_inf_eq (T.U i) (T.U j)
    have hp := hpair i j hij
    simp only [hu, finrank_top] at *
    omega
  have hjoint (i j k : Three) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      (T.U i ⊓ T.U j) ⊔ T.U k = V := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le (inf_le_left.trans (hV i)) (hV k))
    have hh := Submodule.finrank_sup_add_finrank_inf_eq (T.U i ⊓ T.U j) (T.U k)
    have he : (T.U i ⊓ T.U j) ⊓ T.U k = (T.U 0 ⊓ T.U 1) ⊓ T.U 2 := by
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        simp_all only [ne_eq, not_true_eq_false, Submodule.mem_inf] <;>
        ext x <;> simp only [Submodule.mem_inf] <;> tauto
    rw [he, hu] at hh
    have hp := hpair i j hij
    have hsum : u 0 + u 1 + u 2 = u i + u j + u k := by
      have he := sum_three_perm u i j k hij hik hjk
      simpa [Fin.sum_univ_succ, add_assoc] using he
    omega
  refine ⟨ha,hu,hV,hpairSpan,?_,?_,?_⟩
  · intro i j k hij hik hjk
    exact pair_intersections_span_of_join _ _ _ _ (hV i) (hjoint i j k hij hik hjk)
  · intro i j hij
    have hc := condRank_add_intersection (T.U i ⊓ T.U j) (T.A j)
    have he : T.A j ⊓ (T.U i ⊓ T.U j) = T.A j ⊓ T.U i := by
      ext x
      exact ⟨fun h => ⟨h.1,h.2.1⟩, fun h => ⟨h.1,h.2,T.side_le_signal j h.1⟩⟩
    rw [he] at hc
    have hp := hpair i j hij
    have hs := has i j hij
    have haj : a j ≤ u j := by
      simpa only [ha,hu] using Submodule.finrank_mono (T.side_le_signal j)
    omega
  · intro i
    have hc := condRank_add_intersection (T.U 0 ⊓ T.U 1 ⊓ T.U 2) (T.A i)
    rw [inf_comm (T.A i) (T.U 0 ⊓ T.U 1 ⊓ T.U 2), hat i, add_zero] at hc
    omega

end Ambient
end UploadBroadcast.LiteralMatrixCertificates
