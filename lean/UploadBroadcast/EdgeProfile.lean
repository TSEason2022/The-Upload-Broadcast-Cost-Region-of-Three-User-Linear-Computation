import UploadBroadcast.ProfileTransport
import UploadBroadcast.EdgeExtraction
import UploadBroadcast.BinaryCommon
import Mathlib.Tactic.Linarith

namespace UploadBroadcast.EdgeProfile
open Module
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

theorem condRank_real (P A : Submodule K F) :
    (condRank P A : ℝ) = (finrank K P : ℝ) - finrank K ↥(P ⊓ A) := by
  rw [condRank_eq_finrank_sub_inf, Nat.cast_sub (Submodule.finrank_mono inf_le_left)]

theorem condRank_chain (X Y A : Submodule K F) :
    (condRank (X ⊔ Y) A : ℝ) - condRank X A = condRank Y (A ⊔ X) := by
  unfold condRank
  rw [Nat.cast_sub (Submodule.finrank_mono le_sup_left),
    Nat.cast_sub (Submodule.finrank_mono le_sup_left),
    Nat.cast_sub (Submodule.finrank_mono le_sup_left)]
  rw [sup_assoc]
  ring

/-- Exact defect term behind edge extraction, as the dimension of a genuine quotient. -/
theorem rank_interaction (R S B C : Submodule K F) (hSR : S ≤ R) (hSB : S ≤ B) :
    (condRank S C : ℝ) + condRank R B - condRank R C =
      condRank (R ⊓ C) B - condRank (R ⊓ B) (S ⊔ ((R ⊓ C) ⊓ B)) := by
  have hD : S ⊔ ((R ⊓ C) ⊓ B) ≤ R ⊓ B :=
    sup_le (le_inf hSR hSB) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have hI : S ⊓ ((R ⊓ C) ⊓ B) = S ⊓ C := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_right))
    · exact le_inf inf_le_left (le_inf (le_inf (inf_le_left.trans hSR) inf_le_right)
        (inf_le_left.trans hSB))
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq S ((R ⊓ C) ⊓ B)
  rw [hI] at hdim
  have hd : (finrank K ↥(S ⊔ ((R ⊓ C) ⊓ B)) : ℝ) + finrank K ↥(S ⊓ C) =
      finrank K S + finrank K ↥((R ⊓ C) ⊓ B) := by exact_mod_cast hdim
  simp only [condRank_real]
  rw [show (R ⊓ B) ⊓ (S ⊔ ((R ⊓ C) ⊓ B)) = S ⊔ ((R ⊓ C) ⊓ B) from inf_eq_right.mpr hD]
  linarith

/-- Algebraic edge price before selecting an edge complement. -/
theorem edge_price_identity (T : Task K F) (i j k : Three)
    (ht : T.U 0 ⊓ T.U 1 ⊓ T.U 2 = T.U i ⊓ T.U j ⊓ T.U k) :
    Profile.firstEntry T i j k + Profile.firstEntry T j k i -
      2 * Profile.secondEntry T j i k k =
    (condRank (T.A k ⊓ T.U j) (T.A j ⊔ (T.U i ⊓ T.U j)) : ℝ) -
      condRank ((T.U j ⊓ T.U k) ⊓ (T.A j ⊔ (T.U i ⊓ T.U j)))
        ((T.U i ⊓ T.U j ⊓ T.U k) ⊔ (T.A k ⊓ (T.A j ⊔ (T.U i ⊓ T.U j)))) := by
  let B := T.A j ⊔ (T.U i ⊓ T.U j)
  have hB : B ≤ T.U j := sup_le (T.side_le_signal j) inf_le_right
  have hN : (T.U j ⊓ T.U k) ⊓ T.A k = T.A k ⊓ T.U j := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans inf_le_left)
    · exact le_inf (le_inf inf_le_right (inf_le_left.trans (T.side_le_signal k))) inf_le_left
  have hNB : (T.A k ⊓ T.U j) ⊓ B = T.A k ⊓ B := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans hB)) inf_le_right
  have h := rank_interaction (T.U j ⊓ T.U k) (T.U i ⊓ T.U j ⊓ T.U k) B (T.A k)
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    (inf_le_left.trans le_sup_right)
  rw [hN,hNB] at h
  have hc := condRank_chain (T.U i ⊓ T.U j) (T.U j ⊓ T.U k) (T.A j)
  change (condRank ((T.U i ⊓ T.U j) ⊔ (T.U j ⊓ T.U k)) (T.A j) : ℝ) -
    condRank (T.U i ⊓ T.U j) (T.A j) = condRank (T.U j ⊓ T.U k) B at hc
  unfold Profile.firstEntry Profile.secondEntry
  rw [ht]
  rw [inf_comm (T.U j) (T.U i), sup_comm (T.U j) (T.U i)]
  change _ = (condRank (T.A k ⊓ T.U j) B : ℝ) -
    condRank ((T.U j ⊓ T.U k) ⊓ B) ((T.U i ⊓ T.U j ⊓ T.U k) ⊔ (T.A k ⊓ B))
  linarith

omit [FiniteDimensional K F] in
theorem triple_inf_permutation (T : Task K F) (p : Equiv.Perm Three) :
    T.U 0 ⊓ T.U 1 ⊓ T.U 2 = T.U (p 0) ⊓ T.U (p 1) ⊓ T.U (p 2) := by
  rw [← Profile.three_iInf T.U, ← Profile.three_iInf (fun i => T.U (p i)), Equiv.iInf_comp]

/-- Every oriented edge price is bounded by the actual extractable multiplicity. -/
theorem edge_price_le (T : Task K F) (p : Equiv.Perm Three) :
    Profile.firstEntry T (p 0) (p 1) (p 2) +
      Profile.firstEntry T (p 1) (p 2) (p 0) -
      2 * Profile.secondEntry T (p 1) (p 0) (p 2) (p 2) ≤
    (condRank (T.A (p 2) ⊓ T.U (p 1))
      (T.A (p 1) ⊔ (T.U (p 0) ⊓ T.U (p 1))) : ℝ) := by
  rw [edge_price_identity T _ _ _ (triple_inf_permutation T p)]
  exact sub_le_self _ (Nat.cast_nonneg _)

/-- The subtracted conditional rank is literally the dimension of the paper quotient. -/
theorem edge_defect_dimension (T : Task K F) (i j k : Three) :
    condRank ((T.U j ⊓ T.U k) ⊓ (T.A j ⊔ (T.U i ⊓ T.U j)))
      ((T.U i ⊓ T.U j ⊓ T.U k) ⊔ (T.A k ⊓ (T.A j ⊔ (T.U i ⊓ T.U j)))) =
    finrank K ↥((T.U j ⊓ T.U k) ⊓ (T.A j ⊔ (T.U i ⊓ T.U j))) -
      finrank K ↥((T.U i ⊓ T.U j ⊓ T.U k) ⊔ (T.A k ⊓ (T.A j ⊔ (T.U i ⊓ T.U j)))) := by
  have hB : T.A j ⊔ (T.U i ⊓ T.U j) ≤ T.U j :=
    sup_le (T.side_le_signal j) inf_le_right
  have hD : (T.U i ⊓ T.U j ⊓ T.U k) ⊔ (T.A k ⊓ (T.A j ⊔ (T.U i ⊓ T.U j))) ≤
      (T.U j ⊓ T.U k) ⊓ (T.A j ⊔ (T.U i ⊓ T.U j)) := by
    apply sup_le
    · exact le_inf (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (inf_le_left.trans le_sup_right)
    · exact le_inf (le_inf (inf_le_right.trans hB)
        (inf_le_left.trans (T.side_le_signal k))) inf_le_right
  rw [condRank_eq_finrank_sub_inf, inf_eq_right.mpr hD]

/-- Identification with the maximum multiplicity constructed by stable projections. -/
theorem extractable_multiplicity (T : Task K F) (i j k : Three) :
    EdgeExtraction.multiplicity T i j k =
      condRank (T.A k ⊓ T.U j) (T.A j ⊔ (T.U i ⊓ T.U j)) := by
  rw [condRank_eq_finrank_sub_inf]
  rfl

theorem edge_price_le_extractable (T : Task K F) (p : Equiv.Perm Three) :
    Profile.firstEntry T (p 0) (p 1) (p 2) +
      Profile.firstEntry T (p 1) (p 2) (p 0) -
      2 * Profile.secondEntry T (p 1) (p 0) (p 2) (p 2) ≤
      (EdgeExtraction.multiplicity T (p 0) (p 1) (p 2) : ℝ) := by
  rw [extractable_multiplicity]
  exact edge_price_le T p

end UploadBroadcast.EdgeProfile
