import UploadBroadcast.Profile
import UploadBroadcast.RankLoss
import Mathlib.Tactic.Linarith

/-! The lattice-entropy core of the nonlinear LCBC converse. The hypotheses
are local entropy laws, never the target broadcast bound.

Source: Yao--Jafar, *The Capacity of 3 User Linear Computation Broadcast*,
arXiv:2206.10049v3, Sections 7.1 and 7.2.2, equations (29)--(36) and
(51)--(64), https://arxiv.org/html/2206.10049v3 .
The concrete Shannon construction is kept separate from this reusable core.
-/
namespace UploadBroadcast.LCBCConverse
open Module
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- `joint V` represents H(S, XᵀV), and `cost` represents H(S), in
q-ary units per source instance. This interface does not require uploads. -/
structure BroadcastEntropy where
  joint : Submodule K F → ℝ
  cost : ℝ
  mono : Monotone joint
  submod : ∀ V W, joint (V ⊔ W) + joint (V ⊓ W) ≤ joint V + joint W
  rank_le : ∀ (V : Submodule K F), (finrank K V : ℝ) ≤ joint V
  upper : ∀ V, joint V ≤ cost + finrank K V
  increment : ∀ V W, V ≤ W → joint W - joint V ≤
    (finrank K W : ℝ) - finrank K V

variable (h : BroadcastEntropy (K := K) (F := F))

omit [FiniteDimensional K F] in
lemma absorption (C A : Submodule K F) :
    (finrank K ↥(C ⊓ A) : ℝ) ≤ h.joint C + finrank K A - h.joint A := by
  have h₁ := h.increment (C ⊓ A) A inf_le_right
  have h₂ := h.mono (show C ⊓ A ≤ C from inf_le_left)
  linarith

omit [FiniteDimensional K F] in
/-- The five functional-submodularity steps of Yao--Jafar (54)--(55). -/
lemma five_submod (U V W : Submodule K F) :
    h.joint (U ⊓ V ⊓ W) + h.joint ((U ⊓ V) ⊔ (U ⊓ W)) +
      h.joint (W ⊓ (U ⊔ V)) + h.joint (V ⊓ (U ⊔ W)) +
      2 * h.joint (U ⊔ V ⊔ W) ≤ 2 * (h.joint U + h.joint V + h.joint W) := by
  have h₁ := h.submod U V
  have h₂ := h.submod U W
  have h₃ := h.submod (U ⊓ V) (U ⊓ W)
  have h₄ := h.submod (U ⊔ V) W
  have h₅ := h.submod (U ⊔ W) V
  have he : (U ⊓ V) ⊓ (U ⊓ W) = U ⊓ V ⊓ W := by
    ext x; simp only [Submodule.mem_inf]; tauto
  have he' : U ⊔ W ⊔ V = U ⊔ V ⊔ W := by rw [sup_assoc, sup_comm W V, ← sup_assoc]
  rw [he] at h₃
  rw [he', inf_comm (U ⊔ W) V] at h₅
  rw [inf_comm (U ⊔ V) W] at h₄
  linarith

omit [FiniteDimensional K F] in
/-- The entropy inequality before conversion of four intersection ranks to
conditional ranks. `E` can be any one of the three side-information spaces. -/
theorem second_intersection_bound (A B C U V W E : Submodule K F)
    (d₁ : h.joint A = h.joint U) (d₂ : h.joint B = h.joint V)
    (d₃ : h.joint C = h.joint W) (he : E = A ∨ E = B ∨ E = C) :
    2 * (finrank K ↥(U ⊔ V ⊔ W) : ℝ) +
      finrank K ↥((U ⊓ V ⊓ W) ⊓ E) +
      finrank K ↥(((U ⊓ V) ⊔ (U ⊓ W)) ⊓ A) +
      finrank K ↥((W ⊓ (U ⊔ V)) ⊓ C) +
      finrank K ↥((V ⊓ (U ⊔ W)) ⊓ B) -
      2 * ((finrank K A : ℝ) + finrank K B + finrank K C) ≤ 2 * h.cost := by
  have hs := five_submod h U V W
  have ha := absorption h ((U ⊓ V) ⊔ (U ⊓ W)) A
  have hb := absorption h (V ⊓ (U ⊔ W)) B
  have hc := absorption h (W ⊓ (U ⊔ V)) C
  have ht := absorption h (U ⊓ V ⊓ W) E
  have hr := h.rank_le (U ⊔ V ⊔ W)
  have hA := h.upper A
  have hB := h.upper B
  have hC := h.upper C
  rcases he with rfl | rfl | rfl <;> linarith

lemma rank_modular (V W : Submodule K F) :
    (finrank K ↥(V ⊔ W) : ℝ) + finrank K ↥(V ⊓ W) =
      finrank K V + finrank K W := by
  exact_mod_cast Submodule.finrank_sup_add_finrank_inf_eq V W

lemma intersection_rank (V A : Submodule K F) :
    (finrank K ↥(V ⊓ A) : ℝ) = finrank K V - condRank V A := by
  have he := condRank_add_intersection V A
  rw [inf_comm A V] at he
  have he' : (condRank V A : ℝ) + finrank K ↥(V ⊓ A) = finrank K V := by
    exact_mod_cast he
  linarith

/-- Full second-family inequality, for arbitrary side-information subspaces.
There is no global upload feasibility assumption. -/
theorem second_bound (A B C U V W E : Submodule K F)
    (d₁ : h.joint A = h.joint U) (d₂ : h.joint B = h.joint V)
    (d₃ : h.joint C = h.joint W) (he : E = A ∨ E = B ∨ E = C) :
    (finrank K U : ℝ) + finrank K V + finrank K W -
      (finrank K A + finrank K B + finrank K C) -
      ((condRank (U ⊓ V ⊓ W) E : ℝ) +
        condRank ((U ⊓ V) ⊔ (U ⊓ W)) A +
        condRank (W ⊓ (U ⊔ V)) C + condRank (V ⊓ (U ⊔ W)) B) / 2 ≤ h.cost := by
  have hs := second_intersection_bound h A B C U V W E d₁ d₂ d₃ he
  rw [intersection_rank (U ⊓ V ⊓ W) E, intersection_rank ((U ⊓ V) ⊔ (U ⊓ W)) A, intersection_rank (W ⊓ (U ⊔ V)) C, intersection_rank (V ⊓ (U ⊔ W)) B] at hs
  have h₁ := rank_modular U V
  have h₂ := rank_modular U W
  have h₃ := rank_modular (U ⊓ V) (U ⊓ W)
  have h₄ := rank_modular (U ⊔ V) W
  have h₅ := rank_modular (U ⊔ W) V
  have heq : (U ⊓ V) ⊓ (U ⊓ W) = U ⊓ V ⊓ W := by
    ext x; simp only [Submodule.mem_inf]; tauto
  rw [heq] at h₃
  rw [sup_assoc, sup_comm W V, ← sup_assoc, inf_comm (U ⊔ W) V] at h₅
  rw [inf_comm (U ⊔ V) W] at h₄
  linarith

omit [FiniteDimensional K F] in
lemma decode_sup (A U Z : Submodule K F) (ha : A ≤ U)
    (hd : h.joint A = h.joint U) : h.joint (A ⊔ Z) = h.joint (U ⊔ Z) := by
  have hs := h.submod U (A ⊔ Z)
  have hi := h.mono (show A ≤ U ⊓ (A ⊔ Z) from le_inf ha le_sup_left)
  have hm := h.mono (sup_le_sup_right ha Z)
  rw [← sup_assoc, sup_eq_left.mpr ha] at hs
  linarith

omit [FiniteDimensional K F] in
/-- The sequential conditioning argument, in its telescoping rank form. -/
theorem first_chain (A B C U V W : Submodule K F)
    (_ha : A ≤ U) (hb : B ≤ V) (hc : C ≤ W)
    (d₁ : h.joint A = h.joint U) (d₂ : h.joint B = h.joint V)
    (d₃ : h.joint C = h.joint W) :
    (finrank K U : ℝ) - finrank K A +
      (finrank K ↥(U ⊔ V) - finrank K ↥(U ⊔ B)) +
      (finrank K ↥(U ⊔ V ⊔ W) - finrank K ↥(U ⊔ V ⊔ C)) ≤ h.cost := by
  have h₁ := h.upper A
  have h₂ := h.increment U (U ⊔ B) le_sup_left
  have h₃ := h.increment (U ⊔ V) (U ⊔ V ⊔ C) le_sup_left
  have h₄ := h.rank_le (U ⊔ V ⊔ W)
  have hd₂ := decode_sup h B V U hb d₂
  have hd₃ := decode_sup h C W (U ⊔ V) hc d₃
  rw [sup_comm B U, sup_comm V U] at hd₂
  rw [sup_comm C (U ⊔ V), sup_comm W (U ⊔ V)] at hd₃
  linarith

lemma residual_rank (A U Z : Submodule K F) (ha : A ≤ U) :
    (finrank K ↥(Z ⊔ U) : ℝ) - finrank K ↥(Z ⊔ A) =
      finrank K U - finrank K A - condRank (U ⊓ Z) A := by
  have h₁ := rank_modular Z U
  have h₂ := rank_modular Z A
  have h₃ := intersection_rank (U ⊓ Z) A
  have he : (U ⊓ Z) ⊓ A = Z ⊓ A := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    · exact le_inf (le_inf (inf_le_right.trans ha) inf_le_left) inf_le_right
  rw [he] at h₃
  rw [inf_comm Z U] at h₁
  linarith

/-- All first-family bounds follow by specializing the ordered triple. -/
theorem first_bound (A B C U V W : Submodule K F)
    (ha : A ≤ U) (hb : B ≤ V) (hc : C ≤ W)
    (d₁ : h.joint A = h.joint U) (d₂ : h.joint B = h.joint V)
    (d₃ : h.joint C = h.joint W) :
    (finrank K U : ℝ) + finrank K V + finrank K W -
      (finrank K A + finrank K B + finrank K C) -
      condRank (U ⊓ V) B - condRank (W ⊓ (U ⊔ V)) C ≤ h.cost := by
  have hs := first_chain h A B C U V W ha hb hc d₁ d₂ d₃
  rw [residual_rank B V U hb, residual_rank C W (U ⊔ V) hc, inf_comm V U] at hs
  linarith

lemma totalDemand_real (T : Task K F) :
    (Profile.totalDemand T : ℝ) =
      (finrank K (T.U 0) : ℝ) + finrank K (T.U 1) + finrank K (T.U 2) -
      (finrank K (T.A 0) + finrank K (T.A 1) + finrank K (T.A 2)) := by
  unfold Profile.totalDemand
  rw [Nat.cast_sum]
  simp_rw [Nat.cast_sub (Submodule.finrank_mono (T.side_le_signal _))]
  simp [Three, Fin.sum_univ_succ]
  ring

/-- The six ordered first-family profile entries. -/
theorem firstEntry_le (T : Task K F)
    (hd : ∀ i, h.joint (T.A i) = h.joint (T.U i)) (r : Fin 6) :
    Profile.entry T (.inl r) ≤ h.cost := by
  let i := (Profile.firstOrder r).1
  let j := (Profile.firstOrder r).2.1
  let k := (Profile.firstOrder r).2.2
  have hs := first_bound h (T.A i) (T.A j) (T.A k) (T.U i) (T.U j) (T.U k)
    (T.side_le_signal i) (T.side_le_signal j) (T.side_le_signal k) (hd i) (hd j) (hd k)
  change Profile.firstEntry T i j k ≤ h.cost
  unfold Profile.firstEntry
  rw [totalDemand_real]
  fin_cases r <;> dsimp [i, j, k, Profile.firstOrder] at hs ⊢ <;> linarith

/-- The nine cyclic second-family profile entries. -/
theorem secondEntry_le (T : Task K F)
    (hd : ∀ i, h.joint (T.A i) = h.joint (T.U i)) (i ell : Three) :
    Profile.entry T (.inr (i,ell)) ≤ h.cost := by
  have he : T.A ell = T.A i ∨ T.A ell = T.A (i+1) ∨ T.A ell = T.A (i+2) := by
    fin_cases i <;> fin_cases ell <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
  have hs := second_bound h (T.A i) (T.A (i+1)) (T.A (i+2))
    (T.U i) (T.U (i+1)) (T.U (i+2)) (T.A ell) (hd i) (hd (i+1)) (hd (i+2)) he
  have htr : T.U i ⊓ T.U (i+1) ⊓ T.U (i+2) = T.U 0 ⊓ T.U 1 ⊓ T.U 2 := by
    fin_cases i <;> ext x <;> dsimp <;> simp only [Submodule.mem_inf] <;> tauto
  rw [htr] at hs
  change Profile.secondEntry T i (i+1) (i+2) ell ≤ h.cost
  unfold Profile.secondEntry
  rw [totalDemand_real]
  fin_cases i <;> dsimp at hs ⊢
  all_goals simp only [inf_assoc, inf_left_comm, inf_comm] at hs ⊢
  all_goals linarith

/-- The exact maximum of all fifteen entries is a broadcast lower bound,
provided the local entropy laws and the three decoder equalities hold. -/
theorem rankBound_le (T : Task K F)
    (hd : ∀ i, h.joint (T.A i) = h.joint (T.U i)) : Profile.rankBound T ≤ h.cost := by
  apply Finset.sup'_le
  intro r _
  cases r with
  | inl r => exact firstEntry_le h T hd r
  | inr r => exact secondEntry_le h T hd r.1 r.2

end UploadBroadcast.LCBCConverse


