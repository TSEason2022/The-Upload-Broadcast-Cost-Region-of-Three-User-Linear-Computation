import Mathlib.LinearAlgebra.Dual.Lemmas
import UploadBroadcast.LinearAlgebra
import UploadBroadcast.AlignedRelation
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! The three-functional binary solvability criterion used in the separated
binary scalar-broadcast proof. -/
namespace UploadBroadcast

private theorem odd_three_bits (a b c : ZMod 2) (h : a + b + c ≠ 0) :
    (a=1 ∧ b=0 ∧ c=0) ∨ (a=0 ∧ b=1 ∧ c=0) ∨
    (a=0 ∧ b=0 ∧ c=1) ∨ (a=1 ∧ b=1 ∧ c=1) := by
  have all : ∀ a b c : ZMod 2, a+b+c ≠ 0 →
      (a=1 ∧ b=0 ∧ c=0) ∨ (a=0 ∧ b=1 ∧ c=0) ∨
      (a=0 ∧ b=0 ∧ c=1) ∨ (a=1 ∧ b=1 ∧ c=1) := by decide
  exact all a b c h

/-- Three nonzero binary linear forms simultaneously take value one unless
(and only unless) their sum is zero. -/
theorem binary_three_forms_ones
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (a b c : V →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hsum : a + b + c ≠ 0) :
    ∃ v, a v = 1 ∧ b v = 1 ∧ c v = 1 := by
  classical
  let L : V →ₗ[ZMod 2] (Fin 3 → ZMod 2) := LinearMap.pi ![a,b,c]
  let e0 : Fin 3 → ZMod 2 := ![1,0,0]
  let e1 : Fin 3 → ZMod 2 := ![0,1,0]
  let e2 : Fin 3 → ZMod 2 := ![0,0,1]
  let one : Fin 3 → ZMod 2 := ![1,1,1]
  have hmem : one ∈ LinearMap.range L := by
    by_contra hn
    obtain ⟨f,hf,hzero⟩ := (LinearMap.range L).exists_dual_map_eq_bot_of_nmem hn inferInstance
    have expansion (x : Fin 3 → ZMod 2) : f x = x 0 * f e0 + x 1 * f e1 + x 2 * f e2 := by
      have hx : x = x 0 • e0 + x 1 • e1 + x 2 • e2 := by
        ext i
        fin_cases i <;> simp [e0,e1,e2]
      conv_lhs => rw [hx, map_add, map_add, map_smul, map_smul, map_smul]
      rfl
    have hfodd : f e0 + f e1 + f e2 ≠ 0 := by
      rw [expansion one] at hf
      simpa [one] using hf
    have hv (v : V) : a v * f e0 + b v * f e1 + c v * f e2 = 0 := by
      have hm : f (L v) ∈ (LinearMap.range L).map f :=
        ⟨L v, ⟨v,rfl⟩, rfl⟩
      rw [hzero] at hm
      have hz : f (L v) = 0 := hm
      rw [expansion (L v)] at hz
      simpa [L] using hz
    rcases odd_three_bits (f e0) (f e1) (f e2) hfodd with
      ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩
    · apply ha
      ext v
      simpa [h0,h1,h2] using hv v
    · apply hb
      ext v
      simpa [h0,h1,h2] using hv v
    · apply hc
      ext v
      simpa [h0,h1,h2] using hv v
    · apply hsum
      ext v
      simpa [h0,h1,h2] using hv v
  obtain ⟨v,hv⟩ := hmem
  refine ⟨v, ?_, ?_, ?_⟩
  · exact congrFun hv 0
  · exact congrFun hv 1
  · exact congrFun hv 2

/-- The aligned-column step of the binary broadcast construction, including
proof that the possible odd dependency is excluded by the actual side spaces.
The relation is u₁+u₂+u₃=0, equivalent to u₁+u₂=u₃ in characteristic two. -/
theorem binary_aligned_group
    {F : Type*} [AddCommGroup F] [Module (ZMod 2) F]
    (A U : Fin 3 → Submodule (ZMod 2) F) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) (f : ∀ i, U i →ₗ[ZMod 2] ZMod 2)
    (hlocal : ∀ i (v : U i), (v : F) ∈ A i → f i v = 0)
    (hnz : ∀ i, AlignedRelation.relationForm U f i ≠ 0) :
    ∃ h : LinearMap.ker (AlignedRelation.signalSum U), ∀ i, f i (h.1 i) = 1 := by
  have hs := AlignedRelation.relation_sum_ne_zero A U hAU hspan f hlocal ⟨0,hnz 0⟩
  have hs' : AlignedRelation.relationForm U f 0 +
      AlignedRelation.relationForm U f 1 + AlignedRelation.relationForm U f 2 ≠ 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hs
  obtain ⟨h,h0,h1,h2⟩ := binary_three_forms_ones
    (AlignedRelation.relationForm U f 0) (AlignedRelation.relationForm U f 1)
    (AlignedRelation.relationForm U f 2) (hnz 0) (hnz 1) (hnz 2) hs'
  refine ⟨h, fun i => ?_⟩
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

end UploadBroadcast
