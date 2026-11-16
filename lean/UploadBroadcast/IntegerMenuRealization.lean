import UploadBroadcast.AllocationAggregate
import Mathlib.Data.Fintype.EquivFin

namespace UploadBroadcast.Allocation

/-- Integer menu multiplicities are realized by an actual choice for every
component copy; equality holds for every coordinate consumption function. -/
theorem realize_nat_menu {I A : Type*} [Fintype I] [Fintype A]
    (w : A → ℕ) (hw : ∑ a, w a = Fintype.card I) :
    ∃ choose : I → A, ∀ value : A → ℝ,
      (∑ i, value (choose i)) = ∑ a, (w a : ℝ) * value a := by
  classical
  have hcard : Fintype.card (Σ a, Fin (w a)) = Fintype.card I := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using hw
  let e : (Σ a, Fin (w a)) ≃ I :=
    (Fintype.equivFinOfCardEq hcard).trans (Fintype.equivFin I).symm
  let choose : I → A := fun i => (e.symm i).1
  refine ⟨choose,?_⟩
  intro value
  have h := Equiv.sum_comp e (fun i => value (choose i))
  simp only [choose,Equiv.symm_apply_apply] at h
  rw [← h,Fintype.sum_sigma]
  simp

/-- Realized choices inherit every coordinate budget of their integer weights. -/
theorem realize_nat_menu_budget {I A J : Type*} [Fintype I] [Fintype A]
    (w : A → ℕ) (hw : ∑ a, w a = Fintype.card I)
    (menu : A → J → ℝ) (budget : J → ℝ)
    (hbudget : ∀ j, (∑ a, (w a : ℝ) * menu a j) ≤ budget j) :
    ∃ choose : I → A, ∀ j, (∑ i, menu (choose i) j) ≤ budget j := by
  obtain ⟨choose,h⟩ := realize_nat_menu w hw
  exact ⟨choose,fun j => (h (fun a => menu a j)).le.trans (hbudget j)⟩

end UploadBroadcast.Allocation
