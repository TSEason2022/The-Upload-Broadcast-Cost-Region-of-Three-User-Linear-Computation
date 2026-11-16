import UploadBroadcast.StableEnd
import Mathlib.Tactic.NoncommRing

/-!
# Grade-preserving nonresonant splitting for a regular hexagon pencil

For a finite endomorphism ring and an operator `T` whose cube preserves each
specified grade, this module constructs a grade-preserving idempotent power
of `T^3 - 1`. On its image, `1 - T` has an explicitly supported two-sided
inverse. Consequently every coupling row on that image factors through
`1 - T`. This is the regular-pencil splitting step; it does not assert that
an arbitrary pencil has an invertible matching, nor classify singular pencils.
-/
namespace UploadBroadcast.GradedRelationSplit

section Ring
variable {R : Type*} [Ring R]

/-- An idempotent power of `T^3 - 1` admits a supported partial inverse for
`1 - T`. This algebraic identity needs neither division nor a characteristic
restriction, so it also applies in characteristics two and three. -/
theorem supported_inverse_of_idempotent_power (T : R) (n : ℕ) (hn : 0 < n)
    (he : (T^3-1)^(n+n)=(T^3-1)^n) :
    ∃ H : R,
      Commute H T ∧
      (1-T)*H=(T^3-1)^n ∧ H*(1-T)=(T^3-1)^n ∧
      H*(T^3-1)^n=H ∧ (T^3-1)^n*H=H := by
  let N := T^3-1
  let E := N^n
  let G := N^(n-1)*E
  let Q := 1+T+T^2
  have hEE : E*E=E := by
    dsimp [E,N]
    rwa [←pow_add]
  have hNT : Commute N T :=
    ((Commute.refl T).pow_left 3).sub_left (Commute.one_left T)
  have hET : Commute E T := hNT.pow_left n
  have hGT : Commute G T := (hNT.pow_left (n-1)).mul_left hET
  have hNG : N*G=E := by
    dsimp [G]
    rw [←mul_assoc,←pow_succ',Nat.sub_add_cancel (by omega : 1 ≤ n)]
    exact hEE
  have hGE : G*E=G := by dsimp [G]; rw [mul_assoc,hEE]
  have hEG : E*G=G := by
    have h : Commute E G :=
      ((Commute.refl N).pow_left n |>.pow_right (n-1)).mul_right (Commute.refl E)
    rw [h.eq,hGE]
  have hQT : Commute Q T :=
    ((Commute.one_left T).add_left (Commute.refl T)).add_left
      ((Commute.refl T).pow_left 2)
  have hEQ : Commute E Q :=
    ((Commute.one_right E).add_right hET).add_right (hET.pow_right 2)
  have hfactor : (1-T)*(-Q)=N := by dsimp [Q,N]; noncomm_ring
  refine ⟨-Q*G,hQT.neg_left.mul_left hGT,?_,?_,?_,?_⟩
  · rw [←mul_assoc,hfactor,hNG]
  · have hh : Commute (-Q*G) (1-T) :=
      (Commute.one_right _).sub_right (hQT.neg_left.mul_left hGT)
    rw [hh.eq,←mul_assoc,hfactor,hNG]
  · rw [mul_assoc,hGE]
  · rw [←mul_assoc,hEQ.neg_right.eq,mul_assoc,hEG]

/-- Every element of a finite ring has a nonresonant projector with a
supported inverse. The projector is a positive power of the grade-preserving
operator `T^3 - 1`. -/
theorem exists_nonresonant_projector [Finite R] (T : R) :
    ∃ (n : ℕ) (H : R), 0 < n ∧
      (T^3-1)^n*(T^3-1)^n=(T^3-1)^n ∧
      Commute ((T^3-1)^n) T ∧ Commute H T ∧
      (1-T)*H=(T^3-1)^n ∧ H*(1-T)=(T^3-1)^n ∧
      H*(T^3-1)^n=H ∧ (T^3-1)^n*H=H := by
  obtain ⟨n,hn,he⟩ := FiniteMonoidPower.exists_pos_pow_add_eq (T^3-1)
  obtain ⟨H,hHT,hleft,hright,hHE,hEH⟩ :=
    supported_inverse_of_idempotent_power T n hn he
  refine ⟨n,H,hn,?_,?_,hHT,hleft,hright,hHE,hEH⟩
  · rwa [←pow_add]
  · exact (((Commute.refl T).pow_left 3).sub_left (Commute.one_left T)).pow_left n

/-- Every coordinate projection commuting with the cube also commutes with
its nonresonant projector. No eigenvalues or roots of unity are needed. -/
theorem projector_commutes_of_cube_commutes (T A : R) (n : ℕ)
    (h : Commute (T^3) A) : Commute ((T^3-1)^n) A :=
  (h.sub_left (Commute.one_left A)).pow_left n
end Ring

section Linear
open TaskDecomposition
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Grade preservation passes from the cube to every nonresonant power. -/
theorem projector_stable_of_cube_stable (T : Module.End K V)
    (S : ι → Submodule K V) (h : Stable S (T^3)) (n : ℕ) :
    Stable S ((T^3-1)^n) := by
  let N : stableEnd S := ⟨T^3-1,fun i x hx => (S i).sub_mem (h i x hx) hx⟩
  exact (N^n).property

/-- The regular-pencil algebraic splitting, with all prescribed grades
retained. The partial inverse need not preserve grades. -/
theorem exists_graded_nonresonant_projector [Finite K] [FiniteDimensional K V]
    (T : Module.End K V) (S : ι → Submodule K V) (h : Stable S (T^3)) :
    ∃ (n : ℕ) (H : Module.End K V), 0 < n ∧
      Stable S ((T^3-1)^n) ∧
      (T^3-1)^n*(T^3-1)^n=(T^3-1)^n ∧
      Commute ((T^3-1)^n) T ∧ Commute H T ∧
      (1-T)*H=(T^3-1)^n ∧ H*(1-T)=(T^3-1)^n ∧
      H*(T^3-1)^n=H ∧ (T^3-1)^n*H=H := by
  letI : Finite V := Module.finite_of_finite K
  letI : Finite (Module.End K V) := Finite.of_injective
    (fun f : Module.End K V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨n,H,hn,hrest⟩ := exists_nonresonant_projector T
  exact ⟨n,H,hn,projector_stable_of_cube_stable T S h n,hrest⟩

/-- A fixed vector is annihilated by every positive nonresonant power. -/
theorem projector_apply_fixed_eq_zero (T : Module.End K V) (n : ℕ)
    (hn : 0 < n) (v : V) (hv : T v=v) : (((T^3-1)^n) : Module.End K V) v=0 := by
  have hNv : ((T^3-1) : Module.End K V) v=0 := by
    simp [pow_succ,Module.End.mul_apply,hv]
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ,Module.End.mul_apply,hNv,map_zero]

/-- A detected fixed mode rules out the identity branch of the nonresonant
projector dichotomy. This is the final algebraic step after a configuration
has supplied the dichotomy via an actual stable lift. -/
theorem nilpotent_cube_sub_one_of_projector_dichotomy [Finite K]
    [FiniteDimensional K V] (T : Module.End K V)
    (v : V) (hv : T v=v) (hv0 : v≠0)
    (hind : ∀ (n : ℕ) (H : Module.End K V), 0 < n →
      (T^3-1)^n*(T^3-1)^n=(T^3-1)^n →
      Commute ((T^3-1)^n) T → Commute H T →
      (1-T)*H=(T^3-1)^n → H*(1-T)=(T^3-1)^n →
      H*(T^3-1)^n=H → (T^3-1)^n*H=H →
      (T^3-1)^n=0 ∨ (T^3-1)^n=1) :
    IsNilpotent (T^3-1) := by
  letI : Finite V := Module.finite_of_finite K
  letI : Finite (Module.End K V) := Finite.of_injective
    (fun f : Module.End K V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨n,H,hn,hEE,hET,hHT,hleft,hright,hHE,hEH⟩ := exists_nonresonant_projector T
  obtain hz | ho := hind n H hn hEE hET hHT hleft hright hHE hEH
  · exact ⟨n,hz⟩
  · have he := projector_apply_fixed_eq_zero T n hn v hv
    rw [ho] at he
    exact False.elim (hv0 he)

/-- A coupling restricted to the nonresonant projector factors through the
boundary `1 - T`. Support of the partial inverse also supports the factor. -/
theorem coupling_factorization {W : Type*} [AddCommGroup W] [Module K W]
    (T E H : Module.End K V) (κ : V →ₗ[K] W)
    (hHE : H*E=H) (hboundary : H*(1-T)=E) :
    (κ.comp H).comp (1-T)=κ.comp E ∧ (κ.comp H).comp E=κ.comp H := by
  constructor
  · ext x
    exact congrArg κ (LinearMap.congr_fun hboundary x)
  · ext x
    exact congrArg κ (LinearMap.congr_fun hHE x)
end Linear

end UploadBroadcast.GradedRelationSplit
