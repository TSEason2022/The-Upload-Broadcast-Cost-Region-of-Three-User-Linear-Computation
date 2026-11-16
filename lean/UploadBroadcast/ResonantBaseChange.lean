import UploadBroadcast.ResonantEndomorphisms
import UploadBroadcast.ScalarExtensionConfiguration
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.Tactic.FinCases

/-!
# Actual scalar extension of the resonant source configuration

The tensor-product coordinate equivalence identifies each of the three side
spaces and each of their three demand enlargements with the corresponding
space over the extension field. Naturality is proved on generators, extended
to all tensors, and transported to submodule ranges. This closes absolute
indecomposability for the fixed source model, for arbitrary field extensions.
No classification or real-root uniqueness assertion is used here. The
parameter `n` denotes manuscript block size `n + 1`.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 40000
set_option maxHeartbeats 2000000
open scoped TensorProduct
namespace UploadBroadcast.ResonantBaseChange
open ResonantEndomorphisms
variable (K L : Type*) [Field K] [Field L] [Algebra K L] (n : ℕ)
abbrev Vec (K : Type*) (n : ℕ) := Fin (n+1) → K
abbrev Param (K : Type*) (n : ℕ) := Vec K n × Vec K n × K

def vecEquiv : (L ⊗[K] Vec K n) ≃ₗ[L] Vec L n :=
  TensorProduct.piScalarRight K L L (Fin (n+1))

def scalarEquiv : (L ⊗[K] K) ≃ₗ[L] L := TensorProduct.AlgebraTensorModule.rid K L L

def productEquiv {A B C D : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup C] [Module L C]
    [AddCommGroup D] [Module L D]
    (e : (L ⊗[K] A) ≃ₗ[L] C) (f : (L ⊗[K] B) ≃ₗ[L] D) :
    (L ⊗[K] (A × B)) ≃ₗ[L] (C × D) :=
  (TensorProduct.prodRight K L L A B).trans (e.prodCongr f)

def ambientEquiv : (L ⊗[K] Ambient K (Vec K n)) ≃ₗ[L] Ambient L (Vec L n) :=
  productEquiv K L (vecEquiv K L n) (productEquiv K L (vecEquiv K L n)
    (productEquiv K L (vecEquiv K L n)
      (productEquiv K L (scalarEquiv K L) (scalarEquiv K L))))

def paramEquiv : (L ⊗[K] Param K n) ≃ₗ[L] Param L n :=
  productEquiv K L (vecEquiv K L n)
    (productEquiv K L (vecEquiv K L n) (scalarEquiv K L))

@[simp] theorem vecEquiv_tmul (a : L) (x : Vec K n) :
    vecEquiv K L n (a ⊗ₜ[K] x) = fun i => algebraMap K L (x i) * a := by
  simp [vecEquiv, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, Algebra.smul_def]

@[simp] theorem scalarEquiv_tmul (a : L) (x : K) :
    scalarEquiv K L (a ⊗ₜ[K] x) = algebraMap K L x * a := by
  simp [scalarEquiv, Algebra.smul_def]

@[simp] theorem productEquiv_tmul {A B C D : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup C] [Module L C]
    [AddCommGroup D] [Module L D]
    (e : (L ⊗[K] A) ≃ₗ[L] C) (f : (L ⊗[K] B) ≃ₗ[L] D)
    (a : L) (x : A × B) : productEquiv K L e f (a ⊗ₜ[K] x) =
      (e (a ⊗ₜ[K] x.1), f (a ⊗ₜ[K] x.2)) := rfl

/-- A common parameter space generates each of the six source subspaces. -/
def generator (c : Vec K n) (i : Fin 6) : Param K n →ₗ[K] Ambient K (Vec K n) where
  toFun q := ![(q.1,0,0,q.2.2,0), (0,q.1,0,0,q.2.2), (0,0,q.1,-q.2.2,q.2.2),
    (q.1,q.2.1,q.2.1,q.2.2,0), (q.2.1,q.1,q.2.1,0,q.2.2),
    (q.2.1,q.2.1+JordanResonance.shift K n q.2.1,q.1,
      columnForm K n c q.2.1-q.2.2,q.2.2)] i
  map_add' x y := by
    fin_cases i <;> simp <;> abel_nf
    all_goals simp
  map_smul' a x := by fin_cases i <;> simp [smul_add,smul_sub,mul_sub]

theorem generator_range (c : Vec K n) (i : Fin 6) :
    LinearMap.range (generator K n c i) = spaces K (Vec K n)
      (JordanResonance.shift K n) (columnForm K n c) i := by
  ext p
  constructor
  · rintro ⟨q,rfl⟩
    fin_cases i <;> simp [spaces,generator,side₁,side₂,side₃,total₁,total₂,total₃]
  · rcases p with ⟨x,y,z,v,r⟩
    intro hp
    fin_cases i
    · change y = 0 ∧ z = 0 ∧ r = 0 at hp
      rcases hp with ⟨rfl,rfl,rfl⟩
      exact ⟨(x,0,v),rfl⟩
    · change x = 0 ∧ z = 0 ∧ v = 0 at hp
      rcases hp with ⟨rfl,rfl,rfl⟩
      exact ⟨(y,0,r),rfl⟩
    · change x = 0 ∧ y = 0 ∧ v + r = 0 at hp
      rcases hp with ⟨rfl,rfl,hv⟩
      refine ⟨(z,0,r), ?_⟩
      have he : v = -r := by linear_combination hv
      simp [generator,he]
    · change y = z ∧ r = 0 at hp
      rcases hp with ⟨rfl,rfl⟩
      exact ⟨(x,y,v),rfl⟩
    · change x = z ∧ v = 0 at hp
      rcases hp with ⟨rfl,rfl⟩
      exact ⟨(y,x,r),rfl⟩
    · change y = x + JordanResonance.shift K n x ∧ v + r = columnForm K n c x at hp
      rcases hp with ⟨rfl,hv⟩
      refine ⟨(z,x,r), ?_⟩
      have he : v = columnForm K n c x - r := by linear_combination hv
      simp [generator,he]

/-- Scalar extension commutes with the image of any linear map. -/
theorem baseChange_range {A B : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (f : A →ₗ[K] B) :
    (LinearMap.range f).baseChange L = LinearMap.range (f.baseChange L) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,⟨y,rfl⟩,rfl⟩
    exact ⟨1 ⊗ₜ[K] y, by simp⟩
  · rintro _ ⟨x,rfl⟩
    induction x with
    | zero => simp
    | tmul a x =>
      simpa using (Submodule.tmul_mem_baseChange_of_mem a
        (show f x ∈ LinearMap.range f from ⟨x,rfl⟩))
    | add x y hx hy =>
      simpa using ((LinearMap.range f).baseChange L).add_mem hx hy

@[simp] theorem shift_map_smul (a : L) (x : Vec K n) :
    JordanResonance.shift L n (fun i => algebraMap K L (x i) * a) =
      fun i => algebraMap K L (JordanResonance.shift K n x i) * a := by
  funext i
  simp only [JordanResonance.shift, LinearMap.coe_mk, AddHom.coe_mk]
  split <;> simp

@[simp] theorem columnForm_map_smul (c x : Vec K n) (a : L) :
    columnForm L n (fun i => algebraMap K L (c i))
      (fun i => algebraMap K L (x i) * a) =
      algebraMap K L (columnForm K n c x) * a := by
  simp [columnForm, map_sum, map_mul, Finset.sum_mul, mul_assoc]

/-- The tensor extension of each generating map is the same source formula
written over the larger field. -/
theorem generator_natural (c : Vec K n) (i : Fin 6) (x : L ⊗[K] Param K n) :
    ambientEquiv K L n ((generator K n c i).baseChange L x) =
      generator L n (fun j => algebraMap K L (c j)) i (paramEquiv K L n x) := by
  induction x with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul]
    fin_cases i <;>
      simp only [ambientEquiv,paramEquiv,generator, LinearMap.coe_mk, AddHom.coe_mk,
        Matrix.cons_val_zero', Matrix.cons_val_succ', productEquiv_tmul, vecEquiv_tmul,
        scalarEquiv_tmul, LinearMap.map_zero, LinearEquiv.map_zero, RingHom.map_zero, map_neg, map_add, map_sub, add_mul, sub_mul,
        neg_mul, zero_mul, columnForm_map_smul, shift_map_smul, Pi.zero_apply,
        Pi.add_apply, Prod.mk.injEq, funext_iff, and_self, forall_true_iff, true_and, and_true]
  | add x y hx hy => simpa only [LinearMap.map_add, LinearEquiv.map_add] using congrArg₂ (· + ·) hx hy

/-- Exact scalar-extension compatibility of all six subspaces. -/
theorem spaces_baseChange (c : Vec K n) (i : Fin 6) :
    ((spaces K (Vec K n) (JordanResonance.shift K n) (columnForm K n c) i).baseChange L).map
        (ambientEquiv K L n).toLinearMap =
      spaces L (Vec L n) (JordanResonance.shift L n)
        (columnForm L n (fun j => algebraMap K L (c j))) i := by
  rw [← generator_range, baseChange_range, ← generator_range]
  ext y
  constructor
  · rintro ⟨_,⟨x,rfl⟩,rfl⟩
    exact ⟨paramEquiv K L n x, (generator_natural K L n c i x).symm⟩
  · rintro ⟨x,rfl⟩
    refine ⟨(generator K n c i).baseChange L ((paramEquiv K L n).symm x), ⟨_,rfl⟩, ?_⟩
    simp [generator_natural]

/-- The explicit tensor equivalence preserves the six labeled spaces both ways. -/
theorem configuration_iso (c : Vec K n) :
    TaskDecomposition.ConfigurationIso
      (TaskDecomposition.extendConfiguration (L := L)
        (spaces K (Vec K n) (JordanResonance.shift K n) (columnForm K n c)))
      (spaces L (Vec L n) (JordanResonance.shift L n)
        (columnForm L n (fun j => algebraMap K L (c j)))) := by
  refine ⟨ambientEquiv K L n, ?_, ?_⟩
  · intro i x hx
    rw [← spaces_baseChange K L n c i]
    exact ⟨x,hx,rfl⟩
  · intro i x hx
    rw [← spaces_baseChange K L n c i] at hx
    obtain ⟨y,hy,he⟩ := hx
    simpa only [← he, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hy

/-- Indecomposability is invariant under actual label-preserving linear equivalence. -/
theorem indecomposable_of_iso {F A B I : Type*} [Field F]
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    {S : I → Submodule F A} {T : I → Submodule F B}
    (hiso : TaskDecomposition.ConfigurationIso S T)
    (hind : TaskDecomposition.Indecomposable T ⊤) :
    TaskDecomposition.Indecomposable S ⊤ := by
  obtain ⟨e,he,hei⟩ := hiso
  apply TaskDecomposition.indecomposable_of_projection_eq_zero_or_id
  · intro hz
    apply hind.1
    apply eq_bot_iff.mpr
    intro y _
    have h : e.symm y ∈ (⊥ : Submodule F A) := by rw [← hz]; trivial
    have hzero : e.symm y = 0 := h
    have := congrArg e hzero
    simpa using this
  · intro f hf hi
    let g : B →ₗ[F] B := e.toLinearMap.comp (f.comp e.symm.toLinearMap)
    have hg : TaskDecomposition.Stable T g := by
      intro i x hx
      exact he i _ (hf i _ (hei i x hx))
    have hgi : ∀ x, g (g x) = g x := by
      intro x
      simp [g,hi]
    obtain hzero | hone := hind.projection_eq_zero_or_id g hg hgi
    · left
      apply LinearMap.ext
      intro x
      apply e.injective
      have h := LinearMap.congr_fun hzero (e x)
      simpa [g] using h
    · right
      apply LinearMap.ext
      intro x
      apply e.injective
      have h := LinearMap.congr_fun hone (e x)
      simpa [g] using h

/-- The fixed source configuration remains indecomposable after actual tensor
extension to any extension field, including infinite extensions. -/
theorem source_absolutely_indecomposable (c : Vec K n)
    (hc : c ∉ LinearMap.range (JordanResonance.sourceShift K n)) :
    TaskDecomposition.Indecomposable
      (TaskDecomposition.extendConfiguration (L := L)
        (spaces K (Vec K n) (JordanResonance.shift K n) (columnForm K n c))) ⊤ := by
  apply indecomposable_of_iso (configuration_iso K L n c)
  exact source_indecomposable_over_field_map (algebraMap K L) n c hc

/-- The normalized source column has exactly the canonical head pairing. -/
@[simp] theorem canonical_columnForm :
    columnForm K n (JordanResonance.sourceColumn K n) = JordanResonance.head K n := by
  ext x
  simp [columnForm, JordanResonance.sourceColumn, JordanResonance.head,
    Fin.sum_univ_succ]

/-- Canonical Jordan/head compatibility for all six actual extended subspaces. -/
theorem jordan_spaces_baseChange (i : Fin 6) :
    ((spaces K (Vec K n) (JordanResonance.shift K n)
        (JordanResonance.head K n) i).baseChange L).map (ambientEquiv K L n).toLinearMap =
      spaces L (Vec L n) (JordanResonance.shift L n) (JordanResonance.head L n) i := by
  have hc : columnForm L n
      (fun j => algebraMap K L (JordanResonance.sourceColumn K n j)) =
      JordanResonance.head L n := by
    ext x
    simp [columnForm, JordanResonance.sourceColumn, JordanResonance.head,
      Fin.sum_univ_succ]
  simpa only [canonical_columnForm, hc] using
    spaces_baseChange K L n (JordanResonance.sourceColumn K n) i

/-- Absolute indecomposability of the fixed canonical Jordan/head model under
actual tensor-product scalar extension. -/
theorem jordan_absolutely_indecomposable :
    TaskDecomposition.Indecomposable
      (TaskDecomposition.extendConfiguration (L := L)
        (spaces K (Vec K n) (JordanResonance.shift K n) (JordanResonance.head K n))) ⊤ := by
  simpa only [canonical_columnForm] using
    source_absolutely_indecomposable K L n (JordanResonance.sourceColumn K n)
      (JordanResonance.sourceColumn_not_mem_range K n)

#print axioms spaces_baseChange
#print axioms source_absolutely_indecomposable
#print axioms jordan_absolutely_indecomposable

end UploadBroadcast.ResonantBaseChange
