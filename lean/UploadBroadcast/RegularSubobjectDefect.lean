import UploadBroadcast.TaskComponentBridge
import UploadBroadcast.RegularHomVanishing

/-! Zero-defect indecomposable tasks have no positive-defect subobject. -/
namespace UploadBroadcast.TaskDecomposition

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def Task.componentDefect (T : Task K V) (P : Submodule K V) : ℤ :=
  ReflectionReduction.defect (T.componentDimension P)

/-- Defect is additive at every actual simultaneous internal split. -/
theorem Task.componentDefect_split [FiniteDimensional K V] (T : Task K V)
    {W P Q : Submodule K V} (h : Split T.spaces W P Q) :
    T.componentDefect W = T.componentDefect P + T.componentDefect Q := by
  have hu (i : Fin 3) : Module.finrank K ↥(T.U i ⊓ W) =
      Module.finrank K ↥(T.U i ⊓ P) + Module.finrank K ↥(T.U i ⊓ Q) := by
    simpa [Task.spaces] using h.finrank_inter_eq (i, true)
  have ha (i : Fin 3) : Module.finrank K ↥(T.A i ⊓ W) =
      Module.finrank K ↥(T.A i ⊓ P) + Module.finrank K ↥(T.A i ⊓ Q) := by
    simpa [Task.spaces] using h.finrank_inter_eq (i, false)
  unfold Task.componentDefect Task.componentDimension ReflectionReduction.defect
  simp only [hu, ha, h.finrank_eq, Nat.cast_add]
  ring

@[simp] theorem Task.componentDefect_bot (T : Task K V) : T.componentDefect ⊥ = 0 := by
  have hi (A : Submodule K V) : Module.finrank K ↥(A ⊓ ⊥) = 0 := by
    rw [inf_bot_eq]
    exact finrank_bot K V
  simp [Task.componentDefect, Task.componentDimension, ReflectionReduction.defect, hi]

/-- Actual finite decomposition supplies a positive-defect indecomposable
component of every task component of positive total defect. -/
theorem Task.exists_positive_defect_component [FiniteDimensional K V]
    (T : Task K V) {W : Submodule K V} (hpos : 0 < T.componentDefect W) :
    ∃ P : Submodule K V, P ≤ W ∧ Indecomposable T.spaces P ∧ 0 < T.componentDefect P := by
  have hd := TaskDecomposition.exists_decomposition T.spaces W
  induction hd with
  | zero => simp at hpos
  | @atom W h => exact ⟨W, le_rfl, h, hpos⟩
  | @split W P Q hs hp hq ihp ihq =>
    have hadd := T.componentDefect_split hs
    have hpq : 0 < T.componentDefect P ∨ 0 < T.componentDefect Q := by omega
    rcases hpq with hP | hQ
    · obtain ⟨R, hRP, hR, hpos⟩ := ihp hP
      exact ⟨R, hRP.trans (hs.sup_eq ▸ le_sup_left), hR, hpos⟩
    · obtain ⟨R, hRQ, hR, hpos⟩ := ihq hQ
      exact ⟨R, hRQ.trans (hs.sup_eq ▸ le_sup_right), hR, hpos⟩

@[simp] theorem Task.componentDefect_top {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (T : Task K V) : T.componentDefect ⊤ = ReflectionReduction.defect T.dimensionVector := by
  have hi (A : Submodule K V) : Module.finrank K ↥(A ⊓ ⊤) = Module.finrank K A := by
    rw [inf_top_eq]
  simp [Task.componentDefect, Task.componentDimension, Task.dimensionVector, ReflectionReduction.defect, hi]

/-- Restricting an ambient preserving map to a component preserves all six induced spaces. -/
theorem Task.preserves_onComponent {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (T : Task K V) (S : Task K W) (f : V →ₗ[K] W) (hf : Preserves T.spaces S.spaces f)
    (P : Submodule K V) : Preserves (T.onComponent P).spaces S.spaces (f.comp P.subtype) := by
  intro i x hx
  apply hf i x.val
  rw [T.onComponent_spaces] at hx
  exact hx

/-- No positive-defect task, decomposable or not, injects as an actual
six-subspace-preserving subobject of a zero-defect indecomposable task. -/
theorem Task.defect_nonpos_of_injective_preserves {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (T : Task K V) (S : Task K W) (hS : Indecomposable S.spaces ⊤)
    (hzero : ReflectionReduction.defect S.dimensionVector = 0)
    (f : V →ₗ[K] W) (hf : Preserves T.spaces S.spaces f) (hinj : Function.Injective f) :
    ReflectionReduction.defect T.dimensionVector ≤ 0 := by
  by_contra! hpos
  have hpos' : 0 < T.componentDefect ⊤ := by simpa using hpos
  obtain ⟨P, _, hP, hposP⟩ := T.exists_positive_defect_component hpos'
  have hiP := (T.onComponent P).rep_indec_of_indec (T.onComponent_indec P hP)
  have hiS := S.rep_indec_of_indec hS
  have hpositive : 0 < ReflectionReduction.defect
      (E6Reflection.vector (QuiverRepresentation.dimension (T.onComponent P).toRep)) := by
    change 0 < ReflectionReduction.defect (T.onComponent P).dimensionVector
    rw [T.onComponent_dimensionVector]
    exact hposP
  let hmap := (T.onComponent P).homOfPreserves S (f.comp P.subtype) (T.preserves_onComponent S f hf P)
  have hz := RegularHomVanishing.positive_to_zero_hom_zero
    (T.onComponent P).toRep S.toRep hiP hiS hpositive hzero hmap
  have hz' : f.comp P.subtype = 0 := congrArg (fun h => h.map QuiverRepresentation.E6Vertex.center) hz
  apply hP.1
  apply bot_unique
  intro x hx
  apply hinj
  have hh := LinearMap.congr_fun hz' (⟨x, hx⟩ : P)
  simpa using hh

end UploadBroadcast.TaskDecomposition
