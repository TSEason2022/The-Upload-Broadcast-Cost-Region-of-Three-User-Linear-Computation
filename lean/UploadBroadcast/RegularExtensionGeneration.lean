import UploadBroadcast.QuiverExactSequence
import UploadBroadcast.TaskExactSequence
import UploadBroadcast.ExtensionGenerated

/-! Actual regular filtrations yield genuine finite block-extension certificates. -/
namespace UploadBroadcast.TaskDecomposition
open QuiverRepresentation
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem Task.toRep_isZero_of_top_eq_bot (T : Task K V)
    (hz : (⊤ : Submodule K V)=⊥) : IsZero T.toRep := by
  have hzero (x : V) : x=0 := by
    have hx : x ∈ (⊤ : Submodule K V) := Submodule.mem_top
    rw [hz] at hx
    exact hx
  intro v x
  cases v with
  | center => exact hzero x
  | middle i => exact Subtype.ext (hzero x.val)
  | outer i => exact Subtype.ext (hzero x.val)

/-- This conversion constructs every off-diagonal arrow and every actual
vertex isomorphism from the exact induced-subobject/quotient sequence. -/
theorem RegularFiltration.extensionGenerated
    (C : Rep K inwardE6 → Prop)
    (hC : ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W],
      ∀ S : Task K W, S.IsRegularSimple → C S.toRep)
    {T : Task K V} (h : RegularFiltration K T) [hfd : FiniteDimensional K V] :
    ExtensionGenerated C T.toRep := by
  revert hfd
  induction h with
  | zero T hz =>
    intro _
    exact .zero T.toRep (T.toRep_isZero_of_top_eq_bot hz)
  | step T P hp hquot ih =>
    intro _
    obtain ⟨z,e,_,_⟩ := exists_extension_presentation
      (T.onComponent P).toRep (T.quotientBy P).toRep T.toRep
      (T.componentInclusion P) (T.quotientProjection P)
      (T.componentInclusion_injective P) (T.quotientProjection_surjective P)
      (T.component_quotient_exact P)
    exact .iso e (.extension _ _ z (.atom _ (hC P (T.onComponent P) hp)) ih)

end UploadBroadcast.TaskDecomposition
