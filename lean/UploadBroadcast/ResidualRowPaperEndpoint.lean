import UploadBroadcast.ResidualRowShape
import UploadBroadcast.CanonicalResidualScalar

/-! Source-spelled row-completion package: pure owned rows, the exact relay
sum, fixed tripod/pairwise coefficients, and scalar original-field uploads. -/
namespace UploadBroadcast.ResidualRowShape
open Module ResidualUpload ResidualTaskAssembly
variable {K P₁ P₂ P₃ D E : Type*} [Field K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]
  [AddCommGroup E] [Module K E]
  [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K D]
set_option maxHeartbeats 400000

/-- Row-wise completion with explicit individually owned pure generators and
one scalar code on the original task. The same simultaneous shear extends
by the identity on the pairwise-known coefficient factor E. -/
theorem row_completion_paper [Finite K]
    (task : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)
    (hz : pureRows₁ task ⊓ pureRows₂ task ⊓ pureRows₃ task = ⊥)
    (W : Submodule K D)
    (hSW : IsCompl (pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task) W) :
    let S := pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task
    let n := finrank K P₁ + finrank K P₂ + finrank K P₃ + finrank K S + finrank K W
    ∃ (f : Ambient P₁ P₂ P₃ D ≃ₗ[K] Ambient P₁ P₂ P₃ D)
      (Prow : Submodule K (Ambient P₁ P₂ P₃ D)),
      let Q := privateSpace ⊔ Prow ⊔ W.map (embedV (K := K))
      (∀ i, (task.A i).map f.toLinearMap = task.A i) ∧
      (∀ t, f (0,t) = (0,t)) ∧
      (∀ (t : D × D) (z : E), (f.prodCongr (LinearEquiv.refl K E)) ((0,t),z) = ((0,t),z)) ∧
      (∀ i, (task.U i).map f.toLinearMap ≤ task.A i ⊔ Q) ∧
      task.LocallyGenerated Q ∧
      Prow ≤ (⊥ : Submodule K ((P₁ × P₂) × P₃)).prod (S.prod S) ∧
      finrank K Prow = finrank K S ∧
      (∃ (b : Basis (Fin (finrank K Prow)) K Prow)
        (owner : Fin (finrank K Prow) → Three), ∀ j, (b j : Ambient P₁ P₂ P₃ D) ∈ task.A (owner j)) ∧
      Disjoint Prow (W.map (embedV (K := K))) ∧
      Disjoint privateSpace (Prow ⊔ W.map (embedV (K := K))) ∧
      finrank K Q = n ∧
      (∃ r : Three → ℕ, ∃ c : task.LinearCode 1 r n,
        (∑ i, r i) = n ∧ c.toCode.uploadCost ≤ n ∧ c.toCode.broadcastCost ≤ n) := by
  dsimp only
  obtain ⟨f,Prow,ha,hfix,hf,hl,hs,hlrow,hr,hd,hpriv,hQrank⟩ :=
    exists_exact_row_completion task h₀ h₁ h₂ hz W hSW
  obtain ⟨b,owner,howner⟩ := locally_generated_basis task.A Prow hlrow
  let Q := privateSpace (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D) ⊔
    Prow ⊔ W.map (embedV (K := K))
  obtain ⟨Q₀,hlocal,hfeas,hrank⟩ := pullback_relay task.A task.U f Q ha hl hf
  have hcode := RelayLinearComposition.full_relay_linear_code task Q₀ hlocal hfeas
  rw [hrank,hQrank] at hcode
  refine ⟨f,Prow,ha,hfix,?_,hf,hl,hs,hr,⟨b,owner,howner⟩,hd,hpriv,hQrank,hcode⟩
  intro t z
  exact Prod.ext (hfix t) rfl

end UploadBroadcast.ResidualRowShape
