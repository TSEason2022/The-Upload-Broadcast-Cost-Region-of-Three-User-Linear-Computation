import UploadBroadcast.ResidualRowShapeCore

/-! Exact pure/retained-row relay shape, with a tripod-fixing simultaneous shear. -/
namespace UploadBroadcast.ResidualRowShape
open Module ResidualUpload ResidualRowCompletion ResidualTaskAssembly ResidualRelayAssembly
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {K P₁ P₂ P₃ H₁ H₂ H₃ Z : Type*} [Field K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup H₁] [Module K H₁]
  [AddCommGroup H₂] [Module K H₂] [AddCommGroup H₃] [Module K H₃]
  [AddCommGroup Z] [Module K Z]
local notation "R" => Rows H₁ H₂ H₃ Z
local notation "S₁" => A₁ K P₁ P₂ P₃ R
local notation "S₂" => A₂ K P₁ P₂ P₃ R
local notation "S₃" => A₃ K P₁ P₂ P₃ R
local notation "P" => LinearMap.range (fullRelay (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃)
  (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (D := Z))

section RetainedRows
variable {D : Type*} [AddCommGroup D] [Module K D]

/-- Assemble exact relay geometry with abstract row factors, so the concrete
normal-form chart is instantiated only once. -/
private theorem exists_exact_row_completion_of_coordinates [FiniteDimensional K P₁] [FiniteDimensional K P₂]
    [FiniteDimensional K P₃] [FiniteDimensional K D]
    (task : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)
    (S W : Submodule K D) (hSW : IsCompl S W) (e₀ : R ≃ₗ[K] S)
    (b₀ : ∀ t : Rows (H₁ × W) H₂ H₃ Z,
      supportedEquiv S W hSW e₀ t ∈ pureRows₁ task → t.1=0 ∧ t.2.2.2.2=0)
    (b₁ : ∀ t : Rows (H₁ × W) H₂ H₃ Z,
      supportedEquiv S W hSW e₀ t ∈ pureRows₂ task → t.2.1=0 ∧ t.2.2.2.1=0)
    (b₂ : ∀ t : Rows (H₁ × W) H₂ H₃ Z,
      supportedEquiv S W hSW e₀ t ∈ pureRows₃ task → t.2.2.1=0) :
    ∃ (f : Ambient P₁ P₂ P₃ D ≃ₗ[K] Ambient P₁ P₂ P₃ D)
      (Prow : Submodule K (Ambient P₁ P₂ P₃ D)),
      let Q := privateSpace ⊔ Prow ⊔ W.map (embedV (K := K))
      (∀ i, (task.A i).map f.toLinearMap = task.A i) ∧
      (∀ t, f (0,t) = (0,t)) ∧
      (∀ i, (task.U i).map f.toLinearMap ≤ task.A i ⊔ Q) ∧
      task.LocallyGenerated Q ∧
      Prow ≤ (⊥ : Submodule K ((P₁ × P₂) × P₃)).prod (S.prod S) ∧
      task.LocallyGenerated Prow ∧
      finrank K Prow = finrank K S ∧
      Disjoint Prow (W.map (embedV (K := K))) ∧
      Disjoint privateSpace (Prow ⊔ W.map (embedV (K := K))) ∧
      finrank K Q = finrank K P₁ + finrank K P₂ + finrank K P₃ + finrank K S + finrank K W := by
  let e := supportedEquiv S W hSW e₀
  have hshape : LinearMap.range (transportedFullRelay (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) e) =
      privateSpace ⊔ pureRelay S e ⊔ W.map (embedV (K := K)) :=
    supportedFullRelay_shape (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃)
      (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (Z := Z) S W hSW e₀
  obtain ⟨f,ha,hf,hfix,hl⟩ := exists_shear_of_row_coordinates (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (H₁ := H₁ × W) (H₂ := H₂) (H₃ := H₃) (Z := Z) task h₀ h₁ h₂ e b₀ b₁ b₂
  refine ⟨f,pureRelay S e,ha,hfix,?_,?_,pureRelay_supported (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (Z := Z) S W hSW e₀,?_,
    pureRelay_rank (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (H₁ := H₁ × W) (H₂ := H₂) (H₃ := H₃) (Z := Z) S e,pureRelay_disjoint_retained (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (Z := Z) S W hSW e₀,
    privateSpace_disjoint_rows (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (H₁ := H₁ × W) (H₂ := H₂) (H₃ := H₃) (Z := Z) S W e,?_⟩
  · simpa only [hshape] using hf
  · simpa only [hshape] using hl
  · have hA : ∀ i, task.A i = ![A₁ K P₁ P₂ P₃ D,A₂ K P₁ P₂ P₃ D,A₃ K P₁ P₂ P₃ D] i := by
      intro i; fin_cases i
      · exact h₀
      · exact h₁
      · exact h₂
    simpa only [Task.LocallyGenerated,hA] using
      (pureRelay_locally_generated (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (Z := Z) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) S W hSW e₀)
  · rw [← hshape]
    exact supportedFullRelay_rank (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (Z := Z) S W hSW e₀

/-- Source-level row completion, for any prescribed retained lift W complementary
to the pure-row span. The simultaneous shear fixes the tripod pointwise, all
three sides are unchanged, and the relay has the exact independent-sum shape
private ⊕ P_row ⊕ (W⊗v), with dim P_row = dim B₀. -/
theorem exists_exact_row_completion [FiniteDimensional K P₁] [FiniteDimensional K P₂]
    [FiniteDimensional K P₃] [FiniteDimensional K D]
    (task : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)
    (hz : pureRows₁ task ⊓ pureRows₂ task ⊓ pureRows₃ task = ⊥)
    (W : Submodule K D)
    (hSW : IsCompl (pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task) W) :
    let S := pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task
    ∃ (f : Ambient P₁ P₂ P₃ D ≃ₗ[K] Ambient P₁ P₂ P₃ D)
      (Prow : Submodule K (Ambient P₁ P₂ P₃ D)),
      let Q := privateSpace ⊔ Prow ⊔ W.map (embedV (K := K))
      (∀ i, (task.A i).map f.toLinearMap = task.A i) ∧
      (∀ t, f (0,t) = (0,t)) ∧
      (∀ i, (task.U i).map f.toLinearMap ≤ task.A i ⊔ Q) ∧
      task.LocallyGenerated Q ∧
      Prow ≤ (⊥ : Submodule K ((P₁ × P₂) × P₃)).prod (S.prod S) ∧
      task.LocallyGenerated Prow ∧
      finrank K Prow = finrank K S ∧
      Disjoint Prow (W.map (embedV (K := K))) ∧
      Disjoint privateSpace (Prow ⊔ W.map (embedV (K := K))) ∧
      finrank K Q = finrank K P₁ + finrank K P₂ + finrank K P₃ + finrank K S + finrank K W := by
  classical
  let S := pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task
  let A := (pureRows₁ task).comap S.subtype
  let B := (pureRows₂ task).comap S.subtype
  let C := (pureRows₃ task).comap S.subtype
  have hz' : A ⊓ B ⊓ C = ⊥ := by
    apply bot_unique
    intro t ht
    apply Subtype.ext
    have hh : (t : D) ∈ pureRows₁ task ⊓ pureRows₂ task ⊓ pureRows₃ task := ht
    rw [hz] at hh
    exact hh
  obtain ⟨c⟩ := ZeroCommonRowNormalForm.exists_chart A B C hz'
  let e : Rows (c.H₁ × W) c.H₂ c.H₃ (⊥ : Submodule K S) ≃ₗ[K] D :=
    supportedEquiv (H₁ := c.H₁) (H₂ := c.H₂) (H₃ := c.H₃)
      (Z := (⊥ : Submodule K S)) S W hSW c.equiv
  have e_apply (t : Rows (c.H₁ × W) c.H₂ c.H₃ (⊥ : Submodule K S)) :
      e t = (c.equiv (t.1.1,t.2) : D) + (t.1.2 : D) := rfl
  have support (t : Rows (c.H₁ × W) c.H₂ c.H₃ (⊥ : Submodule K S))
      (ht : e t ∈ S) : t.1.2 = 0 ∧ (c.equiv (t.1.1,t.2) : D) = e t := by
    have hw : (t.1.2 : D) ∈ S := by
      have hh := S.sub_mem ht (c.equiv (t.1.1,t.2)).property
      rw [e_apply] at hh
      simpa only [add_sub_cancel_left] using hh
    have hz : t.1.2 = 0 := Subtype.ext
      (Submodule.disjoint_def.mp hSW.disjoint _ hw t.1.2.property)
    refine ⟨hz,?_⟩
    rw [e_apply,hz,Submodule.coe_zero,add_zero]
  have b₀ (t : Rows (c.H₁ × W) c.H₂ c.H₃ (⊥ : Submodule K S))
      (ht : e t ∈ pureRows₁ task) : t.1=0 ∧ t.2.2.2.2=0 := by
    have hs : e t ∈ S := (show pureRows₁ task ≤ S from le_sup_left.trans le_sup_left) ht
    obtain ⟨hw,he⟩ := support t hs
    have hc := c.first (t.1.1,t.2) (by
      change (c.equiv (t.1.1,t.2) : D) ∈ pureRows₁ task
      rw [he]
      exact ht)
    exact ⟨Prod.ext hc.1 hw,hc.2⟩
  have b₁ (t : Rows (c.H₁ × W) c.H₂ c.H₃ (⊥ : Submodule K S))
      (ht : e t ∈ pureRows₂ task) : t.2.1=0 ∧ t.2.2.2.1=0 := by
    have hs : e t ∈ S := (show pureRows₂ task ≤ S from le_sup_right.trans le_sup_left) ht
    obtain ⟨_,he⟩ := support t hs
    exact c.second (t.1.1,t.2) (by
      change (c.equiv (t.1.1,t.2) : D) ∈ pureRows₂ task
      rw [he]
      exact ht)
  have b₂ (t : Rows (c.H₁ × W) c.H₂ c.H₃ (⊥ : Submodule K S))
      (ht : e t ∈ pureRows₃ task) : t.2.2.1=0 := by
    have hs : e t ∈ S := (show pureRows₃ task ≤ S from le_sup_right) ht
    obtain ⟨_,he⟩ := support t hs
    exact c.third (t.1.1,t.2) (by
      change (c.equiv (t.1.1,t.2) : D) ∈ pureRows₃ task
      rw [he]
      exact ht)
  exact exists_exact_row_completion_of_coordinates (K := K)
    (P₁ := P₁) (P₂ := P₂) (P₃ := P₃)
    (H₁ := c.H₁) (H₂ := c.H₂) (H₃ := c.H₃) (Z := (⊥ : Submodule K S))
    task h₀ h₁ h₂ S W hSW c.equiv b₀ b₁ b₂

/-- Extending the residual shear by the identity leaves every pairwise-known
summand pointwise fixed, as well as the entire tripod. -/
theorem shear_extension_fixes_pairwise {E : Type*} [AddCommGroup E] [Module K E]
    (f : Ambient P₁ P₂ P₃ D ≃ₗ[K] Ambient P₁ P₂ P₃ D)
    (hfix : ∀ t, f (0,t) = (0,t)) :
    (∀ e : E, (f.prodCongr (LinearEquiv.refl K E)) (0,e) = (0,e)) ∧
    (∀ t e, (f.prodCongr (LinearEquiv.refl K E)) ((0,t),e) = ((0,t),e)) := by
  constructor
  · intro e; simp
  · intro t e; exact Prod.ext (hfix t) rfl

end RetainedRows
end UploadBroadcast.ResidualRowShape
