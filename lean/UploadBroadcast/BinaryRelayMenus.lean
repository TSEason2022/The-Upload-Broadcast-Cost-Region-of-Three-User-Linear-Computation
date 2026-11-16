import UploadBroadcast.NonzeroDefectRelays
import UploadBroadcast.NonzeroDefectProfile
import UploadBroadcast.AllocationAggregate

/-!
# Binary relay selection and integer menu charges

The original-field linear algebra below works over every field, including
`ZMod 2`. No extension-field specialization or `q ≥ 3` selection is used.
The input rank conditions describe actual original subspaces, relations, and
restriction maps. Classification of the indecomposables into these geometric
conditions remains a separate obligation.
-/
namespace UploadBroadcast.BinaryRelayMenus
open Module NonzeroDefectRelays
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Two proper subspaces cannot cover a vector space over any field. -/
theorem exists_outside_two (A B : Submodule K F) (hA : A ≠ ⊤) (hB : B ≠ ⊤) :
    ∃ x : F, x ∉ A ∧ x ∉ B := by
  have ha : ∃ x : F, x ∉ A := by
    by_contra hh
    push_neg at hh
    exact hA (top_unique (fun x _ => hh x))
  have hb : ∃ x : F, x ∉ B := by
    by_contra hh
    push_neg at hh
    exact hB (top_unique (fun x _ => hh x))
  obtain ⟨a,ha⟩ := ha
  obtain ⟨b,hb⟩ := hb
  by_cases haB : a ∈ B
  · by_cases hbA : b ∈ A
    · refine ⟨a+b, ?_, ?_⟩
      · intro hh
        exact ha (by simpa using A.sub_mem hh hbA)
      · intro hh
        exact hb (by simpa using B.sub_mem hh haB)
    · exact ⟨b,hbA,hb⟩
  · exact ⟨a,ha,haB⟩

/-- The two-exclusion argument also applies to vector-valued linear maps. -/
theorem exists_two_nonzero_linearMaps
    {Y Z : Type*} [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
    (f : F →ₗ[K] Y) (g : F →ₗ[K] Z) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ x, f x ≠ 0 ∧ g x ≠ 0 := by
  have hf' : LinearMap.ker f ≠ ⊤ := by
    intro hh; apply hf; ext x
    exact (show x ∈ LinearMap.ker f by rw [hh]; trivial)
  have hg' : LinearMap.ker g ≠ ⊤ := by
    intro hh; apply hg; ext x
    exact (show x ∈ LinearMap.ker g by rw [hh]; trivial)
  exact exists_outside_two (LinearMap.ker f) (LinearMap.ker g) hf' hg'

/-- A relation direction and one protected remote direction can always be
kept nonzero by a form in the prescribed signal annihilator, even over F₂. -/
theorem exists_annihilating_form_two [FiniteDimensional K F] (U : Submodule K F) (v w : F)
    (hv : v ∉ U) (hw : w ∉ U) :
    ∃ l : F →ₗ[K] K, U ≤ LinearMap.ker l ∧ l v ≠ 0 ∧ l w ≠ 0 := by
  obtain ⟨l,hlv,hlw⟩ := exists_two_nonzero_linearMaps (K := K) (F := U.dualAnnihilator) (Y := K) (Z := K)
    (annihilatorEvaluation U v) (annihilatorEvaluation U w)
    (annihilatorEvaluation_ne_zero U v hv) (annihilatorEvaluation_ne_zero U w hw)
  refine ⟨l.1, ?_, hlv,hlw⟩
  intro x hx
  exact (Submodule.mem_dualAnnihilator l.1).mp l.property x hx

/-- Two-stage bilinear selection for the binary codimension-two relay.
Each stage avoids only two proper kernels. -/
theorem exists_bilinear_nonzero_with_one_constraint
    {X Y : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (B : X →ₗ[K] Y →ₗ[K] K) (hB : B ≠ 0)
    (f : X →ₗ[K] K) (g : Y →ₗ[K] K) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ x y, f x ≠ 0 ∧ g y ≠ 0 ∧ B x y ≠ 0 := by
  obtain ⟨x,hxB,hxf⟩ := exists_two_nonzero_linearMaps B f hB hf
  obtain ⟨y,hyB,hyg⟩ := exists_two_nonzero_linearMaps (B x) g hxB hg
  exact ⟨x,y,hxf,hyg,hyB⟩

section Dimensions
variable [FiniteDimensional K F]

/-- Binary hyperplane relay with a prescribed protected remote vector. -/
theorem exists_binary_hyperplane_relay
    (T : Task K F) (hspan : T.Spanning)
    (a b c v : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a+b+c=0) (hbU : b ∉ T.U 0) (hvU : v ∉ T.U 0) :
    ∃ l : F →ₗ[K] K,
      T.U 0 ≤ LinearMap.ker l ∧ l b ≠ 0 ∧ l v ≠ 0 ∧
      T.LocallyGenerated (LinearMap.ker l) ∧ T.RelayFeasible (LinearMap.ker l) ∧
      finrank K (LinearMap.ker l) + 1 = finrank K F := by
  obtain ⟨l,hU,hlb,hlv⟩ := exists_annihilating_form_two (T.U 0) b v hbU hvU
  obtain ⟨hg,hf⟩ := hyperplane_relay T l hspan hU a b c ha hb hc hrel hlb
  have hn : l ≠ 0 := by intro hz; exact hlb (by simp [hz])
  exact ⟨l,hU,hlb,hlv,hg,hf,Module.Dual.finrank_ker_add_one_of_ne_zero hn⟩

/-- Exact rank loss for the unprotected remote pair is at most one. -/
theorem hyperplane_condRank_loss_le_one (A B : Submodule K F) (l : F →ₗ[K] K) :
    condRank B A ≤ condRank (B ⊓ LinearMap.ker l) (A ⊓ LinearMap.ker l) + 1 := by
  have hloss := kernel_condRank_loss l B A
  have hd := Submodule.finrank_le (LinearMap.range (l.comp B.subtype))
  rw [Module.finrank_self] at hd
  omega

/-- One protected remote intersection attains maximal rank. The other
remote conditional rank can lose at most one. These are actual kernel ranks. -/
theorem exists_binary_hyperplane_protected_rank
    (T : Task K F) (hspan : T.Spanning)
    (a b c : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a+b+c=0) (hbU : b ∉ T.U 0)
    (hremote : ¬ T.U 1 ⊓ T.U 2 ≤ T.U 0)
    (hC : Disjoint (T.A 1 ⊓ (T.U 1 ⊓ T.U 2)) (T.U 0))
    (m p : ℕ) (hp : finrank K ↥(T.U 1 ⊓ T.U 2) = p)
    (hr : condRank (T.U 1 ⊓ T.U 2) (T.A 1) = min m p) :
    ∃ l : F →ₗ[K] K,
      T.U 0 ≤ LinearMap.ker l ∧ T.LocallyGenerated (LinearMap.ker l) ∧
      T.RelayFeasible (LinearMap.ker l) ∧
      finrank K (LinearMap.ker l)+1=finrank K F ∧
      finrank K ↥((T.U 1 ⊓ T.U 2) ⊓ LinearMap.ker l)+1=p ∧
      condRank ((T.U 1 ⊓ T.U 2) ⊓ LinearMap.ker l)
        (T.A 1 ⊓ LinearMap.ker l)=min m (p-1) ∧
      condRank (T.U 1 ⊓ T.U 2) (T.A 2) ≤
        condRank ((T.U 1 ⊓ T.U 2) ⊓ LinearMap.ker l)
          (T.A 2 ⊓ LinearMap.ker l)+1 := by
  obtain ⟨v,hv,hvU,hvC⟩ := exists_rank_witness
    (T.A 1 ⊓ (T.U 1 ⊓ T.U 2)) (T.U 1 ⊓ T.U 2) (T.U 0) inf_le_right hC hremote
  obtain ⟨l,hU,_,hlv,hg,hf,hd⟩ :=
    exists_binary_hyperplane_relay T hspan a b c v ha hb hc hrel hbU hvU
  refine ⟨l,hU,hg,hf,hd,?_,?_,hyperplane_condRank_loss_le_one _ _ _⟩
  · simpa [hp] using hyperplane_intersection_finrank _ l ⟨v,hv,hlv⟩
  · exact hyperplane_pair_maximal_rank _ _ l m p hp hr ⟨v,hv,hlv⟩
      (fun h => ⟨v,hvC h,hlv⟩)

/-- In the original binary menus one remote intersection is zero, so
protecting the other is enough to preserve both maximal pair ranks. -/
theorem exists_binary_hyperplane_remote_ranks
    (T : Task K F) (hspan : T.Spanning)
    (a b c : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a+b+c=0) (hbU : b ∉ T.U 0)
    (hremote : ¬ T.U 1 ⊓ T.U 2 ≤ T.U 0)
    (hC : Disjoint (T.A 1 ⊓ (T.U 1 ⊓ T.U 2)) (T.U 0))
    (hzero : T.A 2 ⊓ (T.U 1 ⊓ T.U 2) = ⊥)
    (m₁ m₂ p : ℕ) (hp : finrank K ↥(T.U 1 ⊓ T.U 2) = p)
    (hr₁ : condRank (T.U 1 ⊓ T.U 2) (T.A 1) = min m₁ p)
    (hr₂ : condRank (T.U 1 ⊓ T.U 2) (T.A 2) = min m₂ p) :
    ∃ l : F →ₗ[K] K,
      T.U 0 ≤ LinearMap.ker l ∧ T.LocallyGenerated (LinearMap.ker l) ∧
      T.RelayFeasible (LinearMap.ker l) ∧
      finrank K (LinearMap.ker l)+1=finrank K F ∧
      condRank ((T.U 1 ⊓ T.U 2) ⊓ LinearMap.ker l)
        (T.A 1 ⊓ LinearMap.ker l)=min m₁ (p-1) ∧
      condRank ((T.U 1 ⊓ T.U 2) ⊓ LinearMap.ker l)
        (T.A 2 ⊓ LinearMap.ker l)=min m₂ (p-1) := by
  obtain ⟨v,hv,hvU,hvC⟩ := exists_rank_witness
    (T.A 1 ⊓ (T.U 1 ⊓ T.U 2)) (T.U 1 ⊓ T.U 2) (T.U 0) inf_le_right hC hremote
  obtain ⟨l,hU,_,hlv,hg,hf,hd⟩ :=
    exists_binary_hyperplane_relay T hspan a b c v ha hb hc hrel hbU hvU
  refine ⟨l,hU,hg,hf,hd,?_,?_⟩
  · exact hyperplane_pair_maximal_rank _ _ l m₁ p hp hr₁ ⟨v,hv,hlv⟩
      (fun h => ⟨v,hvC h,hlv⟩)
  · exact hyperplane_pair_maximal_rank (T.A 2) (T.U 1 ⊓ T.U 2) l m₂ p hp hr₂ ⟨v,hv,hlv⟩
      (by intro h; rw [hzero,finrank_bot] at h; omega)

/-- Actual binary codimension-two relay with the two selected remote lines
protected, one for each form. The relation determinant is geometric input. -/
theorem exists_binary_codimTwo_relay
    (T : Task K F) (hspan : T.Spanning)
    (r w : LinearMap.ker (AlignedRelation.signalSum T.A))
    (hB : relationWedge T r w ≠ 0) (v z : F)
    (hv : v ∉ T.U 0) (hz : z ∉ T.U 1) :
    ∃ l₁ l₂ : F →ₗ[K] K,
      T.U 0 ≤ LinearMap.ker l₁ ∧ T.U 1 ≤ LinearMap.ker l₂ ∧
      l₁ v ≠ 0 ∧ l₂ z ≠ 0 ∧
      T.LocallyGenerated (LinearMap.ker l₁ ⊓ LinearMap.ker l₂) ∧
      T.RelayFeasible (LinearMap.ker l₁ ⊓ LinearMap.ker l₂) ∧
      finrank K ↥(LinearMap.ker l₁ ⊓ LinearMap.ker l₂)+2=finrank K F := by
  obtain ⟨l₁,l₂,hlv,hlz,hwedge⟩ := exists_bilinear_nonzero_with_one_constraint (K := K)
    (X := (T.U 0).dualAnnihilator) (Y := (T.U 1).dualAnnihilator)
    (relationWedge T r w) hB (annihilatorEvaluation (T.U 0) v)
    (annihilatorEvaluation (T.U 1) z)
    (annihilatorEvaluation_ne_zero _ _ hv) (annihilatorEvaluation_ne_zero _ _ hz)
  have h₁ : T.U 0 ≤ LinearMap.ker l₁.1 := by
    intro x hx; exact (Submodule.mem_dualAnnihilator l₁.1).mp l₁.property x hx
  have h₂ : T.U 1 ≤ LinearMap.ker l₂.1 := by
    intro x hx; exact (Submodule.mem_dualAnnihilator l₂.1).mp l₂.property x hx
  have hs : Function.Surjective (relationEvaluation T.A l₁.1 l₂.1) :=
    surjective_of_wedge (relationEvaluation T.A l₁.1 l₂.1) r w hwedge
  exact ⟨l₁.1,l₂.1,h₁,h₂,hlv,hlz,
    codimTwo_locally_generated T l₁.1 l₂.1 hspan h₁ h₂ hs,
    codimTwo_feasible T l₁.1 l₂.1 h₁ h₂ hs,
    codimTwo_finrank T l₁.1 l₂.1 h₁ h₂ hs⟩

end Dimensions
end UploadBroadcast.BinaryRelayMenus
