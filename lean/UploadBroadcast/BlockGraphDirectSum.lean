import UploadBroadcast.ResidualTaskAssembly
import UploadBroadcast.FiniteProductCoordinates

/-! Literal direct sums of the manuscript's B, G and restricted G0 maps.
The domains are the actual demand subspaces of component tasks; the grouped
user-domain chart and cancellation-kernel chart are explicit equivalences. -/
namespace UploadBroadcast.BlockGraphDirectSum
open Module FiniteRelayAssembly FiniteProductCoordinates ResidualUpload ResidualTaskAssembly
open scoped BigOperators
variable {K I : Type*} [Field K]

def blocks {X Y : I → Type*}
    [∀ a, AddCommMonoid (X a)] [∀ a, Module K (X a)]
    [∀ a, AddCommMonoid (Y a)] [∀ a, Module K (Y a)]
    (f : ∀ a, X a →ₗ[K] Y a) : (∀ a, X a) →ₗ[K] (∀ a, Y a) :=
  LinearMap.pi fun a => (f a).comp (LinearMap.proj a)

section PiMaps
variable {X Y Z : I → Type*}
  [∀ a, AddCommGroup (X a)] [∀ a, Module K (X a)]
  [∀ a, AddCommGroup (Y a)] [∀ a, Module K (Y a)]
  [∀ a, AddCommGroup (Z a)] [∀ a, Module K (Z a)]

@[simp] theorem blocks_apply (f : ∀ a, X a →ₗ[K] Y a) (x : ∀ a, X a) (a : I) :
    blocks f x a = f a (x a) := rfl

theorem blocks_kernel (f : ∀ a, X a →ₗ[K] Y a) :
    LinearMap.ker (blocks f) = space (fun a => LinearMap.ker (f a)) := by
  ext x
  change (blocks f x = 0) ↔ ∀ a, a ∈ Set.univ → f a (x a) = 0
  simp only [funext_iff,blocks_apply,Pi.zero_apply,Set.mem_univ,forall_const]

def kernelEquiv (f : ∀ a, X a →ₗ[K] Y a) :
    LinearMap.ker (blocks f) ≃ₗ[K] (∀ a, LinearMap.ker (f a)) where
  toFun x a := ⟨x.val a,congrFun x.property a⟩
  invFun x := ⟨fun a => (x a).val,funext fun a => (x a).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction to private cancellation commutes literally with direct sum,
after the explicit canonical identification of their domains. -/
theorem restrict_blocks (B : ∀ a, X a →ₗ[K] Y a) (G : ∀ a, X a →ₗ[K] Z a) :
    (blocks G).comp (LinearMap.ker (blocks B)).subtype =
      (blocks fun a => (G a).comp (LinearMap.ker (B a)).subtype).comp
        (kernelEquiv B).toLinearMap := rfl

theorem blocks_image (f : ∀ a, X a →ₗ[K] Y a) (A : ∀ a, Submodule K (X a)) :
    (space A).map (blocks f) = space (fun a => (A a).map (f a)) := by
  classical
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩ a _
    exact ⟨x a,hx a trivial,rfl⟩
  · intro hy
    have hh : ∀ a, ∃ x ∈ A a, f a x = y a := fun a => hy a trivial
    choose x hx he using hh
    exact ⟨x,fun a _ => hx a,funext he⟩

theorem restricted_rank_additive [Fintype I] [∀ a, FiniteDimensional K (Z a)]
    (B : ∀ a, X a →ₗ[K] Y a) (G : ∀ a, X a →ₗ[K] Z a) :
    finrank K ((LinearMap.ker (blocks B)).map (blocks G)) =
      ∑ a, finrank K ((LinearMap.ker (B a)).map (G a)) := by
  rw [blocks_kernel,blocks_image,finrank_space]
end PiMaps

section QuotientChart
variable {D : I → Type*} [∀ a, AddCommGroup (D a)] [∀ a, Module K (D a)]
  (R : ∀ a, Submodule K (D a))

theorem quotient_blocks_kernel : LinearMap.ker (blocks fun a => (R a).mkQ) = space R := by
  rw [blocks_kernel]
  simp only [Submodule.ker_mkQ]

theorem quotient_blocks_surjective : Function.Surjective (blocks fun a => (R a).mkQ) := by
  classical
  intro y
  choose x hx using fun a => (R a).mkQ_surjective (y a)
  exact ⟨x,funext hx⟩

/-- The actual quotient by all pure rows is identified with the product of
the component pure-row quotients. No rank identity is assumed. -/
noncomputable def quotientChart : ((∀ a, D a) ⧸ space R) ≃ₗ[K] (∀ a, D a ⧸ R a) :=
  (Submodule.quotEquivOfEq _ _ (quotient_blocks_kernel R).symm).trans
    ((blocks fun a => (R a).mkQ).quotKerEquivOfSurjective (quotient_blocks_surjective R))

theorem quotientChart_mk (x : ∀ a, D a) :
    quotientChart R ((space R).mkQ x) = fun a => (R a).mkQ (x a) := rfl
end QuotientChart

section ActualGraphs
variable {P₁ P₂ P₃ D : I → Type*}
  [∀ a, AddCommGroup (P₁ a)] [∀ a, Module K (P₁ a)]
  [∀ a, AddCommGroup (P₂ a)] [∀ a, Module K (P₂ a)]
  [∀ a, AddCommGroup (P₃ a)] [∀ a, Module K (P₃ a)]
  [∀ a, AddCommGroup (D a)] [∀ a, Module K (D a)]
  (T : ∀ a, Task K (Ambient (P₁ a) (P₂ a) (P₃ a) (D a)))
  (g : ∀ a, DemandData (T a))

abbrev UserRelations :=
  ((∀ a, privateDomain₁ (T a)) × (∀ a, privateDomain₂ (T a))) ×
    (∀ a, privateDomain₃ (T a))

/-- User-first and component-first presentations of the actual demand domain. -/
def relationRegroup : UserRelations T ≃ₗ[K] (∀ a, DemandData.Relations (task := T a)) where
  toFun x a := ((x.1.1 a,x.1.2 a),x.2 a)
  invFun x := ((fun a => (x a).1.1,fun a => (x a).1.2),fun a => (x a).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pureSum (a : I) : Submodule K (D a) :=
  pureRows₁ (T a) ⊔ pureRows₂ (T a) ⊔ pureRows₃ (T a)

/-- Actual source B in the component chart. -/
def componentB (a : I) : DemandData.Relations (task := T a) →ₗ[K] ((P₁ a × P₂ a) × P₃ a) :=
  DemandData.incidence (task := T a)
/-- Actual source G includes the quotient by every pure demand row. -/
def componentG (a : I) : DemandData.Relations (task := T a) →ₗ[K] (D a ⧸ pureSum T a) :=
  (pureSum T a).mkQ.comp (g a).relationRows

def B : UserRelations T →ₗ[K] (∀ a, (P₁ a × P₂ a) × P₃ a) :=
  (blocks (componentB T)).comp (relationRegroup T).toLinearMap

def G : UserRelations T →ₗ[K] (∀ a, D a ⧸ pureSum T a) :=
  (blocks (componentG T g)).comp (relationRegroup T).toLinearMap

/-- The literal signed B formula, with no matrix rank hypotheses. -/
theorem B_apply (x : UserRelations T) (a : I) :
    B T x a = (((x.1.2 a).val.1 + (x.2 a).val.1,
      (x.1.1 a).val.1 + (x.2 a).val.2),
      (x.1.1 a).val.2 - (x.1.2 a).val.2) := rfl

theorem G_apply (x : UserRelations T) (a : I) :
    G T g x a = (pureSum T a).mkQ ((g a).φ₁ (x.1.1 a).val +
      (g a).φ₂ (x.1.2 a).val + (g a).φ₃ (x.2 a).val) := rfl

/-- Actual task membership proves that the component graph maps present the
signals of the genuine product task, rather than invented numerical data. -/
theorem product_signal_graphs (x : ∀ a, Ambient (P₁ a) (P₂ a) (P₃ a) (D a)) :
    (x ∈ (task T).U 0 ↔ ∀ a, ((x a).1.1.2,(x a).1.2) ∈ privateDomain₁ (T a) ∧
      (x a).2.2 - (g a).φ₁ ((x a).1.1.2,(x a).1.2) ∈ pureRows₁ (T a)) ∧
    (x ∈ (task T).U 1 ↔ ∀ a, ((x a).1.1.1,(x a).1.2) ∈ privateDomain₂ (T a) ∧
      (x a).2.1 - (g a).φ₂ ((x a).1.1.1,(x a).1.2) ∈ pureRows₂ (T a)) ∧
    (x ∈ (task T).U 2 ↔ ∀ a, ((x a).1.1.1,(x a).1.1.2) ∈ privateDomain₃ (T a) ∧
      ((x a).2.1 + (x a).2.2) - (g a).φ₃ ((x a).1.1.1,(x a).1.1.2) ∈ pureRows₃ (T a)) := by
  refine ⟨?_,?_,?_⟩
  · change (∀ a, a ∈ Set.univ → x a ∈ (T a).U 0) ↔ _
    simp only [Set.mem_univ,forall_const]
    exact forall_congr' fun a => (g a).mem₁ (x a)
  · change (∀ a, a ∈ Set.univ → x a ∈ (T a).U 1) ↔ _
    simp only [Set.mem_univ,forall_const]
    exact forall_congr' fun a => (g a).mem₂ (x a)
  · change (∀ a, a ∈ Set.univ → x a ∈ (T a).U 2) ↔ _
    simp only [Set.mem_univ,forall_const]
    exact forall_congr' fun a => (g a).mem₃ (x a)

/-- The selected summand-domain regrouping also regroups its cancellation kernel. -/
def cancellationChart : LinearMap.ker (B T) ≃ₗ[K]
    (∀ a, LinearMap.ker (componentB T a)) where
  toFun x a := ⟨relationRegroup T x.val a,congrFun x.property a⟩
  invFun x := ⟨(relationRegroup T).symm (fun a => (x a).val),
    by change blocks (componentB T) (fun a => (x a).val) = 0
       exact funext fun a => (x a).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def componentG0 (a : I) : LinearMap.ker (componentB T a) →ₗ[K] (D a ⧸ pureSum T a) :=
  (componentG T g a).comp (LinearMap.ker (componentB T a)).subtype

/-- The rank of G0 is the sum of component ranks, in the same actual charts. -/
theorem mixed_rank_additive [Fintype I] [∀ a, FiniteDimensional K (D a)] :
    finrank K ((LinearMap.ker (B T)).map (G T g)) =
      ∑ a, finrank K ((LinearMap.ker (componentB T a)).map (componentG T g a)) := by
  have he : (LinearMap.ker (B T)).map (G T g) =
      (LinearMap.ker (blocks (componentB T))).map (blocks (componentG T g)) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨relationRegroup T x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨(relationRegroup T).symm x,hx,rfl⟩
  rw [he]
  exact restricted_rank_additive (componentB T) (componentG T g)

/-- The two terms in d_tri add separately, and hence so does the total
retained tripod dimension in these adapted component charts. -/
theorem pure_mixed_tripod_additive [Fintype I] [∀ a, FiniteDimensional K (D a)] :
    (finrank K (space (pureSum T)) -
      finrank K (space fun a => pureRows₁ (T a) ⊓ pureRows₂ (T a) ⊓ pureRows₃ (T a))) +
      finrank K ((LinearMap.ker (B T)).map (G T g)) =
    ∑ a, ((finrank K (pureSum T a) -
      finrank K ↥(pureRows₁ (T a) ⊓ pureRows₂ (T a) ⊓ pureRows₃ (T a))) +
      finrank K ((LinearMap.ker (componentB T a)).map (componentG T g a))) := by
  rw [finrank_space,finrank_space,mixed_rank_additive]
  have hh : (∑ a, finrank K (pureSum T a)) -
      (∑ a, finrank K ↥(pureRows₁ (T a) ⊓ pureRows₂ (T a) ⊓ pureRows₃ (T a))) =
      ∑ a, (finrank K (pureSum T a) -
        finrank K ↥(pureRows₁ (T a) ⊓ pureRows₂ (T a) ⊓ pureRows₃ (T a))) :=
    (Finset.sum_tsub_distrib Finset.univ fun a _ => Submodule.finrank_mono
      (show pureRows₁ (T a) ⊓ pureRows₂ (T a) ⊓ pureRows₃ (T a) ≤ pureSum T a from
        le_trans (le_trans inf_le_left inf_le_left) (le_trans le_sup_left le_sup_left))).symm
  rw [hh,Finset.sum_add_distrib]

end ActualGraphs
end UploadBroadcast.BlockGraphDirectSum
