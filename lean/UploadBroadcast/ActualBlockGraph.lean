import UploadBroadcast.BlockGraphDirectSum

/-! Exact block-chart presentation of the actual regrouped product task. -/
namespace UploadBroadcast.ActualBlockGraph
open Module FiniteRelayAssembly FiniteProductCoordinates ResidualUpload ResidualTaskAssembly
open BlockGraphDirectSum
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K I : Type*} [Field K]
variable {P₁ P₂ P₃ D : I → Type*}
  [∀ a, AddCommGroup (P₁ a)] [∀ a, Module K (P₁ a)]
  [∀ a, AddCommGroup (P₂ a)] [∀ a, Module K (P₂ a)]
  [∀ a, AddCommGroup (P₃ a)] [∀ a, Module K (P₃ a)]
  [∀ a, AddCommGroup (D a)] [∀ a, Module K (D a)]

def ambientChart : Ambient (∀ a, P₁ a) (∀ a, P₂ a) (∀ a, P₃ a) (∀ a, D a) ≃ₗ[K]
    (∀ a, Ambient (P₁ a) (P₂ a) (P₃ a) (D a)) where
  toFun x a := (((x.1.1.1 a,x.1.1.2 a),x.1.2 a),(x.2.1 a,x.2.2 a))
  invFun x := (((fun a => (x a).1.1.1,fun a => (x a).1.1.2),fun a => (x a).1.2),
    (fun a => (x a).2.1,fun a => (x a).2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Three
variable {X Y Z : I → Type*}
  [∀ a, AddCommGroup (X a)] [∀ a, Module K (X a)]
  [∀ a, AddCommGroup (Y a)] [∀ a, Module K (Y a)]
  [∀ a, AddCommGroup (Z a)] [∀ a, Module K (Z a)]

def tripleChart : (((∀ a, X a) × (∀ a, Y a)) × (∀ a, Z a)) ≃ₗ[K]
    (∀ a, (X a × Y a) × Z a) where
  toFun x a := ((x.1.1 a,x.1.2 a),x.2 a)
  invFun x := ((fun a => (x a).1.1,fun a => (x a).1.2),fun a => (x a).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end Three

variable (T : ∀ a, Task K (Ambient (P₁ a) (P₂ a) (P₃ a) (D a)))

def combinedTask : Task K (Ambient (∀ a, P₁ a) (∀ a, P₂ a) (∀ a, P₃ a) (∀ a, D a)) :=
  Profile.mapTask (ambientChart (K:=K)).symm (task T)

theorem signal_mem (i : Three) (x : Ambient (∀ a, P₁ a) (∀ a, P₂ a) (∀ a, P₃ a) (∀ a, D a)) :
    x ∈ (combinedTask T).U i ↔ ∀ a, ambientChart (K:=K) x a ∈ (T a).U i := by
  constructor
  · rintro ⟨y,hy,rfl⟩ a
    exact hy a trivial
  · intro hx
    exact ⟨ambientChart (K:=K) x,fun a _ => hx a,rfl⟩

theorem quotientSignal₁_map :
    (quotientSignal₁ (combinedTask T)).map (tripleChart (K:=K)).toLinearMap =
      space (fun a => quotientSignal₁ (T a)) := by
  unfold quotientSignal₁ combinedTask
  change (((space fun a => (T a).U 0).map (ambientChart (K:=K)).symm.toLinearMap).map
    demandQuotient₁).map (tripleChart (K:=K)).toLinearMap = _
  rw [←Submodule.map_comp,←Submodule.map_comp]
  exact blocks_image (fun a => demandQuotient₁ (K:=K) (P₁:=P₁ a)) (fun a => (T a).U 0)

theorem quotientSignal₂_map :
    (quotientSignal₂ (combinedTask T)).map (tripleChart (K:=K)).toLinearMap =
      space (fun a => quotientSignal₂ (T a)) := by
  unfold quotientSignal₂ combinedTask
  change (((space fun a => (T a).U 1).map (ambientChart (K:=K)).symm.toLinearMap).map
    demandQuotient₂).map (tripleChart (K:=K)).toLinearMap = _
  rw [←Submodule.map_comp,←Submodule.map_comp]
  exact blocks_image (fun a => demandQuotient₂ (K:=K) (P₂:=P₂ a)) (fun a => (T a).U 1)

theorem quotientSignal₃_map :
    (quotientSignal₃ (combinedTask T)).map (tripleChart (K:=K)).toLinearMap =
      space (fun a => quotientSignal₃ (T a)) := by
  unfold quotientSignal₃ combinedTask
  change (((space fun a => (T a).U 2).map (ambientChart (K:=K)).symm.toLinearMap).map
    demandQuotient₃).map (tripleChart (K:=K)).toLinearMap = _
  rw [←Submodule.map_comp,←Submodule.map_comp]
  exact blocks_image (fun a => demandQuotient₃ (K:=K) (P₃:=P₃ a)) (fun a => (T a).U 2)

section General
variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

lemma equiv_mem_iff (A : Submodule K V) (B : Submodule K W) (e : V ≃ₗ[K] W)
    (h : A.map e.toLinearMap = B) (x : V) : x ∈ A ↔ e x ∈ B := by
  rw [←h]
  constructor
  · intro hx; exact ⟨x,hx,rfl⟩
  · rintro ⟨y,hy,he⟩
    exact e.injective he ▸ hy

lemma mem_map_fst (Q : Submodule K (V × W)) (p : V) :
    p ∈ Q.map (LinearMap.fst K V W) ↔ ∃ d, (p,d) ∈ Q := by
  constructor
  · rintro ⟨x,hx,he⟩
    exact ⟨x.2,he ▸ hx⟩
  · rintro ⟨d,hd⟩
    exact ⟨(p,d),hd,rfl⟩
end General

theorem quotientSignal₁_mem (x : ((∀ a, P₂ a) × (∀ a, P₃ a)) × (∀ a, D a)) :
    x ∈ quotientSignal₁ (combinedTask T) ↔ ∀ a, tripleChart (K:=K) x a ∈ quotientSignal₁ (T a) := by
  exact (equiv_mem_iff _ _ (tripleChart (K:=K)) (quotientSignal₁_map T) x).trans
    (by simp only [space,Submodule.mem_pi,Set.mem_univ,forall_const])

theorem quotientSignal₂_mem (x : ((∀ a, P₁ a) × (∀ a, P₃ a)) × (∀ a, D a)) :
    x ∈ quotientSignal₂ (combinedTask T) ↔ ∀ a, tripleChart (K:=K) x a ∈ quotientSignal₂ (T a) := by
  exact (equiv_mem_iff _ _ (tripleChart (K:=K)) (quotientSignal₂_map T) x).trans
    (by simp only [space,Submodule.mem_pi,Set.mem_univ,forall_const])

theorem quotientSignal₃_mem (x : ((∀ a, P₁ a) × (∀ a, P₂ a)) × (∀ a, D a)) :
    x ∈ quotientSignal₃ (combinedTask T) ↔ ∀ a, tripleChart (K:=K) x a ∈ quotientSignal₃ (T a) := by
  exact (equiv_mem_iff _ _ (tripleChart (K:=K)) (quotientSignal₃_map T) x).trans
    (by simp only [space,Submodule.mem_pi,Set.mem_univ,forall_const])

theorem privateDomain₁_mem (p : (∀ a, P₂ a) × (∀ a, P₃ a)) :
    p ∈ privateDomain₁ (combinedTask T) ↔ ∀ a, (p.1 a,p.2 a) ∈ privateDomain₁ (T a) := by
  simp only [privateDomain₁,mem_map_fst,quotientSignal₁_mem]
  constructor
  · rintro ⟨d,hd⟩ a
    exact ⟨d a,hd a⟩
  · intro h
    choose d hd using h
    exact ⟨d,hd⟩

theorem privateDomain₂_mem (p : (∀ a, P₁ a) × (∀ a, P₃ a)) :
    p ∈ privateDomain₂ (combinedTask T) ↔ ∀ a, (p.1 a,p.2 a) ∈ privateDomain₂ (T a) := by
  simp only [privateDomain₂,mem_map_fst,quotientSignal₂_mem]
  constructor
  · rintro ⟨d,hd⟩ a
    exact ⟨d a,hd a⟩
  · intro h
    choose d hd using h
    exact ⟨d,hd⟩

theorem privateDomain₃_mem (p : (∀ a, P₁ a) × (∀ a, P₂ a)) :
    p ∈ privateDomain₃ (combinedTask T) ↔ ∀ a, (p.1 a,p.2 a) ∈ privateDomain₃ (T a) := by
  simp only [privateDomain₃,mem_map_fst,quotientSignal₃_mem]
  constructor
  · rintro ⟨d,hd⟩ a
    exact ⟨d a,hd a⟩
  · intro h
    choose d hd using h
    exact ⟨d,hd⟩

theorem pureRows₁_eq : pureRows₁ (combinedTask T) = space (fun a => pureRows₁ (T a)) := by
  ext d
  change ((0,d) ∈ quotientSignal₁ (combinedTask T)) ↔ _
  rw [quotientSignal₁_mem]
  simp only [space,Submodule.mem_pi,Set.mem_univ,forall_const]
  rfl

theorem pureRows₂_eq : pureRows₂ (combinedTask T) = space (fun a => pureRows₂ (T a)) := by
  ext d
  change ((0,d) ∈ quotientSignal₂ (combinedTask T)) ↔ _
  rw [quotientSignal₂_mem]
  simp only [space,Submodule.mem_pi,Set.mem_univ,forall_const]
  rfl

theorem pureRows₃_eq : pureRows₃ (combinedTask T) = space (fun a => pureRows₃ (T a)) := by
  ext d
  change ((0,d) ∈ quotientSignal₃ (combinedTask T)) ↔ _
  rw [quotientSignal₃_mem]
  simp only [space,Submodule.mem_pi,Set.mem_univ,forall_const]
  rfl

variable (g : ∀ a, DemandData (T a))

/-- The actual combined task's graph presentation is constructed from the
chosen component graph lifts, not supplied as a rank certificate. -/
def combinedData : DemandData (combinedTask T) where
  φ₁ := (blocks fun a => (g a).φ₁).comp (piProdEquiv (K:=K)).toLinearMap
  φ₂ := (blocks fun a => (g a).φ₂).comp (piProdEquiv (K:=K)).toLinearMap
  φ₃ := (blocks fun a => (g a).φ₃).comp (piProdEquiv (K:=K)).toLinearMap
  mem₁ x := by
    rw [signal_mem,privateDomain₁_mem,pureRows₁_eq]
    simp only [space,Submodule.mem_pi,Set.mem_univ,forall_const]
    rw [←forall_and]
    exact forall_congr' fun a => (g a).mem₁ (ambientChart (K:=K) x a)
  mem₂ x := by
    rw [signal_mem,privateDomain₂_mem,pureRows₂_eq]
    simp only [space,Submodule.mem_pi,Set.mem_univ,forall_const]
    rw [←forall_and]
    exact forall_congr' fun a => (g a).mem₂ (ambientChart (K:=K) x a)
  mem₃ x := by
    rw [signal_mem,privateDomain₃_mem,pureRows₃_eq]
    simp only [space,Submodule.mem_pi,Set.mem_univ,forall_const]
    rw [←forall_and]
    exact forall_congr' fun a => (g a).mem₃ (ambientChart (K:=K) x a)

section Domain
variable {X Y : I → Type*}
  [∀ a, AddCommGroup (X a)] [∀ a, Module K (X a)]
  [∀ a, AddCommGroup (Y a)] [∀ a, Module K (Y a)]

def domainChart (A : Submodule K ((∀ a, X a) × (∀ a, Y a)))
    (C : ∀ a, Submodule K (X a × Y a))
    (h : ∀ p, p ∈ A ↔ ∀ a, (p.1 a,p.2 a) ∈ C a) : A ≃ₗ[K] (∀ a, C a) where
  toFun p a := ⟨(p.val.1 a,p.val.2 a),(h p.val).mp p.property a⟩
  invFun p := ⟨(fun a => (p a).val.1,fun a => (p a).val.2),
    (h _).mpr (fun a => (p a).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end Domain

/-- The actual combined remote-private demand domains identify with the
component domains, respecting every coefficient and all three user labels. -/
def relationChart : DemandData.Relations (task := combinedTask T) ≃ₗ[K]
    (∀ a, DemandData.Relations (task := T a)) :=
  (((domainChart _ _ (privateDomain₁_mem T)).prodCongr
    (domainChart _ _ (privateDomain₂_mem T))).prodCongr
      (domainChart _ _ (privateDomain₃_mem T))).trans (relationRegroup T)

def actualB : DemandData.Relations (task := combinedTask T) →ₗ[K]
    (((∀ a, P₁ a) × (∀ a, P₂ a)) × (∀ a, P₃ a)) :=
  DemandData.incidence (task := combinedTask T)

/-- Source B for the actual combined DemandData is conjugate to the block sum. -/
theorem incidence_conjugacy :
    (tripleChart (K:=K)).toLinearMap.comp (actualB T) =
      (blocks (componentB T)).comp (relationChart T).toLinearMap := rfl

def actualPureSum : Submodule K (∀ a, D a) :=
  pureRows₁ (combinedTask T) ⊔ pureRows₂ (combinedTask T) ⊔ pureRows₃ (combinedTask T)

theorem pureSum_eq : actualPureSum T = space (pureSum T) := by
  unfold actualPureSum pureSum
  rw [pureRows₁_eq,pureRows₂_eq,pureRows₃_eq,←space_sup,←space_sup]

noncomputable def actualQuotientChart :
    ((∀ a, D a) ⧸ actualPureSum T) ≃ₗ[K] (∀ a, D a ⧸ pureSum T a) :=
  (Submodule.quotEquivOfEq _ _ (pureSum_eq T)).trans (quotientChart (pureSum T))

@[simp] theorem actualQuotientChart_mk (x : ∀ a, D a) :
    actualQuotientChart T ((actualPureSum T).mkQ x) =
      fun a => (pureSum T a).mkQ (x a) := rfl

def actualG : DemandData.Relations (task := combinedTask T) →ₗ[K]
    ((∀ a, D a) ⧸ actualPureSum T) :=
  (actualPureSum T).mkQ.comp (combinedData T g).relationRows

/-- Source G for the actual combined DemandData is conjugate to the block sum;
the codomain chart is the proved quotient-by-pure-rows equivalence. -/
theorem graph_conjugacy :
    (actualQuotientChart T).toLinearMap.comp (actualG T g) =
      (blocks (componentG T g)).comp (relationChart T).toLinearMap := by
  apply LinearMap.ext
  intro x
  funext a
  rfl

/-- Cancellation kernels of the actual signed incidence map are identified
coefficient by coefficient, using the proved incidence conjugacy. -/
def actualKernelChart : LinearMap.ker (actualB T) ≃ₗ[K]
    (∀ a, LinearMap.ker (componentB T a)) where
  toFun x a := ⟨relationChart T x.val a,by
    have hh := congrArg (fun z => tripleChart (K:=K) z a) x.property
    exact hh⟩
  invFun x := ⟨(relationChart T).symm (fun a => (x a).val),by
    apply (tripleChart (K:=K) (X:=P₁) (Y:=P₂) (Z:=P₃)).injective
    exact funext fun a => (x a).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual source restriction G|ker B, not a separately postulated map. -/
def actualG0 : LinearMap.ker (actualB T) →ₗ[K] ((∀ a, D a) ⧸ actualPureSum T) :=
  (actualG T g).comp (LinearMap.ker (actualB T)).subtype

/-- Literal source equation (xi-block) for the actual combined Task and its
constructed DemandData, with both genuine coefficient charts displayed. -/
theorem G0_direct_sum :
    ((actualQuotientChart T).toLinearMap.comp (actualG0 T g) :
      LinearMap.ker (actualB T) →ₗ[K] (∀ a, D a ⧸ pureSum T a)) =
      (blocks (K:=K) (X:=fun a => LinearMap.ker (componentB T a))
        (Y:=fun a => D a ⧸ pureSum T a) (componentG0 T g)).comp
          (actualKernelChart T).toLinearMap := by
  apply LinearMap.ext
  intro x
  funext a
  rfl

/-- The actual mixed-row image, in the genuine quotient coordinate chart,
is exactly the product of the component mixed-row images. -/
theorem mixed_image :
    ((LinearMap.ker (actualB T)).map (actualG T g)).map (actualQuotientChart T).toLinearMap =
      space (fun a => (LinearMap.ker (componentB T a)).map (componentG T g a)) := by
  classical
  ext y
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩ a _
    exact ⟨relationChart T x a,(actualKernelChart T ⟨x,hx⟩ a).property,rfl⟩
  · intro hy
    have hh : ∀ a, ∃ x ∈ LinearMap.ker (componentB T a), componentG T g a x = y a :=
      fun a => hy a trivial
    choose x hx he using hh
    let z := (actualKernelChart T).symm (fun a => ⟨x a,hx a⟩)
    refine ⟨actualG T g z.val,⟨z.val,z.property,rfl⟩,?_⟩
    exact funext he

/-- Individual d_mix additivity is computed from the source incidence and
demand-graph maps of the actual combined task over the original field. -/
theorem mixed_rank_additive [Fintype I] [∀ a, FiniteDimensional K (D a)] :
    finrank K ((LinearMap.ker (DemandData.incidence (task:=combinedTask T))).map
      ((actualPureSum T).mkQ.comp (combinedData T g).relationRows)) =
      ∑ a, finrank K ((LinearMap.ker (DemandData.incidence (task:=T a))).map
        ((pureSum T a).mkQ.comp (g a).relationRows)) := by
  change finrank K ((LinearMap.ker (actualB T)).map (actualG T g)) = _
  rw [←(actualQuotientChart T).finrank_map_eq,mixed_image,finrank_space]
  rfl

/-- Common pure rows in the actual combined task add componentwise. -/
theorem common_rank_additive [Fintype I] [∀ a, FiniteDimensional K (D a)] :
    finrank K ↥(pureRows₁ (combinedTask T) ⊓ pureRows₂ (combinedTask T) ⊓
      pureRows₃ (combinedTask T)) =
      ∑ a, finrank K ↥(pureRows₁ (T a) ⊓ pureRows₂ (T a) ⊓ pureRows₃ (T a)) := by
  rw [pureRows₁_eq,pureRows₂_eq,pureRows₃_eq,←space_inf,←space_inf,finrank_space]

/-- The noncommon pure quotient term adds independently of d_mix. -/
theorem pure_rank_additive [Fintype I] [∀ a, FiniteDimensional K (D a)] :
    finrank K (actualPureSum T) -
      finrank K ↥(pureRows₁ (combinedTask T) ⊓ pureRows₂ (combinedTask T) ⊓
        pureRows₃ (combinedTask T)) =
      ∑ a, (finrank K (pureSum T a) -
        finrank K ↥(pureRows₁ (T a) ⊓ pureRows₂ (T a) ⊓ pureRows₃ (T a))) := by
  rw [pureSum_eq,finrank_space,common_rank_additive]
  exact (Finset.sum_tsub_distrib Finset.univ fun a _ => Submodule.finrank_mono
    (show pureRows₁ (T a) ⊓ pureRows₂ (T a) ⊓ pureRows₃ (T a) ≤ pureSum T a from
      le_trans (le_trans inf_le_left inf_le_left) (le_trans le_sup_left le_sup_left))).symm

/-- The source retained-tripod formula is individually additive for these
actual graph presentations, in addition to its separate pure and mixed terms. -/
theorem tripod_rank_additive [Fintype I] [∀ a, FiniteDimensional K (D a)] :
    (finrank K (actualPureSum T) -
      finrank K ↥(pureRows₁ (combinedTask T) ⊓ pureRows₂ (combinedTask T) ⊓
        pureRows₃ (combinedTask T))) +
      finrank K ((LinearMap.ker (actualB T)).map (actualG T g)) =
      ∑ a, ((finrank K (pureSum T a) -
        finrank K ↥(pureRows₁ (T a) ⊓ pureRows₂ (T a) ⊓ pureRows₃ (T a))) +
        finrank K ((LinearMap.ker (componentB T a)).map (componentG T g a))) := by
  rw [pure_rank_additive]
  have hh := mixed_rank_additive T g
  change finrank K ((LinearMap.ker (actualB T)).map (actualG T g)) = _ at hh
  rw [hh,Finset.sum_add_distrib]
  rfl

end UploadBroadcast.ActualBlockGraph
