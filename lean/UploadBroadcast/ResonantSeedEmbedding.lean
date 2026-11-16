import UploadBroadcast.ResonantKernelSupport

/-! A detected full-support boundary mode gives an actual first resonant
subrepresentation. The embedding preserves all six labeled spaces. -/
namespace UploadBroadcast.ResonantSeedEmbedding
open TaskDecomposition ResonantEndomorphisms
open ResonantRelationReduction (Data boundary coupling relationSpaces)
variable {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]

def seedRow (d : Data K X Y) (y : Y × Y × Y) : K →ₗ[K] K :=
  (-coupling d y) • LinearMap.id

def seedMap (d : Data K X Y) (y : Y × Y × Y) : Ambient K K →ₗ[K] Ambient K X where
  toFun p := (p.1 • d.B₂ y.2.1,p.2.1 • d.B₁ y.1,p.2.2.1 • d.C₁ y.1,
    p.2.2.2.1+d.k₂ y.2.1*p.1,p.2.2.2.2+d.k₁ y.1*p.2.1)
  map_add' _ _ := by ext <;> simp [add_smul,mul_add] <;> ring
  map_smul' _ _ := by ext <;> simp [smul_smul,smul_add,smul_eq_mul] <;> ring

theorem seedMap_injective (d : Data K X Y) (y : Y × Y × Y)
    (ha : d.B₂ y.2.1≠0) (hb : d.B₁ y.1≠0) (hc : d.C₁ y.1≠0) :
    Function.Injective (seedMap d y) := by
  intro p q he
  have h₁ : p.1=q.1 := smul_left_injective K ha (congrArg Prod.fst he)
  have h₂ : p.2.1=q.2.1 := smul_left_injective K hb
    (congrArg (fun p : Ambient K X => p.2.1) he)
  have h₃ : p.2.2.1=q.2.2.1 := smul_left_injective K hc
    (congrArg (fun p : Ambient K X => p.2.2.1) he)
  have h₄ : p.2.2.2.1=q.2.2.2.1 := by
    have hh := congrArg (fun p : Ambient K X => p.2.2.2.1) he
    change p.2.2.2.1+d.k₂ y.2.1*p.1=q.2.2.2.1+d.k₂ y.2.1*q.1 at hh
    rw [h₁] at hh
    exact add_right_cancel hh
  have h₅ : p.2.2.2.2=q.2.2.2.2 := by
    have hh := congrArg (fun p : Ambient K X => p.2.2.2.2) he
    change p.2.2.2.2+d.k₁ y.1*p.2.1=q.2.2.2.2+d.k₁ y.1*q.2.1 at hh
    rw [h₂] at hh
    exact add_right_cancel hh
  exact Prod.ext h₁ (Prod.ext h₂ (Prod.ext h₃ (Prod.ext h₄ h₅)))

private theorem preserve_sup {V W Z : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]
    (f : V →ₗ[K] W) (A : Submodule K V) (U : Submodule K W) (d : Z →ₗ[K] V)
    (ha : ∀ x∈A,f x∈U) (hd : ∀ z,f (d z)∈U) :
    ∀ x∈A ⊔ LinearMap.range d,f x∈U := by
  intro x hx
  obtain ⟨a,ha',b,hb,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨z,rfl⟩ := hb
  rw [map_add]
  exact U.add_mem (ha a ha') (hd z)

/-- The signed kernel equation is enough to construct the whole embedding;
nonzero coupling is used only for indecomposability of its source. -/
theorem seedMap_preserves (d : Data K X Y) (y : Y × Y × Y) (hy : boundary d y=0) :
    Preserves (spaces K K 0 (seedRow d y)) (relationSpaces d) (seedMap d y) := by
  have hB : d.B₃ y.2.2= -d.B₂ y.2.1 := by
    have hh := congrArg Prod.fst hy
    exact eq_neg_of_add_eq_zero_right hh
  have hC : d.C₃ y.2.2= -d.B₁ y.1 := by
    have hh := congrArg (fun p : X × X × X => p.2.1) hy
    exact eq_neg_of_add_eq_zero_right hh
  have hD : d.C₂ y.2.1=d.C₁ y.1 := by
    have hh := congrArg (fun p : X × X × X => p.2.2) hy
    exact (sub_eq_zero.mp hh).symm
  have hs₁ : ∀ p∈side₁ K K,seedMap d y p∈side₁ K X := by
    intro p hp
    change p.2.1=0 ∧ p.2.2.1=0 ∧ p.2.2.2.2=0 at hp
    change p.2.1 • d.B₁ y.1=0 ∧ p.2.2.1 • d.C₁ y.1=0 ∧ p.2.2.2.2+d.k₁ y.1*p.2.1=0
    simp [hp.1,hp.2.1,hp.2.2]
  have hs₂ : ∀ p∈side₂ K K,seedMap d y p∈side₂ K X := by
    intro p hp
    change p.1=0 ∧ p.2.2.1=0 ∧ p.2.2.2.1=0 at hp
    change p.1 • d.B₂ y.2.1=0 ∧ p.2.2.1 • d.C₁ y.1=0 ∧ p.2.2.2.1+d.k₂ y.2.1*p.1=0
    simp [hp.1,hp.2.1,hp.2.2]
  have hs₃ : ∀ p∈side₃ K K,seedMap d y p∈side₃ K X := by
    intro p hp
    change p.1=0 ∧ p.2.1=0 ∧ p.2.2.2.1+p.2.2.2.2=0 at hp
    change p.1 • d.B₂ y.2.1=0 ∧ p.2.1 • d.B₁ y.1=0 ∧
      (p.2.2.2.1+d.k₂ y.2.1*p.1)+(p.2.2.2.2+d.k₁ y.1*p.2.1)=0
    simp [hp.1,hp.2.1,hp.2.2]
  intro i
  fin_cases i
  · exact hs₁
  · exact hs₂
  · exact hs₃
  · change ∀ p∈total₁ K K,seedMap d y p∈side₁ K X ⊔ LinearMap.range (ResonantRelationReduction.demand₁ d)
    rw [total₁_eq_side_sup_demand]
    apply preserve_sup _ _ _ _ (fun p hp => Submodule.mem_sup_left (hs₁ p hp))
    intro x
    apply Submodule.mem_sup_right
    refine ⟨x • y.1,?_⟩
    ext <;> simp [ResonantRelationReduction.demand₁,seedMap,demand₁,E₂,E₃,smul_eq_mul,mul_comm]
  · change ∀ p∈total₂ K K,seedMap d y p∈side₂ K X ⊔ LinearMap.range (ResonantRelationReduction.demand₂ d)
    rw [total₂_eq_side_sup_demand]
    apply preserve_sup _ _ _ _ (fun p hp => Submodule.mem_sup_left (hs₂ p hp))
    intro x
    apply Submodule.mem_sup_right
    refine ⟨x • y.2.1,?_⟩
    ext <;> simp [ResonantRelationReduction.demand₂,seedMap,demand₂,E₁,E₃,hD,smul_eq_mul,mul_comm]
  · change ∀ p∈total₃ K K 0 (seedRow d y),
      seedMap d y p∈side₃ K X ⊔ LinearMap.range (ResonantRelationReduction.demand₃ d)
    rw [total₃_eq_side_sup_demand]
    apply preserve_sup _ _ _ _ (fun p hp => Submodule.mem_sup_left (hs₃ p hp))
    intro x
    refine Submodule.mem_sup.mpr ⟨(0,0,0,-d.k₁ y.1*x,d.k₁ y.1*x),?_,
      ResonantRelationReduction.demand₃ d (-x • y.2.2),⟨-x • y.2.2,rfl⟩,?_⟩
    · simp [side₃]
    · ext <;> simp [ResonantRelationReduction.demand₃,seedMap,demand₃,seedRow,coupling,hB,hC,
        smul_eq_mul,smul_smul]; ring

theorem seed_indecomposable (d : Data K X Y) (y : Y × Y × Y) (hk : coupling d y≠0) :
    Indecomposable (spaces K K 0 (seedRow d y)) ⊤ := by
  apply ResonantClassification.graph_indecomposable_of_nilpotent_detecting
  · exact ⟨1,by simp⟩
  · intro x _ hx
    change -coupling d y*x=0 at hx
    exact (mul_eq_zero.mp hx).resolve_left (neg_ne_zero.mpr hk)

/-- A regular indecomposable relation model with private information contains
an actual indecomposable first resonant block. This is only the seed step;
it does not yet split a maximal chain or classify the ambient model. -/
theorem exists_resonant_seed {K X Y : Type} [Field K]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X] [Nontrivial X]
    [AddCommGroup Y] [Module K Y]
    (d : Data K X Y) (hi : Indecomposable (relationSpaces d) ⊤)
    (hd : ReflectionReduction.defect (ResonantKernelSupport.relationTask d).dimensionVector=0) :
    ∃ y : Y × Y × Y, coupling d y≠0 ∧
      Function.Injective (seedMap d y) ∧
      Preserves (spaces K K 0 (seedRow d y)) (relationSpaces d) (seedMap d y) ∧
      Indecomposable (spaces K K 0 (seedRow d y)) ⊤ := by
  obtain ⟨y,hy,hk⟩ := ResonantRelationReduction.boundary_coupling_obstruction d hi
  obtain ⟨ha,hb,hc⟩ := ResonantKernelSupport.detected_mode_full_support d hi hd y hy hk
  exact ⟨y,hk,seedMap_injective d y ha hb hc,seedMap_preserves d y hy,seed_indecomposable d y hk⟩

end UploadBroadcast.ResonantSeedEmbedding
