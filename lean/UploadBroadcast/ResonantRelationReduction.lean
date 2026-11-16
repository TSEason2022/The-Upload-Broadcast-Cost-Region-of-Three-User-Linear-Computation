import UploadBroadcast.ResonantClassification

/-! A signed relation-boundary obstruction before remote projections are invertible.
These coordinates require only a side normal form and chosen demand generators,
not graph demands. The obstruction is necessary, not a classification theorem. -/
namespace UploadBroadcast.ResonantRelationReduction
open ResonantEndomorphisms TaskDecomposition
variable {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]

/-- Three pairs of remote coefficient maps and three scalar couplings. -/
structure Data (K X Y : Type*) [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] where
  B₁ : Y →ₗ[K] X
  C₁ : Y →ₗ[K] X
  B₂ : Y →ₗ[K] X
  C₂ : Y →ₗ[K] X
  B₃ : Y →ₗ[K] X
  C₃ : Y →ₗ[K] X
  k₁ : Y →ₗ[K] K
  k₂ : Y →ₗ[K] K
  k₃ : Y →ₗ[K] K

def demand₁ (d : Data K X Y) : Y →ₗ[K] Ambient K X where
  toFun y := (0,d.B₁ y,d.C₁ y,0,d.k₁ y)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def demand₂ (d : Data K X Y) : Y →ₗ[K] Ambient K X where
  toFun y := (d.B₂ y,0,d.C₂ y,d.k₂ y,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def demand₃ (d : Data K X Y) : Y →ₗ[K] Ambient K X where
  toFun y := (d.B₃ y,d.C₃ y,0,d.k₃ y,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def relationSpaces (d : Data K X Y) : Fin 6 → Submodule K (Ambient K X) :=
  ![side₁ K X,side₂ K X,side₃ K X,
    side₁ K X ⊔ LinearMap.range (demand₁ d),
    side₂ K X ⊔ LinearMap.range (demand₂ d),
    side₃ K X ⊔ LinearMap.range (demand₃ d)]

/-- The signed hexagon boundary; no edge map is assumed invertible. -/
def boundary (d : Data K X Y) : (Y × Y × Y) →ₗ[K] (X × X × X) where
  toFun y := (d.B₂ y.2.1+d.B₃ y.2.2,d.B₁ y.1+d.C₃ y.2.2,d.C₁ y.1-d.C₂ y.2.1)
  map_add' _ _ := by ext <;> simp <;> abel
  map_smul' _ _ := by ext <;> simp [smul_add,smul_sub]

def coupling (d : Data K X Y) : (Y × Y × Y) →ₗ[K] K where
  toFun y := d.k₁ y.1+d.k₂ y.2.1+d.k₃ y.2.2
  map_add' _ _ := by simp; ring
  map_smul' _ _ := by simp; ring

def tripodProjection (f₁ f₂ f₃ : X →ₗ[K] K) : Module.End K (Ambient K X) where
  toFun p := (0,0,0,f₁ p.1-f₃ p.2.2.1+p.2.2.2.1,f₂ p.2.1+f₃ p.2.2.1+p.2.2.2.2)
  map_add' _ _ := by ext <;> simp <;> ring
  map_smul' _ _ := by ext <;> simp <;> ring

theorem tripodProjection_sides (f₁ f₂ f₃ : X →ₗ[K] K) :
    SideStable (tripodProjection f₁ f₂ f₃) := by
  constructor
  · intro p hp
    change p.2.1=0 ∧ p.2.2.1=0 ∧ p.2.2.2.2=0 at hp
    change (0:X)=0 ∧ (0:X)=0 ∧ f₂ p.2.1+f₃ p.2.2.1+p.2.2.2.2=0
    simp [hp.1,hp.2.1,hp.2.2]
  · intro p hp
    change p.1=0 ∧ p.2.2.1=0 ∧ p.2.2.2.1=0 at hp
    change (0:X)=0 ∧ (0:X)=0 ∧ f₁ p.1-f₃ p.2.2.1+p.2.2.2.1=0
    simp [hp.1,hp.2.1,hp.2.2]
  · intro p hp
    change p.1=0 ∧ p.2.1=0 ∧ p.2.2.2.1+p.2.2.2.2=0 at hp
    change (0:X)=0 ∧ (0:X)=0 ∧
      (f₁ p.1-f₃ p.2.2.1+p.2.2.2.1)+(f₂ p.2.1+f₃ p.2.2.1+p.2.2.2.2)=0
    simp only [hp.1,hp.2.1,map_zero,zero_sub,zero_add]
    exact ⟨True.intro,True.intro,by linear_combination hp.2.2⟩

private theorem stable_sup_range {V Z : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup Z] [Module K Z] (A : Submodule K V) (d : Z →ₗ[K] V) (f : Module.End K V)
    (hA : ∀ x∈A,f x∈A) (hd : ∀ z,f (d z)∈A) :
    ∀ x∈A ⊔ LinearMap.range d,f x∈A ⊔ LinearMap.range d := by
  intro x hx
  obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨z,rfl⟩ := hb
  rw [map_add]
  exact Submodule.mem_sup_left (A.add_mem (hA a ha) (hd z))

/-- Solving the three row equations constructs a nontrivial stable projection. -/
theorem tripodProjection_stable (d : Data K X Y) (f₁ f₂ f₃ : X →ₗ[K] K)
    (h₁ : ∀ y,f₂ (d.B₁ y)+f₃ (d.C₁ y)+d.k₁ y=0)
    (h₂ : ∀ y,f₁ (d.B₂ y)-f₃ (d.C₂ y)+d.k₂ y=0)
    (h₃ : ∀ y,f₁ (d.B₃ y)+f₂ (d.C₃ y)+d.k₃ y=0) :
    Stable (relationSpaces d) (tripodProjection f₁ f₂ f₃) := by
  have hs := tripodProjection_sides f₁ f₂ f₃
  intro i
  fin_cases i
  · exact hs.one
  · exact hs.two
  · exact hs.three
  · apply stable_sup_range _ _ _ hs.one
    intro y
    change (0:X)=0 ∧ (0:X)=0 ∧ f₂ (d.B₁ y)+f₃ (d.C₁ y)+d.k₁ y=0
    exact ⟨rfl,rfl,h₁ y⟩
  · apply stable_sup_range _ _ _ hs.two
    intro y
    change (0:X)=0 ∧ (0:X)=0 ∧ f₁ (d.B₂ y)-f₃ (d.C₂ y)+d.k₂ y=0
    exact ⟨rfl,rfl,h₂ y⟩
  · apply stable_sup_range _ _ _ hs.three
    intro y
    change (0:X)=0 ∧ (0:X)=0 ∧
      (f₁ (d.B₃ y)-f₃ 0+d.k₃ y)+(f₂ (d.C₃ y)+f₃ 0+0)=0
    refine ⟨rfl,rfl,?_⟩
    simp only [map_zero,sub_zero,add_zero]
    linear_combination h₃ y

/-- Kernel containment gives a row factorization for a rectangular map. -/
theorem row_factors {Z W : Type*} [AddCommGroup Z] [Module K Z]
    [AddCommGroup W] [Module K W] (D : Z →ₗ[K] W) (h : Z →ₗ[K] K)
    (hh : LinearMap.ker D ≤ LinearMap.ker h) :
    ∃ g : W →ₗ[K] K, ∀ z,h z=g (D z) := by
  let q := (LinearMap.ker D).liftQ h hh
  let l := q.comp D.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g,hg⟩ := l.exists_extend
  refine ⟨g,fun z => ?_⟩
  have he := LinearMap.congr_fun hg (⟨D z,⟨z,rfl⟩⟩ : LinearMap.range D)
  simpa [l,q,LinearMap.quotKerEquivRange_symm_apply_image] using he.symm

private theorem row_decomposition (g : (X × X × X) →ₗ[K] K) (p : X × X × X) :
    g p=g (p.1,0,0)+g (0,p.2.1,0)+g (0,0,p.2.2) := by
  rw [←map_add,←map_add]
  congr 1
  ext <;> simp

/-- A coupling row factoring through the signed boundary solves all three
tripod projection equations, without inverting a single remote edge map. -/
theorem row_equations_of_factor (d : Data K X Y) (g : (X × X × X) →ₗ[K] K)
    (hg : ∀ y,coupling d y=g (boundary d y)) :
    ∃ f₁ f₂ f₃ : X →ₗ[K] K,
      (∀ y,f₂ (d.B₁ y)+f₃ (d.C₁ y)+d.k₁ y=0) ∧
      (∀ y,f₁ (d.B₂ y)-f₃ (d.C₂ y)+d.k₂ y=0) ∧
      (∀ y,f₁ (d.B₃ y)+f₂ (d.C₃ y)+d.k₃ y=0) := by
  let e₁ : X →ₗ[K] (X × X × X) := LinearMap.inl K X (X × X)
  let e₂ : X →ₗ[K] (X × X × X) :=
    (LinearMap.inr K X (X × X)).comp (LinearMap.inl K X X)
  let e₃ : X →ₗ[K] (X × X × X) :=
    (LinearMap.inr K X (X × X)).comp (LinearMap.inr K X X)
  refine ⟨-(g.comp e₁),-(g.comp e₂),-(g.comp e₃),?_,?_,?_⟩
  · intro y
    have he := hg (y,0,0)
    change d.k₁ y+d.k₂ 0+d.k₃ 0=g (d.B₂ 0+d.B₃ 0,d.B₁ y+d.C₃ 0,d.C₁ y-d.C₂ 0) at he
    simp only [map_zero,zero_add,add_zero,sub_zero] at he
    rw [row_decomposition] at he
    simp only [Prod.mk_zero_zero,map_zero,zero_add] at he
    change -g (0,d.B₁ y,0)+ -g (0,0,d.C₁ y)+d.k₁ y=0
    linear_combination he
  · intro y
    have he := hg (0,y,0)
    change d.k₁ 0+d.k₂ y+d.k₃ 0=g (d.B₂ y+d.B₃ 0,d.B₁ 0+d.C₃ 0,d.C₁ 0-d.C₂ y) at he
    simp only [map_zero,zero_add,add_zero,zero_sub] at he
    rw [row_decomposition] at he
    have hneg : g (0,0,-d.C₂ y)= -g (0,0,d.C₂ y) := by simpa using g.map_neg (0,0,d.C₂ y)
    rw [hneg] at he
    simp only [Prod.mk_zero_zero,map_zero,add_zero] at he
    change -g (d.B₂ y,0,0)- -g (0,0,d.C₂ y)+d.k₂ y=0
    linear_combination he
  · intro y
    have he := hg (0,0,y)
    change d.k₁ 0+d.k₂ 0+d.k₃ y=g (d.B₂ 0+d.B₃ y,d.B₁ 0+d.C₃ y,d.C₁ 0-d.C₂ 0) at he
    simp only [map_zero,zero_add,sub_zero] at he
    rw [row_decomposition] at he
    simp only [Prod.mk_zero_zero,map_zero,add_zero] at he
    change -g (d.B₃ y,0,0)+ -g (0,d.C₃ y,0)+d.k₃ y=0
    linear_combination he

/-- A nontrivial indecomposable marked relation necessarily has a boundary
kernel vector detected by the actual scalar coupling. This is a necessary
obstruction at relation level, not an assertion of graph normal form. -/
theorem boundary_coupling_obstruction [Nontrivial X] (d : Data K X Y)
    (hi : Indecomposable (relationSpaces d) ⊤) :
    ∃ y,boundary d y=0 ∧ coupling d y≠0 := by
  by_contra hn
  have hk : LinearMap.ker (boundary d) ≤ LinearMap.ker (coupling d) := by
    intro y hy
    change coupling d y=0
    by_contra hh
    exact hn ⟨y,hy,hh⟩
  obtain ⟨g,hg⟩ := row_factors (boundary d) (coupling d) hk
  obtain ⟨f₁,f₂,f₃,h₁,h₂,h₃⟩ := row_equations_of_factor d g hg
  obtain hz | ho := hi.projection_eq_zero_or_id (tripodProjection f₁ f₂ f₃)
    (tripodProjection_stable d f₁ f₂ f₃ h₁ h₂ h₃)
    (by intro p; simp [tripodProjection])
  · have he := congrArg (fun f : Module.End K (Ambient K X) => (f (scalarV K X 1)).2.2.2.1) hz
    simp [tripodProjection,scalarV] at he
  · obtain ⟨x,hx⟩ := exists_ne (0:X)
    have he := congrArg (fun f : Module.End K (Ambient K X) => (f (E₁ K X x)).1) ho
    exact hx (by simpa [tripodProjection,E₁] using he.symm)

end UploadBroadcast.ResonantRelationReduction
