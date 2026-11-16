import UploadBroadcast.TripodSubobjectExclusion
import UploadBroadcast.SemistableFiltration
import UploadBroadcast.SemistableMorphisms
import UploadBroadcast.IntersectionProbes
import UploadBroadcast.QuiverEuler
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The two concrete regular-simple candidates and their actual Hom spaces.
No tube classification or Ext-duality theorem is assumed. -/
namespace UploadBroadcast.RegularTripodPair
open TaskDecomposition QuiverRepresentation TripodSubobjectExclusion
variable (K : Type) [Field K]

/-- The passive tripod T0. -/
def T₀ : TaskDecomposition.Task K (K × K) where
  A := sides K
  U := sides K
  nested _ := le_rfl

/-- The complementary thin regular object δ−T0. -/
def T₁ : TaskDecomposition.Task K K := IntersectionProbes.signalTriple.task K

theorem T₀_indec : TaskDecomposition.Indecomposable (T₀ K).spaces ⊤ := by
  apply indecomposable_of_projection_eq_zero_or_id top_ne_bot
  intro f hf hid
  obtain ⟨a,ha⟩ := tripod_scalar K f (fun i p hp => hf (i,false) p hp)
  have haa : a*a=a := by
    have he := congrArg Prod.fst (hid (1,0))
    rw [ha,ha] at he
    simpa using he
  have hz : a*(a-1)=0 := by linear_combination haa
  obtain hz | ho := mul_eq_zero.mp hz
  · left; apply LinearMap.ext; intro p; simp [ha,hz]
  · right; have ha1 := sub_eq_zero.mp ho; apply LinearMap.ext; intro p; simp [ha,ha1]

theorem T₁_indec : TaskDecomposition.Indecomposable (T₁ K).spaces ⊤ :=
  IntersectionProbes.signalTriple.indecomposable K

theorem T₀_defect : ReflectionReduction.defect (T₀ K).dimensionVector=0 := by
  simp [TaskDecomposition.Task.dimensionVector,ReflectionReduction.defect,T₀,sides_finrank,Plane]

theorem T₁_defect : ReflectionReduction.defect (T₁ K).dimensionVector=0 := by
  simp [TaskDecomposition.Task.dimensionVector,ReflectionReduction.defect,T₁,
    IntersectionProbes.Probe.task,IntersectionProbes.signalTriple]

/-- A zero-defect actual subspace of T0 is zero or the whole plane. -/
theorem T₀_regular_simple_subspaces (P : Submodule K (K × K))
    (hP : (T₀ K).componentDefect P=0) : P=⊥ ∨ P=⊤ := by
  have hdim : Module.finrank K P ≤ 2 := by
    have he := Submodule.finrank_mono (show P ≤ ⊤ from le_top)
    simpa using he
  have he : -3*(Module.finrank K P:ℤ)+
      2*((Module.finrank K ↥(sides K 0 ⊓ P):ℤ)+Module.finrank K ↥(sides K 1 ⊓ P)+
        Module.finrank K ↥(sides K 2 ⊓ P))=0 := by
    have hh := hP
    simp only [TaskDecomposition.Task.componentDefect,TaskDecomposition.Task.componentDimension,
      ReflectionReduction.defect,T₀] at hh
    linear_combination hh
  have hz : Module.finrank K P=0 ∨ Module.finrank K P=2 := by omega
  rcases hz with hz | hz
  · exact Or.inl (Submodule.finrank_eq_zero.mp hz)
  · exact Or.inr (Submodule.eq_top_of_finrank_eq (by simpa using hz))

theorem T₁_regular_simple_subspaces (P : Submodule K K) : P=⊥ ∨ P=⊤ := by
  have hdim : Module.finrank K P ≤ 1 := by
    have he := Submodule.finrank_mono (show P ≤ ⊤ from le_top)
    simpa using he
  have hz : Module.finrank K P=0 ∨ Module.finrank K P=1 := by omega
  rcases hz with hz | hz
  · exact Or.inl (Submodule.finrank_eq_zero.mp hz)
  · exact Or.inr (Submodule.eq_top_of_finrank_eq (by simpa using hz))

theorem T₀_regularSimple : (T₀ K).IsRegularSimple :=
  ⟨(T₀ K).isSemistable_of_indec (T₀_indec K) (T₀_defect K),top_ne_bot,T₀_regular_simple_subspaces K⟩

theorem T₁_regularSimple : (T₁ K).IsRegularSimple :=
  ⟨(T₁ K).isSemistable_of_indec (T₁_indec K) (T₁_defect K),top_ne_bot,fun P _ => T₁_regular_simple_subspaces K P⟩

variable {K} {F : Type} [AddCommGroup F] [Module K F]

def tripleSum (A B C : Submodule K F) : (A × B × C) →ₗ[K] F :=
  A.subtype.coprod (B.subtype.coprod C.subtype)

theorem tripleSum_range (A B C : Submodule K F) :
    LinearMap.range (tripleSum A B C)=(A ⊔ B) ⊔ C := by
  simp [tripleSum,LinearMap.range_coprod,sup_assoc]

/-- A morphism from T0 is precisely a relation among the three side spaces. -/
def T₀_hom_to_kernel (T : TaskDecomposition.Task K F) (f : Hom (T₀ K).toRep T.toRep) :
    LinearMap.ker (tripleSum (T.A 0) (T.A 1) (T.A 2)) := by
  let v := f.map .center (1,0)
  let r := f.map .center (0,1)
  have hp := (T₀ K).preservesOfHom T f
  have hv : v ∈ T.A 0 := hp (0,false) (1,0) (by simp [TaskDecomposition.Task.spaces,T₀,sides,line₁])
  have hr : r ∈ T.A 1 := hp (1,false) (0,1) (by simp [TaskDecomposition.Task.spaces,T₀,sides,line₂])
  have ht : r-v ∈ T.A 2 := by
    have hh := hp (2,false) ((0,1)-(1,0)) (by simp [TaskDecomposition.Task.spaces,T₀,sides,line₃])
    simpa only [map_sub] using hh
  refine ⟨(⟨v,hv⟩,⟨-r,(T.A 1).neg_mem hr⟩,⟨r-v,ht⟩),?_⟩
  change v+(-r+(r-v))=0
  abel

/-- The inverse relation-to-morphism construction. -/
def T₀_kernel_to_hom (T : TaskDecomposition.Task K F)
    (z : LinearMap.ker (tripleSum (T.A 0) (T.A 1) (T.A 2))) : Hom (T₀ K).toRep T.toRep := by
  let v : F := z.1.1
  let r : F := -z.1.2.1
  have hz : v+((z.1.2.1:F)+z.1.2.2)=0 := z.property
  have ht : r-v ∈ T.A 2 := by
    have he : r-v=(z.1.2.2:F) := by
      dsimp [r]
      rw [eq_neg_of_add_eq_zero_left hz]
      abel
    rw [he]; exact z.1.2.2.property
  have hside (i : Fin 3) (p : K × K) (hp : p ∈ sides K i) : planeMap K v r p ∈ T.A i := by
    fin_cases i
    · change p.2=0 at hp
      change p.1 • v+p.2 • r ∈ T.A 0
      simpa [hp] using (T.A 0).smul_mem p.1 z.1.1.property
    · change p.1=0 at hp
      change p.1 • v+p.2 • r ∈ T.A 1
      simpa only [hp,zero_smul,zero_add] using (T.A 1).smul_mem p.2 ((T.A 1).neg_mem z.1.2.1.property)
    · change p.1+p.2=0 at hp
      change p.1 • v+p.2 • r ∈ T.A 2
      have he : p.1 • v+p.2 • r=p.2 • (r-v) := by
        rw [eq_neg_of_add_eq_zero_left hp,neg_smul,smul_sub]; abel
      rw [he]; exact (T.A 2).smul_mem p.2 ht
  exact (T₀ K).homOfPreserves T (planeMap K v r) (by
    rintro ⟨i,b⟩ p hp
    cases b
    · exact hside i p hp
    · exact T.nested i (hside i p hp))

def T₀_hom_equiv_kernel (T : TaskDecomposition.Task K F) :
    Hom (T₀ K).toRep T.toRep ≃ₗ[K] LinearMap.ker (tripleSum (T.A 0) (T.A 1) (T.A 2)) where
  toFun := T₀_hom_to_kernel T
  invFun := T₀_kernel_to_hom T
  left_inv f := by
    apply (T₀ K).hom_center_ext T
    apply LinearMap.ext
    intro p
    change p.1 • f.map .center (1,0)+p.2 • -(-f.map .center (0,1))=f.map .center p
    rw [neg_neg,←map_smul,←map_smul,←map_add]
    congr 1
    change p.1 • (1,0)+p.2 • (0,1)=p
    apply Prod.ext
    · change p.1*1+p.2*0=p.1; simp
    · change p.1*0+p.2*1=p.2; simp
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext; change (1:K) • (z.1.1:F)+(0:K) • -(z.1.2.1:F)=(z.1.1:F); simp
    · apply Prod.ext
      · apply Subtype.ext
        change -((0:K) • (z.1.1:F)+(1:K) • -(z.1.2.1:F))=(z.1.2.1:F)
        simp
      · apply Subtype.ext
        change ((0:K) • (z.1.1:F)+(1:K) • -(z.1.2.1:F))-
          ((1:K) • (z.1.1:F)+(0:K) • -(z.1.2.1:F))=(z.1.2.2:F)
        simp only [zero_smul,one_smul,zero_add,add_zero]
        have hz : (z.1.1:F)+((z.1.2.1:F)+(z.1.2.2:F))=0 := z.property
        rw [eq_neg_of_add_eq_zero_left hz]
        abel
  map_add' f g := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext; rfl
    · apply Prod.ext
      · apply Subtype.ext
        change -(f.map .center (0,1)+g.map .center (0,1))=
          -f.map .center (0,1)+ -g.map .center (0,1)
        abel
      · apply Subtype.ext
        change (f.map .center (0,1)+g.map .center (0,1))-
          (f.map .center (1,0)+g.map .center (1,0))=
          (f.map .center (0,1)-f.map .center (1,0))+(g.map .center (0,1)-g.map .center (1,0))
        abel
  map_smul' a f := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext; rfl
    · apply Prod.ext
      · apply Subtype.ext; change -(a • f.map .center (0,1))=a • -f.map .center (0,1); simp
      · apply Subtype.ext
        change a • f.map .center (0,1)-a • f.map .center (1,0)=a • (f.map .center (0,1)-f.map .center (1,0))
        rw [smul_sub]

theorem T₀_hom_finrank [FiniteDimensional K F] (T : TaskDecomposition.Task K F) :
    Module.finrank K (Hom (T₀ K).toRep T.toRep)+Module.finrank K ↥((T.A 0 ⊔ T.A 1) ⊔ T.A 2)=
      Module.finrank K (T.A 0)+Module.finrank K (T.A 1)+Module.finrank K (T.A 2) := by
  have he := (tripleSum (T.A 0) (T.A 1) (T.A 2)).finrank_range_add_finrank_ker
  rw [tripleSum_range,Module.finrank_prod,Module.finrank_prod,←(T₀_hom_equiv_kernel T).finrank_eq] at he
  omega

def sideSpan (T : TaskDecomposition.Task K F) : Submodule K F := (T.A 0 ⊔ T.A 1) ⊔ T.A 2

private theorem side_le_sideSpan (T : TaskDecomposition.Task K F) (i : Fin 3) : T.A i ≤ sideSpan T := by
  fin_cases i
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

/-- Maps into T1 are exactly functionals annihilating all side information. -/
def hom_T₁_equiv_annihilator (T : TaskDecomposition.Task K F) :
    Hom T.toRep (T₁ K).toRep ≃ₗ[K] (sideSpan T).dualAnnihilator where
  toFun f := ⟨f.map .center,by
    apply (Submodule.mem_dualAnnihilator _).mpr
    have hp := T.preservesOfHom (T₁ K) f
    have hk (i : Fin 3) : T.A i ≤ LinearMap.ker (f.map .center) := by
      intro x hx
      have hh := hp (i,false) x hx
      simpa [TaskDecomposition.Task.spaces,T₁,IntersectionProbes.Probe.task,IntersectionProbes.signalTriple] using hh
    exact sup_le (sup_le (hk 0) (hk 1)) (hk 2)⟩
  invFun f := T.homOfPreserves (T₁ K) f.val (by
    rintro ⟨i,b⟩ x hx
    cases b
    · change f.val x ∈ (T₁ K).A i
      have hh := (Submodule.mem_dualAnnihilator f.val).mp f.property x (side_le_sideSpan T i hx)
      simpa [T₁,IntersectionProbes.Probe.task,IntersectionProbes.signalTriple] using hh
    · simp [TaskDecomposition.Task.spaces,T₁,IntersectionProbes.Probe.task,IntersectionProbes.signalTriple])
  left_inv f := by apply T.hom_center_ext (T₁ K); rfl
  right_inv f := by apply Subtype.ext; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem hom_T₁_finrank [FiniteDimensional K F] (T : TaskDecomposition.Task K F) :
    Module.finrank K (Hom T.toRep (T₁ K).toRep)+Module.finrank K (sideSpan T)=Module.finrank K F := by
  rw [(hom_T₁_equiv_annihilator T).finrank_eq,add_comm]
  exact Subspace.finrank_add_finrank_dualAnnihilator_eq (sideSpan T)

/-- Incoming maps from T1 are the actual three-way enlarged-space intersection. -/
theorem T₁_hom_finrank (T : TaskDecomposition.Task K F) :
    Module.finrank K (Hom (T₁ K).toRep T.toRep)=Module.finrank K ↥((T.U 0 ⊓ T.U 1) ⊓ T.U 2) := by
  rw [show T₁ K=IntersectionProbes.signalTriple.task K from rfl,
    IntersectionProbes.Probe.hom_finrank]
  have he : IntersectionProbes.signalTriple.intersection T=(T.U 0 ⊓ T.U 1) ⊓ T.U 2 := by
    ext x
    change ((∀ i∈(Finset.univ : Finset (Fin 3)),x∈T.U i) ∧
      (∀ i∈(∅ : Finset (Fin 3)),x∈T.A i)) ↔ ((x∈T.U 0 ∧ x∈T.U 1) ∧ x∈T.U 2)
    simp [Fin.forall_fin_succ,and_assoc]
  rw [he]

/-- The dual relation space describing maps into the tripod. -/
def hom_T₀_to_kernel (T : TaskDecomposition.Task K F) (f : Hom T.toRep (T₀ K).toRep) :
    LinearMap.ker (tripleSum (T.U 0).dualAnnihilator (T.U 1).dualAnnihilator (T.U 2).dualAnnihilator) := by
  let a := (LinearMap.snd K K K).comp (f.map .center)
  let b := (LinearMap.fst K K K).comp (f.map .center)
  have hp := T.preservesOfHom (T₀ K) f
  have ha : a ∈ (T.U 0).dualAnnihilator := by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro x hx
    exact hp (0,true) x hx
  have hb : b ∈ (T.U 1).dualAnnihilator := by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro x hx
    exact hp (1,true) x hx
  have hc : -a-b ∈ (T.U 2).dualAnnihilator := by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro x hx
    have hh := hp (2,true) x hx
    change (f.map .center x).1+(f.map .center x).2=0 at hh
    change -(f.map .center x).2-(f.map .center x).1=0
    linear_combination -hh
  refine ⟨(⟨a,ha⟩,⟨b,hb⟩,⟨-a-b,hc⟩),?_⟩
  apply LinearMap.ext
  intro x
  change a x+(b x+(-a x-b x))=0
  ring

def kernel_to_hom_T₀ (T : TaskDecomposition.Task K F)
    (z : LinearMap.ker (tripleSum (T.U 0).dualAnnihilator (T.U 1).dualAnnihilator (T.U 2).dualAnnihilator)) :
    Hom T.toRep (T₀ K).toRep := by
  let f : F →ₗ[K] (K × K) := z.1.2.1.val.prod z.1.1.val
  have hp (i : Fin 3) (x : F) (hx : x ∈ T.U i) : f x ∈ sides K i := by
    fin_cases i
    · change z.1.1.val x=0
      exact (Submodule.mem_dualAnnihilator _).mp z.1.1.property x hx
    · change z.1.2.1.val x=0
      exact (Submodule.mem_dualAnnihilator _).mp z.1.2.1.property x hx
    · change z.1.2.1.val x+z.1.1.val x=0
      have hz := LinearMap.congr_fun z.property x
      change z.1.1.val x+(z.1.2.1.val x+z.1.2.2.val x)=0 at hz
      have hlast := (Submodule.mem_dualAnnihilator _).mp z.1.2.2.property x hx
      linear_combination hz-hlast
  exact T.homOfPreserves (T₀ K) f (by
    rintro ⟨i,b⟩ x hx
    cases b
    · exact hp i x (T.nested i hx)
    · exact hp i x hx)

def hom_T₀_equiv_kernel (T : TaskDecomposition.Task K F) :
    Hom T.toRep (T₀ K).toRep ≃ₗ[K]
      LinearMap.ker (tripleSum (T.U 0).dualAnnihilator (T.U 1).dualAnnihilator (T.U 2).dualAnnihilator) where
  toFun := hom_T₀_to_kernel T
  invFun := kernel_to_hom_T₀ T
  left_inv f := by
    apply T.hom_center_ext (T₀ K)
    apply LinearMap.ext
    intro x
    apply Prod.ext <;> rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext; apply LinearMap.ext; intro x; rfl
    · apply Prod.ext
      · apply Subtype.ext; apply LinearMap.ext; intro x; rfl
      · apply Subtype.ext
        apply LinearMap.ext
        intro x
        change -z.1.1.val x-z.1.2.1.val x=z.1.2.2.val x
        have hz := LinearMap.congr_fun z.property x
        change z.1.1.val x+(z.1.2.1.val x+z.1.2.2.val x)=0 at hz
        linear_combination -hz
  map_add' f g := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext; apply LinearMap.ext; intro x; rfl
    · apply Prod.ext
      · apply Subtype.ext; apply LinearMap.ext; intro x; rfl
      · apply Subtype.ext
        apply LinearMap.ext
        intro x
        change -((f.map .center x).2+(g.map .center x).2)-((f.map .center x).1+(g.map .center x).1)=
          (-(f.map .center x).2-(f.map .center x).1)+(-(g.map .center x).2-(g.map .center x).1)
        ring
  map_smul' c f := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext; apply LinearMap.ext; intro x; rfl
    · apply Prod.ext
      · apply Subtype.ext; apply LinearMap.ext; intro x; rfl
      · apply Subtype.ext
        apply LinearMap.ext
        intro x
        change -(c*(f.map .center x).2)-c*(f.map .center x).1=c*(-(f.map .center x).2-(f.map .center x).1)
        ring

/-- The fourth Hom dimension identity is a relation among annihilators. -/
theorem hom_T₀_finrank [FiniteDimensional K F] (T : TaskDecomposition.Task K F) :
    Module.finrank K (Hom T.toRep (T₀ K).toRep)+Module.finrank K (T.U 0)+
      Module.finrank K (T.U 1)+Module.finrank K (T.U 2)=
        2*Module.finrank K F+Module.finrank K ↥((T.U 0 ⊓ T.U 1) ⊓ T.U 2) := by
  letI : Module.Free K ↥((T.U 0).dualAnnihilator) := Module.Free.of_divisionRing K ↥((T.U 0).dualAnnihilator)
  letI : Module.Free K ↥((T.U 1).dualAnnihilator) := Module.Free.of_divisionRing K ↥((T.U 1).dualAnnihilator)
  letI : Module.Free K ↥((T.U 2).dualAnnihilator) := Module.Free.of_divisionRing K ↥((T.U 2).dualAnnihilator)
  letI : Module.Free K (↥((T.U 1).dualAnnihilator) × ↥((T.U 2).dualAnnihilator)) :=
    Module.Free.of_divisionRing K (↥((T.U 1).dualAnnihilator) × ↥((T.U 2).dualAnnihilator))
  letI : FiniteDimensional K (↥((T.U 1).dualAnnihilator) × ↥((T.U 2).dualAnnihilator)) := inferInstance
  have he := LinearMap.finrank_range_add_finrank_ker (K:=K)
    (V:= ↥((T.U 0).dualAnnihilator) × ↥((T.U 1).dualAnnihilator) × ↥((T.U 2).dualAnnihilator))
    (V₂:=Module.Dual K F)
    (tripleSum (K:=K) (F:=Module.Dual K F) ((T.U 0).dualAnnihilator) ((T.U 1).dualAnnihilator) ((T.U 2).dualAnnihilator))
  rw [tripleSum_range,Module.finrank_prod,Module.finrank_prod,←(hom_T₀_equiv_kernel T).finrank_eq] at he
  have hsum : ((T.U 0).dualAnnihilator ⊔ (T.U 1).dualAnnihilator) ⊔ (T.U 2).dualAnnihilator=
      ((T.U 0 ⊓ T.U 1) ⊓ T.U 2).dualAnnihilator := by
    rw [Subspace.dualAnnihilator_inf_eq,Subspace.dualAnnihilator_inf_eq]
  rw [hsum] at he
  have h₀ := Subspace.finrank_add_finrank_dualAnnihilator_eq (T.U 0)
  have h₁ := Subspace.finrank_add_finrank_dualAnnihilator_eq (T.U 1)
  have h₂ := Subspace.finrank_add_finrank_dualAnnihilator_eq (T.U 2)
  have hI := Subspace.finrank_add_finrank_dualAnnihilator_eq ((T.U 0 ⊓ T.U 1) ⊓ T.U 2)
  omega

theorem euler_T₀_left (T : TaskDecomposition.Task K F) :
    eulerForm inwardE6 (dimension (T₀ K).toRep) (dimension T.toRep)=
      (Module.finrank K (T.A 0):ℤ)+Module.finrank K (T.A 1)+Module.finrank K (T.A 2)-Module.finrank K F := by
  simp [eulerForm,E6Reflection.sum_vertices,E6Reflection.sum_edges,inwardE6,dimension,
    TaskDecomposition.Task.toRep,T₀,sides_finrank,Plane]
  ring

theorem euler_T₀_right (T : TaskDecomposition.Task K F) :
    eulerForm inwardE6 (dimension T.toRep) (dimension (T₀ K).toRep)=
      2*(Module.finrank K F:ℤ)-Module.finrank K (T.U 0)-Module.finrank K (T.U 1)-Module.finrank K (T.U 2) := by
  simp [eulerForm,E6Reflection.sum_vertices,E6Reflection.sum_edges,inwardE6,dimension,
    TaskDecomposition.Task.toRep,T₀,sides_finrank,Plane]
  ring

theorem euler_T₁_left (T : TaskDecomposition.Task K F) :
    eulerForm inwardE6 (dimension (T₁ K).toRep) (dimension T.toRep)=
      (Module.finrank K (T.U 0):ℤ)+Module.finrank K (T.U 1)+Module.finrank K (T.U 2)-2*Module.finrank K F := by
  simp [eulerForm,E6Reflection.sum_vertices,E6Reflection.sum_edges,inwardE6,dimension,
    TaskDecomposition.Task.toRep,T₁,IntersectionProbes.Probe.task,IntersectionProbes.signalTriple]
  ring

theorem euler_T₁_right (T : TaskDecomposition.Task K F) :
    eulerForm inwardE6 (dimension T.toRep) (dimension (T₁ K).toRep)=
      (Module.finrank K F:ℤ)-Module.finrank K (T.A 0)-Module.finrank K (T.A 1)-Module.finrank K (T.A 2) := by
  simp [eulerForm,E6Reflection.sum_vertices,E6Reflection.sum_edges,inwardE6,dimension,
    TaskDecomposition.Task.toRep,T₁,IntersectionProbes.Probe.task,IntersectionProbes.signalTriple]
  ring

/-- Special Hom–Euler identities for the two-object regular orbit. These
come from explicit kernels and annihilators, not an assumed Ext-duality theorem. -/
theorem hom_euler_T₀_left [FiniteDimensional K F] (T : TaskDecomposition.Task K F) :
    eulerForm inwardE6 (dimension (T₀ K).toRep) (dimension T.toRep)=
      (Module.finrank K (Hom (T₀ K).toRep T.toRep):ℤ)-Module.finrank K (Hom T.toRep (T₁ K).toRep) := by
  rw [euler_T₀_left]
  have h₀ := T₀_hom_finrank T
  have h₁ := hom_T₁_finrank T
  dsimp only [sideSpan] at h₁
  omega

theorem hom_euler_T₁_right [FiniteDimensional K F] (T : TaskDecomposition.Task K F) :
    eulerForm inwardE6 (dimension T.toRep) (dimension (T₁ K).toRep)=
      (Module.finrank K (Hom T.toRep (T₁ K).toRep):ℤ)-Module.finrank K (Hom (T₀ K).toRep T.toRep) := by
  rw [euler_T₁_right]
  have h₀ := T₀_hom_finrank T
  have h₁ := hom_T₁_finrank T
  dsimp only [sideSpan] at h₁
  omega

theorem hom_euler_T₁_left [FiniteDimensional K F] (T : TaskDecomposition.Task K F) :
    eulerForm inwardE6 (dimension (T₁ K).toRep) (dimension T.toRep)=
      (Module.finrank K (Hom (T₁ K).toRep T.toRep):ℤ)-Module.finrank K (Hom T.toRep (T₀ K).toRep) := by
  rw [euler_T₁_left,T₁_hom_finrank]
  have h₀ := hom_T₀_finrank T
  omega

theorem hom_euler_T₀_right [FiniteDimensional K F] (T : TaskDecomposition.Task K F) :
    eulerForm inwardE6 (dimension T.toRep) (dimension (T₀ K).toRep)=
      (Module.finrank K (Hom T.toRep (T₀ K).toRep):ℤ)-Module.finrank K (Hom (T₁ K).toRep T.toRep) := by
  rw [euler_T₀_right,T₁_hom_finrank]
  have h₀ := hom_T₀_finrank T
  omega

/-- Distinct regular-simple tasks have zero actual Hom dimension. -/
theorem regularSimple_hom_finrank_zero {V W : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (S : TaskDecomposition.Task K V) (T : TaskDecomposition.Task K W)
    (hS : S.IsRegularSimple) (hT : T.IsRegularSimple)
    (hni : ¬ConfigurationIso S.spaces T.spaces) :
    Module.finrank K (Hom S.toRep T.toRep)=0 := by
  have hz (f : Hom S.toRep T.toRep) : f=0 := by
    change f=Hom.zero S.toRep T.toRep
    apply S.hom_center_ext T
    exact hS.hom_zero_of_not_iso hT hni (f.map .center) (S.preservesOfHom T f)
  haveI : Subsingleton (Hom S.toRep T.toRep) := ⟨fun f g => (hz f).trans (hz g).symm⟩
  exact Module.finrank_zero_of_subsingleton

theorem T₀_not_iso_T₁ : ¬ConfigurationIso (T₀ K).spaces (T₁ K).spaces := by
  rintro ⟨e,_,_⟩
  have he := e.finrank_eq
  norm_num at he

/-- Every regular-simple class outside the concrete pair has zero Hom and
zero directed Euler pairing with both members, in both directions. -/
theorem regular_simple_outside_pair_orthogonal [FiniteDimensional K F]
    (T : TaskDecomposition.Task K F) (hT : T.IsRegularSimple)
    (h₀ : ¬ConfigurationIso T.spaces (T₀ K).spaces)
    (h₁ : ¬ConfigurationIso T.spaces (T₁ K).spaces) :
    (Module.finrank K (Hom (T₀ K).toRep T.toRep)=0 ∧
      Module.finrank K (Hom T.toRep (T₀ K).toRep)=0 ∧
      eulerForm inwardE6 (dimension (T₀ K).toRep) (dimension T.toRep)=0 ∧
      eulerForm inwardE6 (dimension T.toRep) (dimension (T₀ K).toRep)=0) ∧
    (Module.finrank K (Hom (T₁ K).toRep T.toRep)=0 ∧
      Module.finrank K (Hom T.toRep (T₁ K).toRep)=0 ∧
      eulerForm inwardE6 (dimension (T₁ K).toRep) (dimension T.toRep)=0 ∧
      eulerForm inwardE6 (dimension T.toRep) (dimension (T₁ K).toRep)=0) := by
  have h₀' : ¬ConfigurationIso (T₀ K).spaces T.spaces := by
    rintro ⟨e,he,he'⟩; exact h₀ ⟨e.symm,he',he⟩
  have h₁' : ¬ConfigurationIso (T₁ K).spaces T.spaces := by
    rintro ⟨e,he,he'⟩; exact h₁ ⟨e.symm,he',he⟩
  have ha := regularSimple_hom_finrank_zero (T₀ K) T (T₀_regularSimple K) hT h₀'
  have hb := regularSimple_hom_finrank_zero T (T₀ K) hT (T₀_regularSimple K) h₀
  have hc := regularSimple_hom_finrank_zero (T₁ K) T (T₁_regularSimple K) hT h₁'
  have hd := regularSimple_hom_finrank_zero T (T₁ K) hT (T₁_regularSimple K) h₁
  refine ⟨⟨ha,hb,?_,?_⟩,⟨hc,hd,?_,?_⟩⟩
  · rw [hom_euler_T₀_left,ha,hd]; rfl
  · rw [hom_euler_T₀_right,hb,hc]; rfl
  · rw [hom_euler_T₁_left,hc,hb]; rfl
  · rw [hom_euler_T₁_right,hd,ha]; rfl

theorem T₀_cross_disjoint (i j : Fin 3) (hne : i≠j) :
    Disjoint ((T₀ K).A i) ((T₀ K).U j) := by
  have h := regular_sides_disjoint (T₀ K) (T₀_indec K) (T₀_defect K)
  fin_cases i <;> fin_cases j
  all_goals first
    | exact False.elim (hne rfl)
    | exact h.1
    | exact h.1.symm
    | exact h.2.1
    | exact h.2.1.symm
    | exact h.2.2
    | exact h.2.2.symm

theorem T₁_cross_disjoint (i j : Fin 3) : Disjoint ((T₁ K).A i) ((T₁ K).U j) := by
  simp [T₁,IntersectionProbes.Probe.task,IntersectionProbes.signalTriple]

/-- The six cross-intersection probes vanish on both members of the regular pair. -/
theorem cross_probe_pair_hom_zero (i j : Fin 3) (hne : i≠j) :
    Module.finrank K (Hom ((IntersectionProbes.sideSignal i j).task K).toRep (T₀ K).toRep)=0 ∧
    Module.finrank K (Hom ((IntersectionProbes.sideSignal i j).task K).toRep (T₁ K).toRep)=0 := by
  constructor
  · rw [IntersectionProbes.Probe.hom_finrank,IntersectionProbes.sideSignal_intersection,
      (T₀_cross_disjoint i j hne).eq_bot]
    exact finrank_bot K _
  · rw [IntersectionProbes.Probe.hom_finrank,IntersectionProbes.sideSignal_intersection,
      (T₁_cross_disjoint i j).eq_bot]
    exact finrank_bot K _

/-- Positive side excess detects the T0 block by an actual nonzero Hom space. -/
theorem positive_excess_T₀_hom_pos [FiniteDimensional K F] (T : TaskDecomposition.Task K F)
    (hx : Module.finrank K F < Module.finrank K (T.A 0)+Module.finrank K (T.A 1)+Module.finrank K (T.A 2)) :
    0 < Module.finrank K (Hom (T₀ K).toRep T.toRep) := by
  have he := T₀_hom_finrank T
  have hs : Module.finrank K ↥((T.A 0 ⊔ T.A 1) ⊔ T.A 2) ≤ Module.finrank K F := by
    have hh := Submodule.finrank_mono (show (T.A 0 ⊔ T.A 1) ⊔ T.A 2 ≤ ⊤ from le_top)
    simpa using hh
  omega

end UploadBroadcast.RegularTripodPair
