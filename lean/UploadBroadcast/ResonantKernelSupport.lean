import UploadBroadcast.ResonantRelationReduction
import UploadBroadcast.RegularSubobjectDefect

/-! Kernel modes of the signed relation boundary and their sparse subobjects. -/
namespace UploadBroadcast.ResonantKernelSupport
open TaskDecomposition ResonantRelationReduction
variable {K : Type*} [Field K]

abbrev Sparse (P Q R : Type*) := P × Q × R × K × K

section Coordinates
variable (P Q R : Type*) [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q] [AddCommGroup R] [Module K R]

def side₁ : Submodule K (Sparse (K:=K) P Q R) where
  carrier := {p | p.2.1=0 ∧ p.2.2.1=0 ∧ p.2.2.2.2=0}
  zero_mem' := by simp
  add_mem' := by intro p q hp hq; simp_all
  smul_mem' := by intro a p hp; simp_all

def side₂ : Submodule K (Sparse (K:=K) P Q R) where
  carrier := {p | p.1=0 ∧ p.2.2.1=0 ∧ p.2.2.2.1=0}
  zero_mem' := by simp
  add_mem' := by intro p q hp hq; simp_all
  smul_mem' := by intro a p hp; simp_all

def side₃ : Submodule K (Sparse (K:=K) P Q R) where
  carrier := {p | p.1=0 ∧ p.2.1=0 ∧ p.2.2.2.1+p.2.2.2.2=0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    refine ⟨by simp_all,by simp_all,?_⟩
    change (p.2.2.2.1+q.2.2.2.1)+(p.2.2.2.2+q.2.2.2.2)=0
    linear_combination hp.2.2+hq.2.2
  smul_mem' := by
    intro a p hp
    refine ⟨by simp_all,by simp_all,?_⟩
    change a*p.2.2.2.1+a*p.2.2.2.2=0
    rw [←mul_add,hp.2.2,mul_zero]

def side₁Equiv : side₁ (K:=K) P Q R ≃ₗ[K] (P × K) where
  toFun p := (p.1.1,p.1.2.2.2.1)
  invFun p := ⟨(p.1,0,0,p.2,0),by simp [side₁]⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl (Prod.ext p.property.1.symm (Prod.ext p.property.2.1.symm (Prod.ext rfl p.property.2.2.symm)))
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def side₂Equiv : side₂ (K:=K) P Q R ≃ₗ[K] (Q × K) where
  toFun p := (p.1.2.1,p.1.2.2.2.2)
  invFun p := ⟨(0,p.1,0,0,p.2),by simp [side₂]⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext p.property.1.symm (Prod.ext rfl (Prod.ext p.property.2.1.symm (Prod.ext p.property.2.2.symm rfl)))
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def side₃Equiv : side₃ (K:=K) P Q R ≃ₗ[K] (R × K) where
  toFun p := (p.1.2.2.1,p.1.2.2.2.2)
  invFun p := ⟨(0,0,p.1,-p.2,p.2),by simp [side₃]⟩
  left_inv p := by
    apply Subtype.ext
    refine Prod.ext p.property.1.symm (Prod.ext p.property.2.1.symm (Prod.ext rfl (Prod.ext ?_ rfl)))
    linear_combination -p.property.2.2
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem side₁_finrank [FiniteDimensional K P] [FiniteDimensional K Q] [FiniteDimensional K R] :
    Module.finrank K (side₁ (K:=K) P Q R)=Module.finrank K P+1 := by
  rw [(side₁Equiv P Q R).finrank_eq]; simp

theorem side₂_finrank [FiniteDimensional K P] [FiniteDimensional K Q] [FiniteDimensional K R] :
    Module.finrank K (side₂ (K:=K) P Q R)=Module.finrank K Q+1 := by
  rw [(side₂Equiv P Q R).finrank_eq]; simp

theorem side₃_finrank [FiniteDimensional K P] [FiniteDimensional K Q] [FiniteDimensional K R] :
    Module.finrank K (side₃ (K:=K) P Q R)=Module.finrank K R+1 := by
  rw [(side₃Equiv P Q R).finrank_eq]; simp
end Coordinates

variable {X Y : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

def relationTask (d : Data K X Y) : TaskDecomposition.Task K (ResonantEndomorphisms.Ambient K X) where
  A := ![ResonantEndomorphisms.side₁ K X,ResonantEndomorphisms.side₂ K X,ResonantEndomorphisms.side₃ K X]
  U := ![ResonantEndomorphisms.side₁ K X ⊔ LinearMap.range (demand₁ d),
    ResonantEndomorphisms.side₂ K X ⊔ LinearMap.range (demand₂ d),
    ResonantEndomorphisms.side₃ K X ⊔ LinearMap.range (demand₃ d)]
  nested i := by fin_cases i <;> exact le_sup_left

theorem relationTask_indec (d : Data K X Y) (hi : Indecomposable (relationSpaces d) ⊤) :
    Indecomposable (relationTask d).spaces ⊤ := by
  refine ⟨hi.1,?_⟩
  intro P Q hs
  apply hi.2 P Q
  refine ⟨hs.disjoint,hs.sup_eq,?_⟩
  intro i
  fin_cases i
  · exact hs.compatible (0,false)
  · exact hs.compatible (1,false)
  · exact hs.compatible (2,false)
  · exact hs.compatible (0,true)
  · exact hs.compatible (1,true)
  · exact hs.compatible (2,true)

def inclusion (P Q R : Submodule K X) :
    Sparse (K:=K) P Q R →ₗ[K] ResonantEndomorphisms.Ambient K X where
  toFun p := (p.1.1,p.2.1.1,p.2.2.1.1,p.2.2.2.1,p.2.2.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem inclusion_injective (P Q R : Submodule K X) : Function.Injective (inclusion P Q R) := by
  intro a b he
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg (fun p : ResonantEndomorphisms.Ambient K X => p.2.1) he
  have h₃ := congrArg (fun p : ResonantEndomorphisms.Ambient K X => p.2.2.1) he
  have h₄ := congrArg (fun p : ResonantEndomorphisms.Ambient K X => p.2.2.2.1) he
  have h₅ := congrArg (fun p : ResonantEndomorphisms.Ambient K X => p.2.2.2.2) he
  exact Prod.ext (Subtype.ext h₁) (Prod.ext (Subtype.ext h₂) (Prod.ext (Subtype.ext h₃) (Prod.ext h₄ h₅)))

def sparseTask (d : Data K X Y) (P Q R : Submodule K X) : TaskDecomposition.Task K (Sparse (K:=K) P Q R) where
  A := ![side₁ P Q R,side₂ P Q R,side₃ P Q R]
  U i := ((relationTask d).U i).comap (inclusion P Q R)
  nested i := by
    intro p hp
    change inclusion P Q R p ∈ (relationTask d).U i
    apply (relationTask d).nested i
    fin_cases i
    · change p.2.1=0 ∧ p.2.2.1=0 ∧ p.2.2.2.2=0 at hp
      change (p.2.1 : X)=0 ∧ (p.2.2.1 : X)=0 ∧ p.2.2.2.2=0
      simp [hp.1,hp.2.1,hp.2.2]
    · change p.1=0 ∧ p.2.2.1=0 ∧ p.2.2.2.1=0 at hp
      change (p.1 : X)=0 ∧ (p.2.2.1 : X)=0 ∧ p.2.2.2.1=0
      simp [hp.1,hp.2.1,hp.2.2]
    · change p.1=0 ∧ p.2.1=0 ∧ p.2.2.2.1+p.2.2.2.2=0 at hp
      change (p.1 : X)=0 ∧ (p.2.1 : X)=0 ∧ p.2.2.2.1+p.2.2.2.2=0
      simp [hp.1,hp.2.1,hp.2.2]

theorem inclusion_preserves (d : Data K X Y) (P Q R : Submodule K X) :
    Preserves (sparseTask d P Q R).spaces (relationTask d).spaces (inclusion P Q R) := by
  rintro ⟨i,b⟩ p hp
  cases b
  · fin_cases i
    · change p.2.1=0 ∧ p.2.2.1=0 ∧ p.2.2.2.2=0 at hp
      change (p.2.1 : X)=0 ∧ (p.2.2.1 : X)=0 ∧ p.2.2.2.2=0
      simp [hp.1,hp.2.1,hp.2.2]
    · change p.1=0 ∧ p.2.2.1=0 ∧ p.2.2.2.1=0 at hp
      change (p.1 : X)=0 ∧ (p.2.2.1 : X)=0 ∧ p.2.2.2.1=0
      simp [hp.1,hp.2.1,hp.2.2]
    · change p.1=0 ∧ p.2.1=0 ∧ p.2.2.2.1+p.2.2.2.2=0 at hp
      change (p.1 : X)=0 ∧ (p.2.1 : X)=0 ∧ p.2.2.2.1+p.2.2.2.2=0
      simp [hp.1,hp.2.1,hp.2.2]
  · exact hp

private theorem finrank_increment {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A U : Submodule K V) (ha : A ≤ U)
    (p : V) (hp : p ∈ U) (hn : p ∉ A) :
    Module.finrank K A+1 ≤ Module.finrank K U := by
  have hlt : A < U := lt_of_le_not_le ha (by intro h; exact hn (h hp))
  have he := Submodule.finrank_lt_finrank_of_lt hlt
  omega

private theorem span_finrank [DecidableEq X] (x : X) : Module.finrank K (Submodule.span K {x}) = if x=0 then 0 else 1 := by
  classical
  by_cases hx : x=0
  · simp [hx]
  · simp [hx,finrank_span_singleton hx]

private def rankOne [DecidableEq X] (x : X) : ℕ := if x=0 then 0 else 1

omit [Module K X] in
private theorem support_arithmetic [DecidableEq X] [DecidableEq K]
    (a b c : X) (k₁ k₂ k₃ : K) (u₁ u₂ u₃ : ℕ) (hk : k₁+k₂+k₃≠0)
    (hn : -3*((rankOne a+rankOne b+rankOne c+2:ℕ):ℤ)+u₁+u₂+u₃+
      (rankOne a+1:ℕ)+(rankOne b+1:ℕ)+(rankOne c+1:ℕ) ≤ 0)
    (h₁ : rankOne a+1+(if b=0 ∧ c=0 ∧ k₁=0 then 0 else 1) ≤ u₁)
    (h₂ : rankOne b+1+(if a=0 ∧ c=0 ∧ k₂=0 then 0 else 1) ≤ u₂)
    (h₃ : rankOne c+1+(if a=0 ∧ b=0 ∧ k₃=0 then 0 else 1) ≤ u₃) :
    a≠0 ∧ b≠0 ∧ c≠0 := by
  by_cases ha : a=0 <;> by_cases hb : b=0 <;> by_cases hc : c=0
  all_goals simp only [rankOne,ha,hb,hc,if_true,if_false] at hn h₁ h₂ h₃
  all_goals first
    | exact ⟨ha,hb,hc⟩
    | (exfalso; split_ifs at hn h₁ h₂ h₃ <;> simp_all <;> omega)

/-- A detected boundary mode must meet every private vertex. Missing support
would create an actual positive-defect sparse subtask, which cannot inject into
a regular indecomposable. No pencil or tube classification is assumed. -/
theorem detected_mode_full_support {K X Y : Type} [Field K]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Y] [Module K Y]
    (d : Data K X Y) (hi : Indecomposable (relationSpaces d) ⊤)
    (hregular : ReflectionReduction.defect (relationTask d).dimensionVector=0)
    (y : Y × Y × Y) (hy : boundary d y=0) (hk : coupling d y≠0) :
    d.B₂ y.2.1≠0 ∧ d.B₁ y.1≠0 ∧ d.C₁ y.1≠0 := by
  classical
  let a := d.B₂ y.2.1
  let b := d.B₁ y.1
  let c := d.C₁ y.1
  let P := Submodule.span K {a}
  let Q := Submodule.span K {b}
  let R := Submodule.span K {c}
  let S := sparseTask d P Q R
  have haP : a ∈ P := Submodule.mem_span_singleton_self a
  have hbQ : b ∈ Q := Submodule.mem_span_singleton_self b
  have hcR : c ∈ R := Submodule.mem_span_singleton_self c
  have h₁ : d.B₃ y.2.2= -a := by
    have he := congrArg Prod.fst hy
    change a+d.B₃ y.2.2=0 at he
    exact eq_neg_of_add_eq_zero_right he
  have h₂ : d.C₃ y.2.2= -b := by
    have he := congrArg (fun p : X × X × X => p.2.1) hy
    change b+d.C₃ y.2.2=0 at he
    exact eq_neg_of_add_eq_zero_right he
  have h₃ : d.C₂ y.2.1=c := by
    have he := congrArg (fun p : X × X × X => p.2.2) hy
    change c-d.C₂ y.2.1=0 at he
    exact (sub_eq_zero.mp he).symm
  let w₁ : Sparse (K:=K) P Q R := (0,⟨b,hbQ⟩,⟨c,hcR⟩,0,d.k₁ y.1)
  let w₂ : Sparse (K:=K) P Q R := (⟨a,haP⟩,0,⟨c,hcR⟩,d.k₂ y.2.1,0)
  let w₃ : Sparse (K:=K) P Q R := (⟨-a,P.neg_mem haP⟩,⟨-b,Q.neg_mem hbQ⟩,0,d.k₃ y.2.2,0)
  have hw₁ : w₁ ∈ S.U 0 := by
    apply Submodule.mem_sup_right
    exact ⟨y.1,rfl⟩
  have hw₂ : w₂ ∈ S.U 1 := by
    apply Submodule.mem_sup_right
    refine ⟨y.2.1,?_⟩
    change (a,0,d.C₂ y.2.1,d.k₂ y.2.1,0)=(a,0,c,d.k₂ y.2.1,0)
    rw [h₃]
  have hw₃ : w₃ ∈ S.U 2 := by
    apply Submodule.mem_sup_right
    refine ⟨y.2.2,?_⟩
    change (d.B₃ y.2.2,d.C₃ y.2.2,0,d.k₃ y.2.2,0)=(-a,-b,0,d.k₃ y.2.2,0)
    rw [h₁,h₂]
  have hmem₁ : w₁ ∈ S.A 0 ↔ b=0 ∧ c=0 ∧ d.k₁ y.1=0 := by
    change ((⟨b,hbQ⟩ : Q)=0 ∧ (⟨c,hcR⟩ : R)=0 ∧ d.k₁ y.1=0) ↔ _
    simp only [Submodule.mk_eq_zero]
  have hmem₂ : w₂ ∈ S.A 1 ↔ a=0 ∧ c=0 ∧ d.k₂ y.2.1=0 := by
    change ((⟨a,haP⟩ : P)=0 ∧ (⟨c,hcR⟩ : R)=0 ∧ d.k₂ y.2.1=0) ↔ _
    simp only [Submodule.mk_eq_zero]
  have hmem₃ : w₃ ∈ S.A 2 ↔ a=0 ∧ b=0 ∧ d.k₃ y.2.2=0 := by
    change ((⟨-a,P.neg_mem haP⟩ : P)=0 ∧ (⟨-b,Q.neg_mem hbQ⟩ : Q)=0 ∧ d.k₃ y.2.2+0=0) ↔ _
    simp only [Submodule.mk_eq_zero,neg_eq_zero,add_zero]
  have inc (j : Fin 3) (w : Sparse (K:=K) P Q R) (hw : w ∈ S.U j) :
      Module.finrank K (S.A j)+(if w ∈ S.A j then 0 else 1) ≤ Module.finrank K (S.U j) := by
    split_ifs with h
    · simpa using Submodule.finrank_mono (S.nested j)
    · exact finrank_increment _ _ (S.nested j) w hw h
  have hu₁ := inc 0 w₁ hw₁
  have hu₂ := inc 1 w₂ hw₂
  have hu₃ := inc 2 w₃ hw₃
  have hn := S.defect_nonpos_of_injective_preserves (relationTask d) (relationTask_indec d hi)
    hregular (inclusion P Q R) (inclusion_preserves d P Q R) (inclusion_injective P Q R)
  have hA₁ : Module.finrank K (S.A 0)=Module.finrank K P+1 := side₁_finrank P Q R
  have hA₂ : Module.finrank K (S.A 1)=Module.finrank K Q+1 := side₂_finrank P Q R
  have hA₃ : Module.finrank K (S.A 2)=Module.finrank K R+1 := side₃_finrank P Q R
  have hF : Module.finrank K (Sparse (K:=K) P Q R)=Module.finrank K P+Module.finrank K Q+Module.finrank K R+2 := by
    simp [Sparse,Module.finrank_prod]; omega
  have hP := span_finrank (K:=K) a
  have hQ := span_finrank (K:=K) b
  have hR := span_finrank (K:=K) c
  change Module.finrank K P=_ at hP
  change Module.finrank K Q=_ at hQ
  change Module.finrank K R=_ at hR
  change -3*(Module.finrank K (Sparse (K:=K) P Q R):ℤ)+
    Module.finrank K (S.U 0)+Module.finrank K (S.U 1)+Module.finrank K (S.U 2)+
    Module.finrank K (S.A 0)+Module.finrank K (S.A 1)+Module.finrank K (S.A 2) ≤ 0 at hn
  rw [hF,hA₁,hA₂,hA₃,hP,hQ,hR] at hn
  rw [hA₁,hP,hmem₁] at hu₁
  rw [hA₂,hQ,hmem₂] at hu₂
  rw [hA₃,hR,hmem₃] at hu₃
  exact support_arithmetic a b c (d.k₁ y.1) (d.k₂ y.2.1) (d.k₃ y.2.2)
    (Module.finrank K (S.U 0)) (Module.finrank K (S.U 1)) (Module.finrank K (S.U 2))
    hk hn
      (by by_cases h : b=0 ∧ c=0 ∧ d.k₁ y.1=0 <;> simpa [rankOne,h] using hu₁)
      (by by_cases h : a=0 ∧ c=0 ∧ d.k₂ y.2.1=0 <;> simpa [rankOne,h] using hu₂)
      (by by_cases h : a=0 ∧ b=0 ∧ d.k₃ y.2.2=0 <;> simpa [rankOne,h] using hu₃)

end UploadBroadcast.ResonantKernelSupport
