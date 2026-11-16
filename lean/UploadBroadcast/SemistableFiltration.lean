import UploadBroadcast.RegularSubobjectDefect
import UploadBroadcast.TripodQuotient

/-!
# Semistable actual three-flag tasks

Semistability is stated using actual ambient subspaces and their six induced
intersections. Zero-defect subobjects and quotients remain semistable. Minimal
positive-dimensional zero-defect subspaces supply regular-simple factors;
no root or tube classification is assumed.
-/
namespace UploadBroadcast.TaskDecomposition
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

/-- A zero-defect task with no positive-defect actual induced subtask. -/
def Task.IsSemistable (T : Task K V) : Prop :=
  ReflectionReduction.defect T.dimensionVector=0 ∧ ∀ P, T.componentDefect P ≤ 0

/-- A nonzero semistable task with no proper nonzero zero-defect subobject. -/
def Task.IsRegularSimple (T : Task K V) : Prop :=
  T.IsSemistable ∧ (⊤ : Submodule K V)≠⊥ ∧
    ∀ P, T.componentDefect P=0 → P=⊥ ∨ P=⊤

/-- The already proved positive-to-regular Hom vanishing gives semistability
of every actual zero-defect indecomposable. -/
theorem Task.isSemistable_of_indec [FiniteDimensional K V] (T : Task K V)
    (hi : Indecomposable T.spaces ⊤)
    (hz : ReflectionReduction.defect T.dimensionVector=0) : T.IsSemistable := by
  refine ⟨hz,fun P => ?_⟩
  have h := (T.onComponent P).defect_nonpos_of_injective_preserves T hi hz
    P.subtype (by intro i x hx; rw [T.onComponent_spaces] at hx; exact hx)
    Subtype.val_injective
  change ReflectionReduction.defect (T.onComponent P).dimensionVector ≤ 0 at h
  rw [T.onComponent_dimensionVector] at h
  exact h

/-- The quotient keeps the images of all six actual designated spaces. -/
def Task.quotientBy (T : Task K V) (P : Submodule K V) : Task K (V ⧸ P) where
  A i := (T.A i).map P.mkQ
  U i := (T.U i).map P.mkQ
  nested i := Submodule.map_mono (T.nested i)

/-- The quotient map is an actual morphism of all six designated subspaces. -/
theorem Task.quotientBy_preserves (T : Task K V) (P : Submodule K V) :
    Preserves T.spaces (T.quotientBy P).spaces P.mkQ := by
  rintro ⟨i,b⟩ x hx
  cases b <;> exact ⟨x,hx,rfl⟩

/-- Intersecting an image with a quotient subspace is the image of the
corresponding intersection with its full preimage. -/
theorem quotient_intersection_image (A P : Submodule K V) (Q : Submodule K (V ⧸ P)) :
    (A ⊓ Q.comap P.mkQ).map P.mkQ = A.map P.mkQ ⊓ Q := by
  ext q
  constructor
  · rintro ⟨a,⟨ha,hq⟩,rfl⟩
    exact ⟨⟨a,ha,rfl⟩,hq⟩
  · rintro ⟨⟨a,ha,rfl⟩,hq⟩
    exact ⟨a,⟨ha,hq⟩,rfl⟩

/-- The kernel lies in every full preimage of a quotient subspace. -/
theorem le_quotient_comap (P : Submodule K V) (Q : Submodule K (V ⧸ P)) :
    P ≤ Q.comap P.mkQ := by
  intro x hx
  change P.mkQ x ∈ Q
  have he : P.mkQ x=0 := (Submodule.Quotient.mk_eq_zero P).mpr hx
  rw [he]
  exact Q.zero_mem

/-- Exact rank additivity for each designated-space intersection in a quotient. -/
theorem quotient_intersection_finrank [FiniteDimensional K V]
    (A P : Submodule K V) (Q : Submodule K (V ⧸ P)) :
    Module.finrank K ↥(A.map P.mkQ ⊓ Q)+Module.finrank K ↥(A ⊓ P)=
      Module.finrank K ↥(A ⊓ Q.comap P.mkQ) := by
  have h := TripodQuotient.quotient_image_finrank (A ⊓ Q.comap P.mkQ) P
  rw [quotient_intersection_image,inf_assoc,inf_eq_right.mpr (le_quotient_comap P Q)] at h
  exact h

/-- Exact rank additivity for an arbitrary quotient subspace and its preimage. -/
theorem quotient_comap_finrank [FiniteDimensional K V]
    (P : Submodule K V) (Q : Submodule K (V ⧸ P)) :
    Module.finrank K Q+Module.finrank K P=Module.finrank K (Q.comap P.mkQ) := by
  have h := quotient_intersection_finrank (⊤ : Submodule K V) P Q
  rw [Submodule.map_top,LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective P),
    top_inf_eq,top_inf_eq,top_inf_eq] at h
  exact h

/-- Defect is additive along every induced subobject/quotient sequence,
including after restricting the quotient to any of its ambient subspaces. -/
theorem Task.quotientBy_componentDefect_add [FiniteDimensional K V]
    (T : Task K V) (P : Submodule K V) (Q : Submodule K (V ⧸ P)) :
    (T.quotientBy P).componentDefect Q+T.componentDefect P=
      T.componentDefect (Q.comap P.mkQ) := by
  have hf := quotient_comap_finrank P Q
  have hu := fun i => quotient_intersection_finrank (T.U i) P Q
  have ha := fun i => quotient_intersection_finrank (T.A i) P Q
  unfold Task.componentDefect Task.componentDimension ReflectionReduction.defect
  simp only [Task.quotientBy]
  have hf' := congrArg (fun n : ℕ => (n : ℤ)) hf
  have hu' := fun i => congrArg (fun n : ℕ => (n : ℤ)) (hu i)
  have ha' := fun i => congrArg (fun n : ℕ => (n : ℤ)) (ha i)
  simp only [Nat.cast_add] at hf' hu' ha'
  linear_combination -3*hf'+hu' 0+hu' 1+hu' 2+ha' 0+ha' 1+ha' 2

/-- Quotienting a semistable task by a zero-defect actual subobject preserves
semistability. This also proves quotient arrow injectivity at the task level. -/
theorem Task.IsSemistable.quotientBy [FiniteDimensional K V]
    {T : Task K V} (hT : T.IsSemistable) (P : Submodule K V)
    (hP : T.componentDefect P=0) : (T.quotientBy P).IsSemistable := by
  constructor
  · have he := T.quotientBy_componentDefect_add P ⊤
    rw [hP,add_zero,Submodule.comap_top,Task.componentDefect_top,
      Task.componentDefect_top,hT.1] at he
    exact he
  · intro Q
    have he := T.quotientBy_componentDefect_add P Q
    rw [hP,add_zero] at he
    rw [he]
    exact hT.2 _


/-- Restriction to a subspace commutes with taking further induced subspaces,
including the exact signed defect. -/
theorem Task.onComponent_componentDefect (T : Task K V) (P : Submodule K V)
    (Q : Submodule K P) :
    (T.onComponent P).componentDefect Q=T.componentDefect (Q.map P.subtype) := by
  have h (A : Submodule K V) :
      Module.finrank K ↥(A.comap P.subtype ⊓ Q)=
        Module.finrank K ↥(A ⊓ Q.map P.subtype) := by
    rw [←map_restricted_inf,Submodule.finrank_map_subtype_eq]
  unfold Task.componentDefect Task.componentDimension ReflectionReduction.defect
  simp only [Task.onComponent,h,Submodule.finrank_map_subtype_eq]

/-- Every zero-defect induced subobject of a semistable task is semistable. -/
theorem Task.IsSemistable.onComponent {T : Task K V} (hT : T.IsSemistable)
    (P : Submodule K V) (hP : T.componentDefect P=0) :
    (T.onComponent P).IsSemistable := by
  constructor
  · rw [T.onComponent_dimensionVector]
    exact hP
  · intro Q
    rw [T.onComponent_componentDefect]
    exact hT.2 _

/-- A minimal positive-rank zero-defect actual subspace is a regular-simple
subobject. Its existence is obtained by minimizing an actual finite rank. -/
theorem Task.IsSemistable.exists_regularSimple_component [FiniteDimensional K V]
    {T : Task K V} (hT : T.IsSemistable) (hne : (⊤ : Submodule K V)≠⊥) :
    ∃ P : Submodule K V, (T.onComponent P).IsRegularSimple ∧ P≠⊥ ∧
      T.componentDefect P=0 := by
  classical
  have hex : ∃ n : ℕ, ∃ P : Submodule K V,
      P≠⊥ ∧ T.componentDefect P=0 ∧ Module.finrank K P=n :=
    ⟨Module.finrank K (⊤ : Submodule K V),⊤,hne,by simpa using hT.1,rfl⟩
  obtain ⟨P,hP,hzero,hpn⟩ := Nat.find_spec hex
  have htop : (⊤ : Submodule K P)≠⊥ := by
    intro he
    apply hP
    have hm := congrArg (Submodule.map P.subtype) he
    simpa using hm
  refine ⟨P,⟨hT.onComponent P hzero,htop,?_⟩,hP,hzero⟩
  intro Q hQ
  by_cases hq : Q=⊥
  · exact Or.inl hq
  · right
    have hmap : Q.map P.subtype≠⊥ := by
      intro he
      apply hq
      apply Submodule.map_injective_of_injective (f:=P.subtype) Subtype.val_injective
      simpa using he
    have hzeroQ : T.componentDefect (Q.map P.subtype)=0 := by
      rw [←T.onComponent_componentDefect]
      exact hQ
    have hmin := Nat.find_min' hex ⟨Q.map P.subtype,hmap,hzeroQ,rfl⟩
    rw [←hpn,Submodule.finrank_map_subtype_eq] at hmin
    apply Submodule.eq_of_le_of_finrank_eq le_top
    have hle := Submodule.finrank_mono (show Q ≤ ⊤ from le_top)
    simpa only [finrank_top] using Nat.le_antisymm hle (by simpa using hmin)

/-- A regular-simple task is indecomposable as an actual six-subspace
configuration; a split would have two nonpositive defects summing to zero. -/
theorem Task.IsRegularSimple.indecomposable [FiniteDimensional K V]
    {T : Task K V} (hT : T.IsRegularSimple) : Indecomposable T.spaces ⊤ := by
  refine ⟨hT.2.1,?_⟩
  intro P Q hs
  have hadd := T.componentDefect_split hs
  have hP := hT.1.2 P
  have hQ := hT.1.2 Q
  have hz : T.componentDefect ⊤=0 := by simpa using hT.1.1
  have hPz : T.componentDefect P=0 := by omega
  obtain hp | hp := hT.2.2 P hPz
  · exact Or.inl hp
  · right
    have hh := hs.disjoint
    rw [hp] at hh
    exact disjoint_top.mp hh.symm

/-- A finite recursive certificate of successive regular-simple actual
subobjects and their actual quotients. -/
inductive RegularFiltration (K : Type) [Field K] :
    {V : Type} → [AddCommGroup V] → [Module K V] → Task K V → Prop where
  | zero {V : Type} [AddCommGroup V] [Module K V] (T : Task K V)
      (hzero : (⊤ : Submodule K V)=⊥) : RegularFiltration K T
  | step {V : Type} [AddCommGroup V] [Module K V] (T : Task K V)
      (P : Submodule K V) (hP : (T.onComponent P).IsRegularSimple)
      (hquot : RegularFiltration K (T.quotientBy P)) : RegularFiltration K T

/-- Every finite-dimensional semistable actual three-flag task has a finite
regular-simple filtration. The induction strictly decreases ambient rank. -/
theorem Task.IsSemistable.regularFiltration [FiniteDimensional K V]
    {T : Task K V} (hT : T.IsSemistable) : RegularFiltration K T := by
  have aux : ∀ n : ℕ, ∀ (W : Type) [AddCommGroup W] [Module K W]
      [FiniteDimensional K W], ∀ S : Task K W,
      Module.finrank K W=n → S.IsSemistable → RegularFiltration K S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ _ S hr hS
      by_cases hz : (⊤ : Submodule K W)=⊥
      · exact RegularFiltration.zero S hz
      obtain ⟨P,hP,hPne,hPz⟩ := hS.exists_regularSimple_component hz
      refine RegularFiltration.step S P hP ?_
      have hpos : 0 < Module.finrank K P := by
        have hlt := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.mpr hPne)
        simpa only [finrank_bot] using hlt
      have hadd := P.finrank_quotient_add_finrank
      have hlt : Module.finrank K (W ⧸ P)<n := by omega
      exact ih _ hlt (W ⧸ P) (S.quotientBy P) rfl (hS.quotientBy P hPz)
  exact aux (Module.finrank K V) V T rfl hT

end UploadBroadcast.TaskDecomposition
