import UploadBroadcast.ReducedTask
import UploadBroadcast.ResidualUpload

/-!
# Constructed coordinates and operational private reduction

The coordinate chart below is constructed from the actual three coefficient
spaces. The private reduction then retains exactly the projections occurring
in remote signals and constructs both nonlinear code transports.
-/
namespace UploadBroadcast
namespace ResidualTaskAssembly
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {K P₁ P₂ P₃ D F : Type*} [Field K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]
  [AddCommGroup F] [Module K F]
open ResidualUpload

/-- Reorder the proved private/diagonal normal form and choose the sign
which gives the manuscript's three lines v, r, and r-v. -/
def canonicalReorder : Ambient P₁ P₂ P₃ D ≃ₗ[K]
    (((D × P₁) × (D × P₂)) × P₃) where
  toFun x := (((-x.2.1,x.1.1.1),(x.2.2,x.1.1.2)),x.1.2)
  invFun x := (((x.1.1.2,x.1.2.2),x.2),(-x.1.1.1,x.1.2.1))
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' a x := by ext <;> simp

/-- Exact canonical private/tripod charts are obtained from the actual side
spaces; no normal-form certificate is supplied by the caller. -/
theorem exists_canonical_chart (A B C : Submodule K F)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hspan : A ⊔ B ⊔ C = ⊤) :
    let D := C ⊓ (A ⊔ B)
    ∃ (P₁ : Submodule K A) (P₂ : Submodule K B) (P₃ : Submodule K F)
      (e : Ambient P₁ P₂ P₃ D ≃ₗ[K] F),
      (A₁ K P₁ P₂ P₃ D).map e.toLinearMap = A ∧
      (A₂ K P₁ P₂ P₃ D).map e.toLinearMap = B ∧
      (A₃ K P₁ P₂ P₃ D).map e.toLinearMap = C := by
  dsimp only
  let D := C ⊓ (A ⊔ B)
  obtain ⟨P₁,P₂,P₃,e,h₁,h₂,h₃⟩ :=
    pairwise_disjoint_three_subspace_normal_form A B C hAB hAC hBC hspan
  let f : Ambient P₁ P₂ P₃ D ≃ₗ[K] F := canonicalReorder.trans e
  refine ⟨P₁,P₂,P₃,f,?_,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨y,⟨⟨p,t⟩,rfl⟩,rfl⟩
      apply h₁.le
      exact ⟨(-t,p),rfl⟩
    · intro hx
      obtain ⟨⟨t,p⟩,rfl⟩ := h₁.ge hx
      refine ⟨side₁ (p,-t),⟨(p,-t),rfl⟩,?_⟩
      simp [f,canonicalReorder,side₁]; rfl
  · ext x
    constructor
    · rintro ⟨y,⟨⟨p,t⟩,rfl⟩,rfl⟩
      apply h₂.le
      exact ⟨(t,p),by simp [f,canonicalReorder,side₂]; rfl⟩
    · intro hx
      obtain ⟨⟨t,p⟩,rfl⟩ := h₂.ge hx
      refine ⟨side₂ (p,t),⟨(p,t),rfl⟩,?_⟩
      simp [f,canonicalReorder,side₂]; rfl
  · ext x
    constructor
    · rintro ⟨y,⟨⟨p,t⟩,rfl⟩,rfl⟩
      apply h₃.le
      exact ⟨(t,p),by simp [f,canonicalReorder,side₃]; rfl⟩
    · intro hx
      obtain ⟨⟨t,p⟩,rfl⟩ := h₃.ge hx
      refine ⟨side₃ (p,t),⟨(p,t),rfl⟩,?_⟩
      simp [f,canonicalReorder,side₃]; rfl

/-- Canonical private-coordinate projections. -/
def private₁ : Ambient P₁ P₂ P₃ D →ₗ[K] P₁ :=
  (LinearMap.fst K P₁ P₂).comp ((LinearMap.fst K (P₁ × P₂) P₃).comp
    (LinearMap.fst K ((P₁ × P₂) × P₃) (D × D)))
def private₂ : Ambient P₁ P₂ P₃ D →ₗ[K] P₂ :=
  (LinearMap.snd K P₁ P₂).comp ((LinearMap.fst K (P₁ × P₂) P₃).comp
    (LinearMap.fst K ((P₁ × P₂) × P₃) (D × D)))
def private₃ : Ambient P₁ P₂ P₃ D →ₗ[K] P₃ :=
  (LinearMap.snd K (P₁ × P₂) P₃).comp
    (LinearMap.fst K ((P₁ × P₂) × P₃) (D × D))


/-- A definite retraction onto any retained coefficient subspace. -/
noncomputable def retainedProjection {V : Type*} [AddCommGroup V] [Module K V]
    (A : Submodule K V) : V →ₗ[K] A :=
  A.linearProjOfIsCompl (Classical.choose A.exists_isCompl)
    (Classical.choose_spec A.exists_isCompl)

@[simp] theorem retainedProjection_self {V : Type*} [AddCommGroup V] [Module K V]
    (A : Submodule K V) (a : A) : retainedProjection A a = a :=
  Submodule.linearProjOfIsCompl_apply_left _ a

variable (task : Task K (Ambient P₁ P₂ P₃ D))
/-- The retained private space is selected from both actual remote signals. -/
def used₁ : Submodule K P₁ := (task.U 1).map private₁ ⊔ (task.U 2).map private₁
def used₂ : Submodule K P₂ := (task.U 0).map private₂ ⊔ (task.U 2).map private₂
def used₃ : Submodule K P₃ := (task.U 0).map private₃ ⊔ (task.U 1).map private₃

/-- Delete all unused private directions simultaneously. Tripod coordinates
are unchanged, so one user's deletion cannot alter another's retained space. -/
noncomputable def trimProjection : Ambient P₁ P₂ P₃ D →ₗ[K]
    Ambient (used₁ task) (used₂ task) (used₃ task) D where
  toFun x := (((retainedProjection (used₁ task) x.1.1.1,
    retainedProjection (used₂ task) x.1.1.2),
    retainedProjection (used₃ task) x.1.2),x.2)
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp

def trimEmbedding : Ambient (used₁ task) (used₂ task) (used₃ task) D →ₗ[K]
    Ambient P₁ P₂ P₃ D where
  toFun x := (((x.1.1.1.val,x.1.1.2.val),x.1.2.val),x.2)
  map_add' x y := by ext <;> rfl
  map_smul' a x := by ext <;> rfl

@[simp] theorem trimProjection_embedding :
    (trimProjection task).comp (trimEmbedding task) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (((retainedProjection (used₁ task) (x.1.1.1 : P₁),
    retainedProjection (used₂ task) (x.1.1.2 : P₂)),
    retainedProjection (used₃ task) (x.1.2 : P₃)),x.2) = x
  simp only [retainedProjection_self]

noncomputable def privateTrim : Task K (Ambient (used₁ task) (used₂ task) (used₃ task) D) :=
  task.imageTask (trimProjection task)

variable
  (h₁ : task.A 0 = A₁ K P₁ P₂ P₃ D)
  (h₂ : task.A 1 = A₂ K P₁ P₂ P₃ D)
  (h₃ : task.A 2 = A₃ K P₁ P₂ P₃ D)

include h₁ h₂ h₃

/-- Every removed signal coefficient belongs to that user's own private side.
This is checked on the signals themselves, before applying any code theorem. -/
theorem trim_local (i : Three) (x : Ambient P₁ P₂ P₃ D) (hx : x ∈ task.U i) :
    x - trimEmbedding task (trimProjection task x) ∈ task.A i := by
  have hfix₁ (h : x.1.1.1 ∈ used₁ task) :
      (retainedProjection (used₁ task) x.1.1.1 : P₁) = x.1.1.1 := by
    exact congrArg Subtype.val (retainedProjection_self (used₁ task) ⟨_,h⟩)
  have hfix₂ (h : x.1.1.2 ∈ used₂ task) :
      (retainedProjection (used₂ task) x.1.1.2 : P₂) = x.1.1.2 := by
    exact congrArg Subtype.val (retainedProjection_self (used₂ task) ⟨_,h⟩)
  have hfix₃ (h : x.1.2 ∈ used₃ task) :
      (retainedProjection (used₃ task) x.1.2 : P₃) = x.1.2 := by
    exact congrArg Subtype.val (retainedProjection_self (used₃ task) ⟨_,h⟩)
  fin_cases i
  · change x ∈ task.U 0 at hx
    change _ ∈ task.A 0
    rw [h₁]
    have h₂' := hfix₂ (Submodule.mem_sup_left ⟨x,hx,rfl⟩)
    have h₃' := hfix₃ (Submodule.mem_sup_left ⟨x,hx,rfl⟩)
    refine ⟨(x.1.1.1 - retainedProjection (used₁ task) x.1.1.1,0),?_⟩
    ext <;> simp [side₁,trimEmbedding,trimProjection,h₂',h₃']
  · change x ∈ task.U 1 at hx
    change _ ∈ task.A 1
    rw [h₂]
    have h₁' := hfix₁ (Submodule.mem_sup_left ⟨x,hx,rfl⟩)
    have h₃' := hfix₃ (Submodule.mem_sup_right ⟨x,hx,rfl⟩)
    refine ⟨(x.1.1.2 - retainedProjection (used₂ task) x.1.1.2,0),?_⟩
    ext <;> simp [side₂,trimEmbedding,trimProjection,h₁',h₃']
  · change x ∈ task.U 2 at hx
    change _ ∈ task.A 2
    rw [h₃]
    have h₁' := hfix₁ (Submodule.mem_sup_right ⟨x,hx,rfl⟩)
    have h₂' := hfix₂ (Submodule.mem_sup_right ⟨x,hx,rfl⟩)
    refine ⟨(x.1.2 - retainedProjection (used₃ task) x.1.2,0),?_⟩
    ext <;> simp [side₃,trimEmbedding,trimProjection,h₁',h₂']

/-- Concrete deletion/restoration of all three unused-private complements. -/
noncomputable def trimRetraction : PassiveRetraction task (privateTrim task) := by
  let p := trimProjection task
  let e := trimEmbedding task
  have hlocal := trim_local task h₁ h₂ h₃
  have hA (i : Three) (x : Ambient P₁ P₂ P₃ D) (hx : x ∈ task.A i) :
      e (p x) ∈ task.A i := by
    have hh := (task.A i).sub_mem hx (hlocal i x (task.side_le_signal i hx))
    simpa only [sub_sub_cancel] using hh
  have hU (i : Three) (x : Ambient P₁ P₂ P₃ D) (hx : x ∈ task.U i) :
      e (p x) ∈ task.U i := by
    have hh := (task.U i).sub_mem hx (task.side_le_signal i (hlocal i x hx))
    simpa only [sub_sub_cancel] using hh
  exact passiveRetractionOfProjection task (privateTrim task) p e
    (trimProjection_embedding task)
    (fun i x hx => ⟨x,hx,rfl⟩)
    (by intro i x hx; obtain ⟨y,hy,rfl⟩ := hx; exact hA i y hy)
    (fun i x hx => ⟨x,hx,rfl⟩)
    (by intro i x hx; obtain ⟨y,hy,rfl⟩ := hx; exact hU i y hy)
    hlocal

/-- Simultaneous private deletion preserves every fixed-block nonlinear
achievable region. It does not impose linearity on the encoders or decoders. -/
theorem privateTrim_achievableAt_eq [Finite K]
    [FiniteDimensional K P₁] [FiniteDimensional K P₂]
    [FiniteDimensional K P₃] [FiniteDimensional K D] (n : ℕ) :
    task.achievableAt n = (privateTrim task).achievableAt n :=
  (trimRetraction task h₁ h₂ h₃).achievableAt_eq n

theorem privateTrim_costRegion_eq [Finite K]
    [FiniteDimensional K P₁] [FiniteDimensional K P₂]
    [FiniteDimensional K P₃] [FiniteDimensional K D] :
    task.costRegion = (privateTrim task).costRegion :=
  (trimRetraction task h₁ h₂ h₃).costRegion_eq


/-- The retained task has exactly the same canonical side-space form. -/
theorem privateTrim_sides :
    (privateTrim task).A 0 = A₁ K (used₁ task) (used₂ task) (used₃ task) D ∧
    (privateTrim task).A 1 = A₂ K (used₁ task) (used₂ task) (used₃ task) D ∧
    (privateTrim task).A 2 = A₃ K (used₁ task) (used₂ task) (used₃ task) D := by
  change (task.A 0).map (trimProjection task) = _ ∧
    (task.A 1).map (trimProjection task) = _ ∧
    (task.A 2).map (trimProjection task) = _
  rw [h₁,h₂,h₃]
  refine ⟨?_,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨y,⟨⟨p,t⟩,rfl⟩,rfl⟩
      exact ⟨(retainedProjection (used₁ task) p,t),by simp [side₁,trimProjection]⟩
    · rintro ⟨⟨p,t⟩,rfl⟩
      refine ⟨side₁ ((p : P₁),t),⟨((p : P₁),t),rfl⟩,?_⟩
      simp [side₁,trimProjection]
  · ext x
    constructor
    · rintro ⟨y,⟨⟨p,t⟩,rfl⟩,rfl⟩
      exact ⟨(retainedProjection (used₂ task) p,t),by simp [side₂,trimProjection]⟩
    · rintro ⟨⟨p,t⟩,rfl⟩
      refine ⟨side₂ ((p : P₂),t),⟨((p : P₂),t),rfl⟩,?_⟩
      simp [side₂,trimProjection]
  · ext x
    constructor
    · rintro ⟨y,⟨⟨p,t⟩,rfl⟩,rfl⟩
      exact ⟨(retainedProjection (used₃ task) p,t),by simp [side₃,trimProjection]⟩
    · rintro ⟨⟨p,t⟩,rfl⟩
      refine ⟨side₃ ((p : P₃),t),⟨((p : P₃),t),rfl⟩,?_⟩
      simp [side₃,trimProjection]

omit h₁ h₂ h₃

/-- A retained subspace maps onto all of its own subtype. -/
theorem map_retainedProjection_top {V : Type*} [AddCommGroup V] [Module K V]
    (A : Submodule K V) : A.map (retainedProjection A) = ⊤ := by
  apply top_unique
  intro a _
  exact ⟨a,a.property,retainedProjection_self A a⟩

/-- The retained private spaces are fully used by remote demands, exactly as
in equation (rho). This is a conclusion of the construction, not a hypothesis. -/
theorem privateTrim_fully_used :
    used₁ (privateTrim task) = ⊤ ∧ used₂ (privateTrim task) = ⊤ ∧
    used₃ (privateTrim task) = ⊤ := by
  have hp₁ : (private₁ (K := K)).comp (trimProjection task) =
      (retainedProjection (used₁ task)).comp private₁ := rfl
  have hp₂ : (private₂ (K := K)).comp (trimProjection task) =
      (retainedProjection (used₂ task)).comp private₂ := rfl
  have hp₃ : (private₃ (K := K)).comp (trimProjection task) =
      (retainedProjection (used₃ task)).comp private₃ := rfl
  refine ⟨?_,?_,?_⟩
  · change ((task.U 1).map (trimProjection task)).map private₁ ⊔
      ((task.U 2).map (trimProjection task)).map private₁ = ⊤
    rw [← Submodule.map_comp,← Submodule.map_comp,hp₁]
    rw [Submodule.map_comp,Submodule.map_comp,← Submodule.map_sup]
    exact map_retainedProjection_top (used₁ task)
  · change ((task.U 0).map (trimProjection task)).map private₂ ⊔
      ((task.U 2).map (trimProjection task)).map private₂ = ⊤
    rw [← Submodule.map_comp,← Submodule.map_comp,hp₂]
    rw [Submodule.map_comp,Submodule.map_comp,← Submodule.map_sup]
    exact map_retainedProjection_top (used₂ task)
  · change ((task.U 0).map (trimProjection task)).map private₃ ⊔
      ((task.U 1).map (trimProjection task)).map private₃ = ⊤
    rw [← Submodule.map_comp,← Submodule.map_comp,hp₃]
    rw [Submodule.map_comp,Submodule.map_comp,← Submodule.map_sup]
    exact map_retainedProjection_top (used₃ task)


section DemandGraphs
variable {P T : Type*} [AddCommGroup P] [Module K P] [AddCommGroup T] [Module K T]
/-- Lift the actual quotient-valued demand graph to the tripod space. The
pure space is still the intersection, never the tripod projection of Q. -/
theorem exists_liftedDemandGraph (Q : Submodule K (P × T)) :
    ∃ φ : P →ₗ[K] T, ∀ p t, (p,t) ∈ Q ↔
      p ∈ Q.map (LinearMap.fst K P T) ∧
      t - φ p ∈ Q.comap (LinearMap.inr K P T) := by
  let D := Q.comap (LinearMap.inr K P T)
  obtain ⟨f,hf⟩ := pureDemandGraph_characterization Q
  obtain ⟨S,hS⟩ := D.exists_isCompl
  let e := Submodule.quotientEquivOfIsCompl D S hS
  let φ := S.subtype.comp (e.toLinearMap.comp f)
  have hφ (p : P) : D.mkQ (φ p) = f p :=
    Submodule.mk_quotientEquivOfIsCompl_apply D S hS (f p)
  refine ⟨φ,?_⟩
  intro p t
  rw [hf]
  apply and_congr_right
  intro _
  rw [← Submodule.Quotient.mk_eq_zero D]
  change f p = D.mkQ t ↔ D.mkQ (t - φ p) = 0
  rw [map_sub,hφ,sub_eq_zero]
  exact eq_comm
end DemandGraphs

/-- User-one demand coordinates after quotienting only its own side space. -/
def demandQuotient₁ : Ambient P₁ P₂ P₃ D →ₗ[K] ((P₂ × P₃) × D) where
  toFun x := ((x.1.1.2,x.1.2),x.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def demandQuotient₂ : Ambient P₁ P₂ P₃ D →ₗ[K] ((P₁ × P₃) × D) where
  toFun x := ((x.1.1.1,x.1.2),x.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def demandQuotient₃ : Ambient P₁ P₂ P₃ D →ₗ[K] ((P₁ × P₂) × D) where
  toFun x := ((x.1.1.1,x.1.1.2),x.2.1 + x.2.2)
  map_add' x y := by ext <;> simp [add_comm,add_left_comm,add_assoc]
  map_smul' a x := by ext <;> simp [smul_add]

/-- Linear representatives of the three demand quotient spaces. -/
def demandLift₁ : ((P₂ × P₃) × D) →ₗ[K] Ambient P₁ P₂ P₃ D where
  toFun x := (((0,x.1.1),x.1.2),(0,x.2))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def demandLift₂ : ((P₁ × P₃) × D) →ₗ[K] Ambient P₁ P₂ P₃ D where
  toFun x := (((x.1.1,0),x.1.2),(x.2,0))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def demandLift₃ : ((P₁ × P₂) × D) →ₗ[K] Ambient P₁ P₂ P₃ D where
  toFun x := (((x.1.1,x.1.2),0),(x.2,0))
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

/-- Subtracting the selected quotient representative leaves exactly local
side information, including the v+r quotient for the third user. -/
theorem demandLift_remainder :
    (∀ x : Ambient P₁ P₂ P₃ D, x - demandLift₁ (K := K) (demandQuotient₁ (K := K) x) ∈ A₁ K P₁ P₂ P₃ D) ∧
    (∀ x : Ambient P₁ P₂ P₃ D, x - demandLift₂ (K := K) (demandQuotient₂ (K := K) x) ∈ A₂ K P₁ P₂ P₃ D) ∧
    (∀ x : Ambient P₁ P₂ P₃ D, x - demandLift₃ (K := K) (demandQuotient₃ (K := K) x) ∈ A₃ K P₁ P₂ P₃ D) := by
  refine ⟨?_,?_,?_⟩
  · intro x
    exact ⟨(x.1.1.1,x.2.1),by ext <;> simp [side₁,demandLift₁,demandQuotient₁]⟩
  · intro x
    exact ⟨(x.1.1.2,x.2.2),by ext <;> simp [side₂,demandLift₂,demandQuotient₂]⟩
  · intro x
    exact ⟨(x.1.2,x.2.2),by ext <;> simp [side₃,demandLift₃,demandQuotient₃]⟩

/-- A side-containing signal is recovered exactly from its quotient image.
The statement is purely about actual coefficient spaces. -/
theorem signal_eq_side_sup_lift {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (A U : Submodule K V) (hAU : A ≤ U)
    (q : V →ₗ[K] W) (s : W →ₗ[K] V) (hlocal : ∀ x, x - s (q x) ∈ A) :
    U = A ⊔ (U.map q).map s := by
  apply le_antisymm
  · intro x hx
    have hh := Submodule.add_mem_sup (hlocal x)
      (show s (q x) ∈ (U.map q).map s from ⟨q x,⟨x,hx,rfl⟩,rfl⟩)
    simpa using hh
  · apply sup_le hAU
    rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
    have hh := U.sub_mem hz (hAU (hlocal z))
    simpa only [sub_sub_cancel] using hh

include h₁ h₂ h₃
/-- All three actual signals admit exact private-plus-tripod quotient
coordinates, simultaneously in the same ambient chart. -/
theorem actual_signal_quotients :
    task.U 0 = task.A 0 ⊔ ((task.U 0).map demandQuotient₁).map demandLift₁ ∧
    task.U 1 = task.A 1 ⊔ ((task.U 1).map demandQuotient₂).map demandLift₂ ∧
    task.U 2 = task.A 2 ⊔ ((task.U 2).map demandQuotient₃).map demandLift₃ := by
  obtain ⟨hl₁,hl₂,hl₃⟩ := demandLift_remainder (K := K) (P₁ := P₁) (P₂ := P₂)
    (P₃ := P₃) (D := D)
  refine ⟨signal_eq_side_sup_lift _ _ (task.side_le_signal 0) _ _ ?_,
    signal_eq_side_sup_lift _ _ (task.side_le_signal 1) _ _ ?_,
    signal_eq_side_sup_lift _ _ (task.side_le_signal 2) _ _ ?_⟩
  · simpa only [h₁] using hl₁
  · simpa only [h₂] using hl₂
  · simpa only [h₃] using hl₃
omit h₁ h₂ h₃


/-- Quotient membership loses only locally known coefficients. -/
theorem mem_signal_iff_quotient {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (A U : Submodule K V) (hAU : A ≤ U)
    (q : V →ₗ[K] W) (s : W →ₗ[K] V) (hlocal : ∀ x, x - s (q x) ∈ A) (x : V) :
    x ∈ U ↔ q x ∈ U.map q := by
  constructor
  · intro hx; exact ⟨x,hx,rfl⟩
  · rintro ⟨y,hy,he⟩
    have hs : s (q y) ∈ U := by
      simpa only [sub_sub_cancel] using U.sub_mem hy (hAU (hlocal y))
    rw [he] at hs
    simpa using U.add_mem (hAU (hlocal x)) hs

/-- The three actual quotient-demand subspaces. -/
def quotientSignal₁ := (task.U 0).map (demandQuotient₁ (K := K))
def quotientSignal₂ := (task.U 1).map (demandQuotient₂ (K := K))
def quotientSignal₃ := (task.U 2).map (demandQuotient₃ (K := K))

def privateDomain₁ := (quotientSignal₁ task).map (LinearMap.fst K (P₂ × P₃) D)
def privateDomain₂ := (quotientSignal₂ task).map (LinearMap.fst K (P₁ × P₃) D)
def privateDomain₃ := (quotientSignal₃ task).map (LinearMap.fst K (P₁ × P₂) D)

/-- Pure demand rows are actual intersections with the tripod summand. -/
def pureRows₁ := (quotientSignal₁ task).comap (LinearMap.inr K (P₂ × P₃) D)
def pureRows₂ := (quotientSignal₂ task).comap (LinearMap.inr K (P₁ × P₃) D)
def pureRows₃ := (quotientSignal₃ task).comap (LinearMap.inr K (P₁ × P₂) D)

/-- Lifted demand graphs selected from a task, with exact signal membership.
The graph maps are extended to the whole remote-private product merely for
convenient evaluation; the actual domains remain privateDomain_i. -/
structure DemandData where
  φ₁ : (P₂ × P₃) →ₗ[K] D
  φ₂ : (P₁ × P₃) →ₗ[K] D
  φ₃ : (P₁ × P₂) →ₗ[K] D
  mem₁ : ∀ x, x ∈ task.U 0 ↔ (x.1.1.2,x.1.2) ∈ privateDomain₁ task ∧
    x.2.2 - φ₁ (x.1.1.2,x.1.2) ∈ pureRows₁ task
  mem₂ : ∀ x, x ∈ task.U 1 ↔ (x.1.1.1,x.1.2) ∈ privateDomain₂ task ∧
    x.2.1 - φ₂ (x.1.1.1,x.1.2) ∈ pureRows₂ task
  mem₃ : ∀ x, x ∈ task.U 2 ↔ (x.1.1.1,x.1.1.2) ∈ privateDomain₃ task ∧
    (x.2.1 + x.2.2) - φ₃ (x.1.1.1,x.1.1.2) ∈ pureRows₃ task

include h₁ h₂ h₃
/-- Every task with the canonical side spaces has constructed graph data. -/
theorem exists_demandData : Nonempty (DemandData task) := by
  obtain ⟨f₁,hf₁⟩ := exists_liftedDemandGraph (quotientSignal₁ task)
  obtain ⟨f₂,hf₂⟩ := exists_liftedDemandGraph (quotientSignal₂ task)
  obtain ⟨f₃,hf₃⟩ := exists_liftedDemandGraph (quotientSignal₃ task)
  obtain ⟨hl₁,hl₂,hl₃⟩ := demandLift_remainder (K := K) (P₁ := P₁) (P₂ := P₂)
    (P₃ := P₃) (D := D)
  refine ⟨⟨f₁,f₂,f₃,?_,?_,?_⟩⟩
  · intro x
    exact (mem_signal_iff_quotient _ _ (task.side_le_signal 0) demandQuotient₁ demandLift₁
      (by simpa only [h₁] using hl₁) x).trans (hf₁ _ _)
  · intro x
    exact (mem_signal_iff_quotient _ _ (task.side_le_signal 1) demandQuotient₂ demandLift₂
      (by simpa only [h₂] using hl₂) x).trans (hf₂ _ _)
  · intro x
    exact (mem_signal_iff_quotient _ _ (task.side_le_signal 2) demandQuotient₃ demandLift₃
      (by simpa only [h₃] using hl₃) x).trans (hf₃ _ _)
omit h₁ h₂ h₃

namespace DemandData
variable {task} (g : DemandData task)
/-- The actual direct sum of the three remote-private demand domains. -/
abbrev Relations := ((privateDomain₁ task) × (privateDomain₂ task)) × privateDomain₃ task

/-- Signed private incidence map of equation (upload-matrices). -/
def incidence : Relations (task := task) →ₗ[K] ((P₁ × P₂) × P₃) where
  toFun x := ((x.1.2.val.1 + x.2.val.1,x.1.1.val.1 + x.2.val.2),
    x.1.1.val.2 - x.1.2.val.2)
  map_add' x y := by ext <;> simp <;> abel
  map_smul' a x := by ext <;> simp [smul_add,smul_sub]

def relationRows : Relations (task := task) →ₗ[K] D where
  toFun x := g.φ₁ x.1.1.val + g.φ₂ x.1.2.val + g.φ₃ x.2.val
  map_add' x y := by simp [map_add]; abel
  map_smul' a x := by simp [map_smul,smul_add]

/-- Retain all pure rows and precisely the rows arising from zero-private
relations. Its definition uses actual signals and constructed graph lifts. -/
def activeRows : Submodule K D :=
  (pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task) ⊔
    (LinearMap.ker (incidence (task := task))).map g.relationRows


/-- The component outside activeRows vanishes on ker B, so it is canceled
by one simultaneous private correction. This chooses the correction from the
actual demand maps instead of assuming a cancellation certificate. -/
theorem exists_empty_cancellation :
    ∃ f : ((P₁ × P₂) × P₃) →ₗ[K] D,
      (∀ x : privateDomain₁ task, g.φ₁ x.val - f ((0,x.val.1),x.val.2) ∈ g.activeRows) ∧
      (∀ x : privateDomain₂ task, g.φ₂ x.val - f ((x.val.1,0),-x.val.2) ∈ g.activeRows) ∧
      (∀ x : privateDomain₃ task, g.φ₃ x.val - f ((x.val.1,x.val.2),0) ∈ g.activeRows) := by
  let q := g.activeRows.mkQ
  have hker : LinearMap.ker (incidence (task := task)) ≤
      LinearMap.ker (q.comp g.relationRows) := by
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero g.activeRows).mpr
    exact Submodule.mem_sup_right ⟨x,hx,rfl⟩
  obtain ⟨h,hh⟩ := factors_through_of_ker_le (incidence (task := task))
    (q.comp g.relationRows) hker
  obtain ⟨N,hN⟩ := g.activeRows.exists_isCompl
  let e := Submodule.quotientEquivOfIsCompl g.activeRows N hN
  let f := N.subtype.comp (e.toLinearMap.comp h)
  have hf (p : ((P₁ × P₂) × P₃)) : q (f p) = h p :=
    Submodule.mk_quotientEquivOfIsCompl_apply g.activeRows N hN (h p)
  have hrow (x : Relations (task := task)) :
      g.relationRows x - f (incidence x) ∈ g.activeRows := by
    apply (Submodule.Quotient.mk_eq_zero g.activeRows).mp
    change q (g.relationRows x - f (incidence x)) = 0
    rw [map_sub,hf]
    have he := LinearMap.congr_fun hh x
    exact sub_eq_zero.mpr he.symm
  refine ⟨f,?_,?_,?_⟩
  · intro x
    simpa [relationRows,incidence] using hrow ((x,0),0)
  · intro x
    simpa [relationRows,incidence] using hrow ((0,x),0)
  · intro x
    simpa [relationRows,incidence] using hrow ((0,0),x)

end DemandData

section RowDeletion
variable (R : Submodule K D)
/-- Delete only tripod rows outside the retained row subspace. -/
noncomputable def rowProjection : Ambient P₁ P₂ P₃ D →ₗ[K] Ambient P₁ P₂ P₃ R where
  toFun x := (x.1,(retainedProjection R x.2.1,retainedProjection R x.2.2))
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp

def rowEmbedding : Ambient P₁ P₂ P₃ R →ₗ[K] Ambient P₁ P₂ P₃ D where
  toFun x := (x.1,(x.2.1.val,x.2.2.val))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem rowProjection_embedding :
    (rowProjection (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) R).comp (rowEmbedding R) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (x.1,(retainedProjection R (x.2.1 : D),retainedProjection R (x.2.2 : D))) = x
  simp only [retainedProjection_self]

noncomputable def rowTrim : Task K (Ambient P₁ P₂ P₃ R) := task.imageTask (rowProjection R)

variable
  (hr₁ : ∀ x ∈ task.U 0, x.2.2 ∈ R)
  (hr₂ : ∀ x ∈ task.U 1, x.2.1 ∈ R)
  (hr₃ : ∀ x ∈ task.U 2, x.2.1 + x.2.2 ∈ R)
include h₁ h₂ h₃ hr₁ hr₂ hr₃
/-- On every signal, the discarded tripod part lies on the user's own
side-information line. This is the operational side-only condition. -/
theorem row_local (i : Three) (x : Ambient P₁ P₂ P₃ D) (hx : x ∈ task.U i) :
    x - rowEmbedding R (rowProjection R x) ∈ task.A i := by
  have hfix (d : D) (hd : d ∈ R) : (retainedProjection R d : D) = d :=
    congrArg Subtype.val (retainedProjection_self R ⟨d,hd⟩)
  fin_cases i
  · change x ∈ task.U 0 at hx
    change _ ∈ task.A 0
    rw [h₁]
    refine ⟨(0,x.2.1 - retainedProjection R x.2.1),?_⟩
    ext <;> simp [side₁,rowEmbedding,rowProjection,hfix _ (hr₁ x hx)]
  · change x ∈ task.U 1 at hx
    change _ ∈ task.A 1
    rw [h₂]
    refine ⟨(0,x.2.2 - retainedProjection R x.2.2),?_⟩
    ext <;> simp [side₂,rowEmbedding,rowProjection,hfix _ (hr₂ x hx)]
  · change x ∈ task.U 2 at hx
    change _ ∈ task.A 2
    rw [h₃]
    have hh := hfix _ (hr₃ x hx)
    have hh' : (retainedProjection R x.2.1 : D) + retainedProjection R x.2.2 =
        x.2.1 + x.2.2 := by simpa only [map_add,Submodule.coe_add] using hh
    refine ⟨(0,x.2.2 - retainedProjection R x.2.2),?_⟩
    ext <;> simp only [side₃,rowEmbedding,rowProjection,LinearMap.coe_mk,AddHom.coe_mk,
      Prod.fst_sub,Prod.snd_sub,sub_self,Prod.fst_zero,Prod.snd_zero]
    apply eq_of_sub_eq_zero
    calc
      -(x.2.2 - (retainedProjection R x.2.2 : D)) -
          (x.2.1 - (retainedProjection R x.2.1 : D)) =
          ((retainedProjection R x.2.1 : D) + retainedProjection R x.2.2) -
            (x.2.1 + x.2.2) := by abel
      _ = 0 := sub_eq_zero.mpr hh'

noncomputable def rowRetraction : PassiveRetraction task (rowTrim task R) := by
  let p := rowProjection (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) R
  let e := rowEmbedding (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) R
  have hlocal := row_local task h₁ h₂ h₃ R hr₁ hr₂ hr₃
  have hA (i : Three) (x : Ambient P₁ P₂ P₃ D) (hx : x ∈ task.A i) : e (p x) ∈ task.A i := by
    simpa only [sub_sub_cancel] using
      (task.A i).sub_mem hx (hlocal i x (task.side_le_signal i hx))
  have hU (i : Three) (x : Ambient P₁ P₂ P₃ D) (hx : x ∈ task.U i) : e (p x) ∈ task.U i := by
    simpa only [sub_sub_cancel] using
      (task.U i).sub_mem hx (task.side_le_signal i (hlocal i x hx))
  exact passiveRetractionOfProjection task (rowTrim task R) p e (rowProjection_embedding R)
    (fun i x hx => ⟨x,hx,rfl⟩)
    (by intro i x hx; obtain ⟨y,hy,rfl⟩ := hx; exact hA i y hy)
    (fun i x hx => ⟨x,hx,rfl⟩)
    (by intro i x hx; obtain ⟨y,hy,rfl⟩ := hx; exact hU i y hy)
    hlocal

theorem rowTrim_achievableAt_eq [Finite K]
    [FiniteDimensional K P₁] [FiniteDimensional K P₂]
    [FiniteDimensional K P₃] [FiniteDimensional K D] (n : ℕ) :
    task.achievableAt n = (rowTrim task R).achievableAt n :=
  (rowRetraction task h₁ h₂ h₃ R hr₁ hr₂ hr₃).achievableAt_eq n
omit h₁ h₂ h₃ hr₁ hr₂ hr₃

include h₁ h₂ h₃
/-- The row-reduced side spaces retain the identical three-line pattern. -/
theorem rowTrim_sides :
    (rowTrim task R).A 0 = A₁ K P₁ P₂ P₃ R ∧
    (rowTrim task R).A 1 = A₂ K P₁ P₂ P₃ R ∧
    (rowTrim task R).A 2 = A₃ K P₁ P₂ P₃ R := by
  change (task.A 0).map (rowProjection R) = _ ∧
    (task.A 1).map (rowProjection R) = _ ∧
    (task.A 2).map (rowProjection R) = _
  rw [h₁,h₂,h₃]
  refine ⟨?_,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨y,⟨⟨p,t⟩,rfl⟩,rfl⟩
      exact ⟨(p,retainedProjection R t),by simp [side₁,rowProjection]⟩
    · rintro ⟨⟨p,t⟩,rfl⟩
      refine ⟨side₁ (p,(t : D)),⟨(p,(t : D)),rfl⟩,?_⟩
      simp [side₁,rowProjection]
  · ext x
    constructor
    · rintro ⟨y,⟨⟨p,t⟩,rfl⟩,rfl⟩
      exact ⟨(p,retainedProjection R t),by simp [side₂,rowProjection]⟩
    · rintro ⟨⟨p,t⟩,rfl⟩
      refine ⟨side₂ (p,(t : D)),⟨(p,(t : D)),rfl⟩,?_⟩
      simp [side₂,rowProjection]
  · ext x
    constructor
    · rintro ⟨y,⟨⟨p,t⟩,rfl⟩,rfl⟩
      exact ⟨(p,retainedProjection R t),by simp [side₃,rowProjection]⟩
    · rintro ⟨⟨p,t⟩,rfl⟩
      refine ⟨side₃ (p,(t : D)),⟨(p,(t : D)),rfl⟩,?_⟩
      simp [side₃,rowProjection]
omit h₁ h₂ h₃
end RowDeletion

/-- A simultaneous private-to-tripod correction in the signed incidence
convention. Its values on each private summand lie on that owner's line. -/
def privateGauge (f : ((P₁ × P₂) × P₃) →ₗ[K] D) :
    Ambient P₁ P₂ P₃ D →ₗ[K] Ambient P₁ P₂ P₃ D where
  toFun x := (0,(f ((x.1.1.1,0),-x.1.2),f ((0,x.1.1.2),x.1.2)))
  map_add' x y := by
    ext <;> simp [map_add,neg_add,Prod.add_def]
    all_goals
      rw [← map_add]
      congr 1
      ext <;> simp [add_comm]
  map_smul' a x := by
    ext <;> simp [map_smul,Prod.smul_def]
    all_goals
      rw [← map_smul]
      congr 1
      ext <;> simp

theorem privateGauge_square_zero (f : ((P₁ × P₂) × P₃) →ₗ[K] D) :
    (privateGauge f).comp (privateGauge f) = 0 := by
  ext x <;> simp [privateGauge]

def privateGaugeShear (f : ((P₁ × P₂) × P₃) →ₗ[K] D) :
    Ambient P₁ P₂ P₃ D ≃ₗ[K] Ambient P₁ P₂ P₃ D :=
  squareZeroShear (privateGauge f) (privateGauge_square_zero f)

theorem privateGaugeShear_sides (f : ((P₁ × P₂) × P₃) →ₗ[K] D) :
    (A₁ K P₁ P₂ P₃ D).map (privateGaugeShear f).toLinearMap = A₁ K P₁ P₂ P₃ D ∧
    (A₂ K P₁ P₂ P₃ D).map (privateGaugeShear f).toLinearMap = A₂ K P₁ P₂ P₃ D ∧
    (A₃ K P₁ P₂ P₃ D).map (privateGaugeShear f).toLinearMap = A₃ K P₁ P₂ P₃ D := by
  refine ⟨squareZeroShear_preserves _ _ _ ?_,squareZeroShear_preserves _ _ _ ?_,
    squareZeroShear_preserves _ _ _ ?_⟩
  · rintro _ ⟨⟨p,t⟩,rfl⟩
    exact ⟨(0,f ((p,0),0)),by simp [side₁,privateGauge]⟩
  · rintro _ ⟨⟨p,t⟩,rfl⟩
    exact ⟨(0,f ((0,p),0)),by simp [side₂,privateGauge]⟩
  · rintro _ ⟨⟨p,t⟩,rfl⟩
    refine ⟨(0,f ((0,0),p)),?_⟩
    have hh : f ((0,0),-p) = -f ((0,0),p) := by
      simpa only [Prod.neg_mk,neg_zero] using f.map_neg ((0,0),p)
    simp [side₃,privateGauge,hh]
    exact hh.symm

namespace DemandData
variable {task} (g : DemandData task)
/-- One chosen simultaneous correction, obtained from actual graph data. -/
noncomputable def emptyCorrection : ((P₁ × P₂) × P₃) →ₗ[K] D :=
  Classical.choose g.exists_empty_cancellation

theorem emptyCorrection_spec :
    (∀ x : privateDomain₁ task, g.φ₁ x.val - g.emptyCorrection ((0,x.val.1),x.val.2) ∈ g.activeRows) ∧
    (∀ x : privateDomain₂ task, g.φ₂ x.val - g.emptyCorrection ((x.val.1,0),-x.val.2) ∈ g.activeRows) ∧
    (∀ x : privateDomain₃ task, g.φ₃ x.val - g.emptyCorrection ((x.val.1,x.val.2),0) ∈ g.activeRows) :=
  Classical.choose_spec g.exists_empty_cancellation

noncomputable def correctedTask : Task K (Ambient P₁ P₂ P₃ D) :=
  Profile.mapTask (privateGaugeShear g.emptyCorrection) task

include h₁ h₂ h₃
theorem correctedTask_sides :
    g.correctedTask.A 0 = A₁ K P₁ P₂ P₃ D ∧
    g.correctedTask.A 1 = A₂ K P₁ P₂ P₃ D ∧
    g.correctedTask.A 2 = A₃ K P₁ P₂ P₃ D := by
  change (task.A 0).map _ = _ ∧ (task.A 1).map _ = _ ∧ (task.A 2).map _ = _
  rw [h₁,h₂,h₃]
  exact privateGaugeShear_sides g.emptyCorrection
omit h₁ h₂ h₃

/-- The chosen correction removes every demand outside the retained row
space in all three users at once. -/
theorem correctedTask_rows :
    (∀ x ∈ g.correctedTask.U 0, x.2.2 ∈ g.activeRows) ∧
    (∀ x ∈ g.correctedTask.U 1, x.2.1 ∈ g.activeRows) ∧
    (∀ x ∈ g.correctedTask.U 2, x.2.1 + x.2.2 ∈ g.activeRows) := by
  obtain ⟨hc₁,hc₂,hc₃⟩ := g.emptyCorrection_spec
  refine ⟨?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨hp,hd⟩ := (g.mem₁ x).mp hx
    have hpure : x.2.2 - g.φ₁ (x.1.1.2,x.1.2) ∈ g.activeRows :=
      Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left hd))
    have h := g.activeRows.add_mem hpure (hc₁ ⟨_,hp⟩)
    change x.2.2 - g.emptyCorrection ((0,x.1.1.2),x.1.2) ∈ g.activeRows
    convert h using 1; abel
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨hp,hd⟩ := (g.mem₂ x).mp hx
    have hpure : x.2.1 - g.φ₂ (x.1.1.1,x.1.2) ∈ g.activeRows :=
      Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right hd))
    have h := g.activeRows.add_mem hpure (hc₂ ⟨_,hp⟩)
    change x.2.1 - g.emptyCorrection ((x.1.1.1,0),-x.1.2) ∈ g.activeRows
    convert h using 1; abel
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨hp,hd⟩ := (g.mem₃ x).mp hx
    have hpure : x.2.1 + x.2.2 - g.φ₃ (x.1.1.1,x.1.1.2) ∈ g.activeRows :=
      Submodule.mem_sup_left (Submodule.mem_sup_right hd)
    have h := g.activeRows.add_mem hpure (hc₃ ⟨_,hp⟩)
    have hf : g.emptyCorrection ((x.1.1.1,0),-x.1.2) +
        g.emptyCorrection ((0,x.1.1.2),x.1.2) =
        g.emptyCorrection ((x.1.1.1,x.1.1.2),0) := by
      rw [← map_add]
      simp only [Prod.add_def,add_zero,zero_add,neg_add_cancel]
    change (x.2.1 - g.emptyCorrection ((x.1.1.1,0),-x.1.2)) +
      (x.2.2 - g.emptyCorrection ((0,x.1.1.2),x.1.2)) ∈ g.activeRows
    have he : (x.2.1 - g.emptyCorrection ((x.1.1.1,0),-x.1.2)) +
        (x.2.2 - g.emptyCorrection ((0,x.1.1.2),x.1.2)) =
        (x.2.1 + x.2.2 - g.φ₃ (x.1.1.1,x.1.1.2)) +
          (g.φ₃ (x.1.1.1,x.1.1.2) - g.emptyCorrection ((x.1.1.1,x.1.1.2),0)) := by
      rw [← hf]
      abel
    exact he.symm ▸ h

/-- The actual task after empty-tripod cancellation and passive-row deletion. -/
noncomputable def activeRowReduction : Task K (Ambient P₁ P₂ P₃ g.activeRows) :=
  rowTrim g.correctedTask g.activeRows

include h₁ h₂ h₃
/-- Operational empty-row reduction, derived from the actual task and its
constructed graphs. Every fixed-block nonlinear achievable region is equal. -/
theorem activeRowReduction_achievableAt_eq [Finite K]
    [FiniteDimensional K P₁] [FiniteDimensional K P₂]
    [FiniteDimensional K P₃] [FiniteDimensional K D] (n : ℕ) :
    task.achievableAt n = g.activeRowReduction.achievableAt n := by
  obtain ⟨hs₁,hs₂,hs₃⟩ := g.correctedTask_sides h₁ h₂ h₃
  obtain ⟨hr₁,hr₂,hr₃⟩ := g.correctedTask_rows
  exact (task.coordinate_achievableAt_eq (privateGaugeShear g.emptyCorrection) n).trans
    (rowTrim_achievableAt_eq g.correctedTask hs₁ hs₂ hs₃ g.activeRows hr₁ hr₂ hr₃ n)

theorem activeRowReduction_costRegion_eq [Finite K]
    [FiniteDimensional K P₁] [FiniteDimensional K P₂]
    [FiniteDimensional K P₃] [FiniteDimensional K D] :
    task.costRegion = g.activeRowReduction.costRegion := by
  unfold Task.costRegion
  simp_rw [g.activeRowReduction_achievableAt_eq h₁ h₂ h₃]

theorem activeRowReduction_sides :
    g.activeRowReduction.A 0 = A₁ K P₁ P₂ P₃ g.activeRows ∧
    g.activeRowReduction.A 1 = A₂ K P₁ P₂ P₃ g.activeRows ∧
    g.activeRowReduction.A 2 = A₃ K P₁ P₂ P₃ g.activeRows := by
  obtain ⟨hs₁,hs₂,hs₃⟩ := g.correctedTask_sides h₁ h₂ h₃
  exact rowTrim_sides g.correctedTask hs₁ hs₂ hs₃ g.activeRows
omit h₁ h₂ h₃
end DemandData

/-- Row deletion leaves every private signal projection unchanged. -/
theorem rowTrim_used (R : Submodule K D) :
    used₁ (rowTrim task R) = used₁ task ∧ used₂ (rowTrim task R) = used₂ task ∧
    used₃ (rowTrim task R) = used₃ task := by
  have hp₁ : (private₁ (K := K)).comp (rowProjection (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) R) = private₁ := rfl
  have hp₂ : (private₂ (K := K)).comp (rowProjection (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) R) = private₂ := rfl
  have hp₃ : (private₃ (K := K)).comp (rowProjection (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) R) = private₃ := rfl
  simp only [used₁,used₂,used₃,rowTrim,Task.imageTask,← Submodule.map_comp,hp₁,hp₂,hp₃,and_self]

namespace DemandData
variable {task} (g : DemandData task)
/-- Private activity survives both the private shear and the row projection. -/
theorem activeRowReduction_used :
    used₁ g.activeRowReduction = used₁ task ∧
    used₂ g.activeRowReduction = used₂ task ∧
    used₃ g.activeRowReduction = used₃ task := by
  have hp₁ : (private₁ (K := K)).comp (privateGaugeShear g.emptyCorrection).toLinearMap = private₁ := by
    apply LinearMap.ext
    intro x
    change x.1.1.1 - 0 = x.1.1.1
    exact sub_zero _
  have hp₂ : (private₂ (K := K)).comp (privateGaugeShear g.emptyCorrection).toLinearMap = private₂ := by
    apply LinearMap.ext
    intro x
    change x.1.1.2 - 0 = x.1.1.2
    exact sub_zero _
  have hp₃ : (private₃ (K := K)).comp (privateGaugeShear g.emptyCorrection).toLinearMap = private₃ := by
    apply LinearMap.ext
    intro x
    change x.1.2 - 0 = x.1.2
    exact sub_zero _
  obtain ⟨h₁,h₂,h₃⟩ := rowTrim_used g.correctedTask g.activeRows
  change used₁ (rowTrim g.correctedTask g.activeRows) = _ ∧
    used₂ (rowTrim g.correctedTask g.activeRows) = _ ∧
    used₃ (rowTrim g.correctedTask g.activeRows) = _
  rw [h₁,h₂,h₃]
  simp only [used₁,used₂,used₃,correctedTask,Profile.mapTask,← Submodule.map_comp,hp₁,hp₂,hp₃,and_self]
end DemandData

/-- Select the exact demand graph maps from the actual task. -/
noncomputable def selectedDemandData : DemandData task :=
  Classical.choice (exists_demandData task h₁ h₂ h₃)

/-- First remove unused private coordinates, then construct the actual
private cancellation and remove every passive tripod row. -/
noncomputable def selectedTrimData : DemandData (privateTrim task) :=
  selectedDemandData (privateTrim task)
    (privateTrim_sides task h₁ h₂ h₃).1
    (privateTrim_sides task h₁ h₂ h₃).2.1
    (privateTrim_sides task h₁ h₂ h₃).2.2

noncomputable def canonicalReduction : Task K
    (Ambient (used₁ task) (used₂ task) (used₃ task) (selectedTrimData task h₁ h₂ h₃).activeRows) :=
  (selectedTrimData task h₁ h₂ h₃).activeRowReduction

include h₁ h₂ h₃
/-- End-to-end operational reduction for arbitrary demand subspaces in the
canonical side chart. No graphs, complements, gauges, or reductions are input. -/
theorem canonicalReduction_achievableAt_eq [Finite K]
    [FiniteDimensional K P₁] [FiniteDimensional K P₂]
    [FiniteDimensional K P₃] [FiniteDimensional K D] (n : ℕ) :
    task.achievableAt n = (canonicalReduction task h₁ h₂ h₃).achievableAt n := by
  obtain ⟨hs₁,hs₂,hs₃⟩ := privateTrim_sides task h₁ h₂ h₃
  exact (privateTrim_achievableAt_eq task h₁ h₂ h₃ n).trans
    ((selectedTrimData task h₁ h₂ h₃).activeRowReduction_achievableAt_eq hs₁ hs₂ hs₃ n)

theorem canonicalReduction_costRegion_eq [Finite K]
    [FiniteDimensional K P₁] [FiniteDimensional K P₂]
    [FiniteDimensional K P₃] [FiniteDimensional K D] :
    task.costRegion = (canonicalReduction task h₁ h₂ h₃).costRegion := by
  unfold Task.costRegion
  simp_rw [canonicalReduction_achievableAt_eq task h₁ h₂ h₃]

theorem canonicalReduction_fully_used :
    used₁ (canonicalReduction task h₁ h₂ h₃) = ⊤ ∧
    used₂ (canonicalReduction task h₁ h₂ h₃) = ⊤ ∧
    used₃ (canonicalReduction task h₁ h₂ h₃) = ⊤ := by
  obtain ⟨h₁',h₂',h₃'⟩ := (selectedTrimData task h₁ h₂ h₃).activeRowReduction_used
  change used₁ (selectedTrimData task h₁ h₂ h₃).activeRowReduction = _ ∧
    used₂ (selectedTrimData task h₁ h₂ h₃).activeRowReduction = _ ∧
    used₃ (selectedTrimData task h₁ h₂ h₃).activeRowReduction = _
  rw [h₁',h₂',h₃']
  exact privateTrim_fully_used task
omit h₁ h₂ h₃

/-- Canonical private and tripod coefficient embeddings. -/
def embedPrivate₁ : P₁ →ₗ[K] Ambient P₁ P₂ P₃ D :=
  (side₁ (K := K)).comp (LinearMap.inl K P₁ D)
def embedPrivate₂ : P₂ →ₗ[K] Ambient P₁ P₂ P₃ D :=
  (side₂ (K := K)).comp (LinearMap.inl K P₂ D)
def embedPrivate₃ : P₃ →ₗ[K] Ambient P₁ P₂ P₃ D :=
  (side₃ (K := K)).comp (LinearMap.inl K P₃ D)
def embedV : D →ₗ[K] Ambient P₁ P₂ P₃ D :=
  (side₁ (K := K)).comp (LinearMap.inr K P₁ D)
def embedR : D →ₗ[K] Ambient P₁ P₂ P₃ D :=
  (side₂ (K := K)).comp (LinearMap.inr K P₂ D)

/-- The three contributions to the signed private-incidence map. -/
def incidence₁ : (P₂ × P₃) →ₗ[K] ((P₁ × P₂) × P₃) where
  toFun x := ((0,x.1),x.2)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def incidence₂ : (P₁ × P₃) →ₗ[K] ((P₁ × P₂) × P₃) where
  toFun x := ((x.1,0),-x.2)
  map_add' _ _ := by simp [add_comm]
  map_smul' _ _ := by simp

def incidence₃ : (P₁ × P₂) →ₗ[K] ((P₁ × P₂) × P₃) := LinearMap.inl K (P₁ × P₂) P₃

namespace DemandData
variable {task} (g : DemandData task)
/-- Actual corrected graph maps, with values in the retained rows. -/
noncomputable def correctedGraph₁ : privateDomain₁ task →ₗ[K] g.activeRows :=
  (retainedProjection g.activeRows).comp
    ((g.φ₁ - g.emptyCorrection.comp incidence₁).comp (privateDomain₁ task).subtype)
noncomputable def correctedGraph₂ : privateDomain₂ task →ₗ[K] g.activeRows :=
  (retainedProjection g.activeRows).comp
    ((g.φ₂ - g.emptyCorrection.comp incidence₂).comp (privateDomain₂ task).subtype)
noncomputable def correctedGraph₃ : privateDomain₃ task →ₗ[K] g.activeRows :=
  (retainedProjection g.activeRows).comp
    ((g.φ₃ - g.emptyCorrection.comp incidence₃).comp (privateDomain₃ task).subtype)

theorem correctedGraph₁_coe (x : privateDomain₁ task) :
    (g.correctedGraph₁ x : D) = g.φ₁ x.val - g.emptyCorrection ((0,x.val.1),x.val.2) :=
  congrArg Subtype.val (retainedProjection_self g.activeRows
    ⟨_,g.emptyCorrection_spec.1 x⟩)
theorem correctedGraph₂_coe (x : privateDomain₂ task) :
    (g.correctedGraph₂ x : D) = g.φ₂ x.val - g.emptyCorrection ((x.val.1,0),-x.val.2) :=
  congrArg Subtype.val (retainedProjection_self g.activeRows
    ⟨_,g.emptyCorrection_spec.2.1 x⟩)
theorem correctedGraph₃_coe (x : privateDomain₃ task) :
    (g.correctedGraph₃ x : D) = g.φ₃ x.val - g.emptyCorrection ((x.val.1,x.val.2),0) :=
  congrArg Subtype.val (retainedProjection_self g.activeRows
    ⟨_,g.emptyCorrection_spec.2.2 x⟩)

/-- Private cancellation leaves the genuine zero-private relation rows
unchanged, including their actual representatives rather than just their rank. -/
theorem correctedGraphs_on_kernel (x : Relations (task := task))
    (hx : x ∈ LinearMap.ker (incidence (task := task))) :
    (g.correctedGraph₁ x.1.1 : D) + g.correctedGraph₂ x.1.2 + g.correctedGraph₃ x.2 =
      g.relationRows x := by
  rw [g.correctedGraph₁_coe,g.correctedGraph₂_coe,g.correctedGraph₃_coe]
  have hf : g.emptyCorrection ((0,x.1.1.val.1),x.1.1.val.2) +
      g.emptyCorrection ((x.1.2.val.1,0),-x.1.2.val.2) +
      g.emptyCorrection ((x.2.val.1,x.2.val.2),0) = 0 := by
    rw [← map_add,← map_add]
    have he : ((0,x.1.1.val.1),x.1.1.val.2) +
        ((x.1.2.val.1,0),-x.1.2.val.2) + ((x.2.val.1,x.2.val.2),0) = incidence x := by
      ext <;> simp [incidence,sub_eq_add_neg]
    rw [he,show incidence x = 0 from hx,map_zero]
  change (g.φ₁ x.1.1.val - _) + (g.φ₂ x.1.2.val - _) + (g.φ₃ x.2.val - _) =
    g.φ₁ x.1.1.val + g.φ₂ x.1.2.val + g.φ₃ x.2.val
  have he : (g.φ₁ x.1.1.val - g.emptyCorrection ((0,x.1.1.val.1),x.1.1.val.2)) +
      (g.φ₂ x.1.2.val - g.emptyCorrection ((x.1.2.val.1,0),-x.1.2.val.2)) +
      (g.φ₃ x.2.val - g.emptyCorrection ((x.2.val.1,x.2.val.2),0)) =
      (g.φ₁ x.1.1.val + g.φ₂ x.1.2.val + g.φ₃ x.2.val) -
        (g.emptyCorrection ((0,x.1.1.val.1),x.1.1.val.2) +
          g.emptyCorrection ((x.1.2.val.1,0),-x.1.2.val.2) +
          g.emptyCorrection ((x.2.val.1,x.2.val.2),0)) := by abel
  rw [he,hf,sub_zero]

/-- Every retained row is generated by pure rows and an actual signed
zero-private relation after correction. This is the activity hypothesis needed
by the signal-intersection converse, now obtained by construction. -/
theorem activeRows_generated (d : g.activeRows) :
    ∃ (d₁ : g.activeRows), d₁.val ∈ pureRows₁ task ∧
    ∃ (d₂ : g.activeRows), d₂.val ∈ pureRows₂ task ∧
    ∃ (d₃ : g.activeRows), d₃.val ∈ pureRows₃ task ∧
    ∃ x : Relations (task := task),
      x.1.2.val.1 + x.2.val.1 = 0 ∧
      x.1.1.val.1 + x.2.val.2 = 0 ∧
      x.1.1.val.2 - x.1.2.val.2 = 0 ∧
      d = d₁ + d₂ + d₃ +
        (g.correctedGraph₁ x.1.1 + g.correctedGraph₂ x.1.2 + g.correctedGraph₃ x.2) := by
  obtain ⟨s,hs,m,hm,hsm⟩ := Submodule.mem_sup.mp d.property
  obtain ⟨s₁₂,hs₁₂,s₃,hs₃,hs⟩ := Submodule.mem_sup.mp hs
  obtain ⟨s₁,hs₁,s₂,hs₂,hs₁₂⟩ := Submodule.mem_sup.mp hs₁₂
  obtain ⟨x,hx,rfl⟩ := hm
  have h₁r : s₁ ∈ g.activeRows :=
    Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left hs₁))
  have h₂r : s₂ ∈ g.activeRows :=
    Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right hs₂))
  have h₃r : s₃ ∈ g.activeRows := Submodule.mem_sup_left (Submodule.mem_sup_right hs₃)
  refine ⟨⟨s₁,h₁r⟩,hs₁,⟨s₂,h₂r⟩,hs₂,⟨s₃,h₃r⟩,hs₃,x,?_,?_,?_,?_⟩
  · exact congrArg (fun p : (P₁ × P₂) × P₃ => p.1.1) hx
  · exact congrArg (fun p : (P₁ × P₂) × P₃ => p.1.2) hx
  · exact congrArg (fun p : (P₁ × P₂) × P₃ => p.2) hx
  · apply Subtype.ext
    change (d : D) = s₁ + s₂ + s₃ +
      ((g.correctedGraph₁ x.1.1 : D) + g.correctedGraph₂ x.1.2 + g.correctedGraph₃ x.2)
    rw [g.correctedGraphs_on_kernel x hx,hs₁₂,hs,hsm]
end DemandData

/-- A locally normalized quotient representative of a signal is a signal. -/
theorem quotientLift_mem {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (A U : Submodule K V) (hAU : A ≤ U)
    (q : V →ₗ[K] W) (s : W →ₗ[K] V) (hlocal : ∀ x, x - s (q x) ∈ A)
    (x : V) (hx : x ∈ U) : s (q x) ∈ U := by
  simpa only [sub_sub_cancel] using U.sub_mem hx (hAU (hlocal x))

namespace DemandData
variable {task} (g : DemandData task)
/-- The actual coefficient transport through correction and row deletion. -/
noncomputable def transport : Ambient P₁ P₂ P₃ D →ₗ[K] Ambient P₁ P₂ P₃ g.activeRows :=
  (rowProjection g.activeRows).comp (privateGaugeShear g.emptyCorrection).toLinearMap

theorem transport_mem (i : Three) (x : Ambient P₁ P₂ P₃ D) (hx : x ∈ task.U i) :
    g.transport x ∈ g.activeRowReduction.U i :=
  ⟨privateGaugeShear g.emptyCorrection x,⟨x,hx,rfl⟩,rfl⟩

theorem reduced_pure₁ (d : g.activeRows) (hd : d.val ∈ pureRows₁ task) :
    embedR (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d ∈ g.activeRowReduction.U 0 := by
  have hz : embedR (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d.val ∈ task.U 0 := by
    apply (g.mem₁ _).mpr
    simpa [embedR,side₂] using And.intro (privateDomain₁ task).zero_mem hd
  have ht := g.transport_mem 0 _ hz
  convert ht using 1;
    simp [transport,embedR,side₂,privateGaugeShear,squareZeroShear,privateGauge,rowProjection]

theorem reduced_pure₂ (d : g.activeRows) (hd : d.val ∈ pureRows₂ task) :
    embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d ∈ g.activeRowReduction.U 1 := by
  have hz : embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d.val ∈ task.U 1 := by
    apply (g.mem₂ _).mpr
    simpa [embedV,side₁] using And.intro (privateDomain₂ task).zero_mem hd
  have ht := g.transport_mem 1 _ hz
  convert ht using 1;
    simp [transport,embedV,side₁,privateGaugeShear,squareZeroShear,privateGauge,rowProjection]

theorem reduced_pure₃ (d : g.activeRows) (hd : d.val ∈ pureRows₃ task) :
    embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d ∈ g.activeRowReduction.U 2 := by
  have hz : embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d.val ∈ task.U 2 := by
    apply (g.mem₃ _).mpr
    simpa [embedV,side₁] using And.intro (privateDomain₃ task).zero_mem hd
  have ht := g.transport_mem 2 _ hz
  convert ht using 1;
    simp [transport,embedV,side₁,privateGaugeShear,squareZeroShear,privateGauge,rowProjection]

include h₁ h₂ h₃
theorem reduced_graph₁ (x : privateDomain₁ task) :
    embedPrivate₂ (K := K) x.val.1 + embedPrivate₃ (K := K) x.val.2 +
      embedR (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (g.correctedGraph₁ x) ∈ g.activeRowReduction.U 0 := by
  let z := demandLift₁ (K := K) (P₁ := P₁) (x.val,g.φ₁ x.val)
  have hz : z ∈ task.U 0 := by
    apply (g.mem₁ _).mpr
    exact ⟨x.property,by simp [z,demandLift₁]⟩
  obtain ⟨hs₁,hs₂,hs₃⟩ := g.activeRowReduction_sides h₁ h₂ h₃
  have hl := quotientLift_mem _ _ (g.activeRowReduction.side_le_signal 0)
    (demandQuotient₁ (K := K)) demandLift₁
    (by simpa only [hs₁] using (demandLift_remainder (K := K) (P₁ := P₁) (P₂ := P₂)
      (P₃ := P₃) (D := g.activeRows)).1)
    (g.transport z) (g.transport_mem 0 z hz)
  convert hl using 1; ext <;>
    simp [embedPrivate₂,embedPrivate₃,embedR,side₂,side₃,transport,z,
      demandLift₁,demandQuotient₁,privateGaugeShear,squareZeroShear,privateGauge,rowProjection,
      correctedGraph₁,incidence₁]

theorem reduced_graph₂ (x : privateDomain₂ task) :
    embedPrivate₁ (K := K) x.val.1 + embedPrivate₃ (K := K) x.val.2 +
      embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (g.correctedGraph₂ x) ∈ g.activeRowReduction.U 1 := by
  let z := demandLift₂ (K := K) (P₂ := P₂) (x.val,g.φ₂ x.val)
  have hz : z ∈ task.U 1 := by
    apply (g.mem₂ _).mpr
    exact ⟨x.property,by simp [z,demandLift₂]⟩
  obtain ⟨hs₁,hs₂,hs₃⟩ := g.activeRowReduction_sides h₁ h₂ h₃
  have hl := quotientLift_mem _ _ (g.activeRowReduction.side_le_signal 1)
    (demandQuotient₂ (K := K)) demandLift₂
    (by simpa only [hs₂] using (demandLift_remainder (K := K) (P₁ := P₁) (P₂ := P₂)
      (P₃ := P₃) (D := g.activeRows)).2.1)
    (g.transport z) (g.transport_mem 1 z hz)
  convert hl using 1; ext <;>
    simp [embedPrivate₁,embedPrivate₃,embedV,side₁,side₃,transport,z,
      demandLift₂,demandQuotient₂,privateGaugeShear,squareZeroShear,privateGauge,rowProjection,
      correctedGraph₂,incidence₂]

theorem reduced_graph₃ (x : privateDomain₃ task) :
    embedPrivate₁ (K := K) x.val.1 + embedPrivate₂ (K := K) x.val.2 +
      embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (g.correctedGraph₃ x) ∈ g.activeRowReduction.U 2 := by
  let z := demandLift₃ (K := K) (P₃ := P₃) (x.val,g.φ₃ x.val)
  have hz : z ∈ task.U 2 := by
    apply (g.mem₃ _).mpr
    exact ⟨x.property,by simp [z,demandLift₃]⟩
  obtain ⟨hs₁,hs₂,hs₃⟩ := g.activeRowReduction_sides h₁ h₂ h₃
  have hl := quotientLift_mem _ _ (g.activeRowReduction.side_le_signal 2)
    (demandQuotient₃ (K := K)) demandLift₃
    (by simpa only [hs₃] using (demandLift_remainder (K := K) (P₁ := P₁) (P₂ := P₂)
      (P₃ := P₃) (D := g.activeRows)).2.2)
    (g.transport z) (g.transport_mem 2 z hz)
  convert hl using 1; ext <;>
    simp [embedPrivate₁,embedPrivate₂,embedV,side₁,side₂,transport,z,
      demandLift₃,demandQuotient₃,privateGaugeShear,squareZeroShear,privateGauge,rowProjection,
      correctedGraph₃,incidence₃]
  have he : g.emptyCorrection (x.val,0) =
      g.emptyCorrection ((x.val.1,0),0) + g.emptyCorrection ((0,x.val.2),0) := by
    rw [← map_add]
    congr 1
    ext <;> simp
  rw [he,map_add,Submodule.coe_add]
  abel
omit h₁ h₂ h₃
end DemandData

namespace DemandData
variable {task} (g : DemandData task)

def relationPart₁ : Relations (task := task) →ₗ[K] privateDomain₁ task :=
  (LinearMap.fst K (privateDomain₁ task) (privateDomain₂ task)).comp
    (LinearMap.fst K (privateDomain₁ task × privateDomain₂ task) (privateDomain₃ task))
def relationPart₂ : Relations (task := task) →ₗ[K] privateDomain₂ task :=
  (LinearMap.snd K (privateDomain₁ task) (privateDomain₂ task)).comp
    (LinearMap.fst K (privateDomain₁ task × privateDomain₂ task) (privateDomain₃ task))
def relationPart₃ : Relations (task := task) →ₗ[K] privateDomain₃ task :=
  LinearMap.snd K (privateDomain₁ task × privateDomain₂ task) (privateDomain₃ task)

/-- The fully operational signal-intersection data of the constructed
reduction. Its active-row assertion is proved from the actual signed relation
map, not supplied by a normal-form or converse hypothesis. -/
noncomputable def signalBridge : SignalBridge.Data (K := K)
    (F := Ambient P₁ P₂ P₃ g.activeRows) (T := g.activeRows)
    (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (L := Relations (task := task)) := by
  have hs₁ := (g.activeRowReduction_sides h₁ h₂ h₃).1
  have hs₂ := (g.activeRowReduction_sides h₁ h₂ h₃).2.1
  have hs₃ := (g.activeRowReduction_sides h₁ h₂ h₃).2.2
  refine {
    U₁ := g.activeRowReduction.U 0
    U₂ := g.activeRowReduction.U 1
    U₃ := g.activeRowReduction.U 2
    p₁ := embedPrivate₁
    p₂ := embedPrivate₂
    p₃ := embedPrivate₃
    v := embedV
    r := embedR
    D₁ := (pureRows₁ task).comap g.activeRows.subtype
    D₂ := (pureRows₂ task).comap g.activeRows.subtype
    D₃ := (pureRows₃ task).comap g.activeRows.subtype
    a₁₂ := (LinearMap.fst K P₂ P₃).comp ((privateDomain₁ task).subtype.comp relationPart₁)
    a₁₃ := (LinearMap.snd K P₂ P₃).comp ((privateDomain₁ task).subtype.comp relationPart₁)
    a₂₁ := (LinearMap.fst K P₁ P₃).comp ((privateDomain₂ task).subtype.comp relationPart₂)
    a₂₃ := (LinearMap.snd K P₁ P₃).comp ((privateDomain₂ task).subtype.comp relationPart₂)
    a₃₁ := (LinearMap.fst K P₁ P₂).comp ((privateDomain₃ task).subtype.comp relationPart₃)
    a₃₂ := (LinearMap.snd K P₁ P₂).comp ((privateDomain₃ task).subtype.comp relationPart₃)
    φ₁ := g.correctedGraph₁.comp relationPart₁
    φ₂ := g.correctedGraph₂.comp relationPart₂
    φ₃ := g.correctedGraph₃.comp relationPart₃
    side₁ := ?_
    side₂ := ?_
    side₃ := ?_
    private₁ := ?_
    private₂ := ?_
    private₃ := ?_
    pure₁ := g.reduced_pure₁
    pure₂ := g.reduced_pure₂
    pure₃ := g.reduced_pure₃
    demand₁ := ?_
    demand₂ := ?_
    demand₃ := ?_
    active := g.activeRows_generated }
  · intro d
    apply g.activeRowReduction.side_le_signal 0
    rw [hs₁]
    exact ⟨(0,d),rfl⟩
  · intro d
    apply g.activeRowReduction.side_le_signal 1
    rw [hs₂]
    exact ⟨(0,d),rfl⟩
  · intro d
    apply g.activeRowReduction.side_le_signal 2
    rw [hs₃]
    exact ⟨(0,d),by ext <;> simp [embedR,embedV,side₁,side₂,side₃]⟩
  · intro p
    apply g.activeRowReduction.side_le_signal 0
    rw [hs₁]
    exact ⟨(p,0),rfl⟩
  · intro p
    apply g.activeRowReduction.side_le_signal 1
    rw [hs₂]
    exact ⟨(p,0),rfl⟩
  · intro p
    apply g.activeRowReduction.side_le_signal 2
    rw [hs₃]
    exact ⟨(p,0),rfl⟩
  · intro x
    exact g.reduced_graph₁ h₁ h₂ h₃ x.1.1
  · intro x
    exact g.reduced_graph₂ h₁ h₂ h₃ x.1.2
  · intro x
    exact g.reduced_graph₃ h₁ h₂ h₃ x.2

include h₁ h₂ h₃
/-- The key residual signal bridge is a theorem for the constructed task. -/
theorem activeRowReduction_tripod_bridge :
    LinearMap.range (embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := g.activeRows)) ⊔
      LinearMap.range embedR ≤ g.activeRowReduction.U 2 ⊔
        (g.activeRowReduction.U 0 ⊓ g.activeRowReduction.U 1) :=
  SignalBridge.tripod_le_signal_sup_inter (g.signalBridge h₁ h₂ h₃)
omit h₁ h₂ h₃
end DemandData
end ResidualTaskAssembly
end UploadBroadcast

namespace UploadBroadcast.ResidualTaskAssembly
variable {K P₁ P₂ P₃ D : Type*} [Field K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]
  (task : Task K (ResidualUpload.Ambient P₁ P₂ P₃ D))
  (h₁ : task.A 0 = ResidualUpload.A₁ K P₁ P₂ P₃ D)
  (h₂ : task.A 1 = ResidualUpload.A₂ K P₁ P₂ P₃ D)
  (h₃ : task.A 2 = ResidualUpload.A₃ K P₁ P₂ P₃ D)

theorem canonicalReduction_sides :
    (canonicalReduction task h₁ h₂ h₃).A 0 =
      ResidualUpload.A₁ K (used₁ task) (used₂ task) (used₃ task) (selectedTrimData task h₁ h₂ h₃).activeRows ∧
    (canonicalReduction task h₁ h₂ h₃).A 1 =
      ResidualUpload.A₂ K (used₁ task) (used₂ task) (used₃ task) (selectedTrimData task h₁ h₂ h₃).activeRows ∧
    (canonicalReduction task h₁ h₂ h₃).A 2 =
      ResidualUpload.A₃ K (used₁ task) (used₂ task) (used₃ task) (selectedTrimData task h₁ h₂ h₃).activeRows :=
  (selectedTrimData task h₁ h₂ h₃).activeRowReduction_sides
    (privateTrim_sides task h₁ h₂ h₃).1
    (privateTrim_sides task h₁ h₂ h₃).2.1
    (privateTrim_sides task h₁ h₂ h₃).2.2

/-- Ready-to-use converse data for the entirely constructed canonical reduction. -/
noncomputable def canonicalReductionBridge :=
  (selectedTrimData task h₁ h₂ h₃).signalBridge
    (privateTrim_sides task h₁ h₂ h₃).1
    (privateTrim_sides task h₁ h₂ h₃).2.1
    (privateTrim_sides task h₁ h₂ h₃).2.2
end UploadBroadcast.ResidualTaskAssembly
