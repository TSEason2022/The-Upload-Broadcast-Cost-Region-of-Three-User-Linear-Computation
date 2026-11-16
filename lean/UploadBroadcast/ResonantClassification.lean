import UploadBroadcast.ResonantEndomorphisms
import UploadBroadcast.MarkedNilpotent

/-!
# Necessary conditions on the resonant graph form

These results concern configurations already in the displayed graph coordinates.
They do not assert that every indecomposable flag configuration can be put in
those coordinates. In particular they do not supply real-root uniqueness.
-/
namespace UploadBroadcast.ResonantClassification
open ResonantEndomorphisms TaskDecomposition
variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

/-- Construct an endomorphism from the manuscript's block parameters. -/
def blockEnd (α : K) (B : X →ₗ[K] X) (g : X →ₗ[K] K) :
    Ambient K X →ₗ[K] Ambient K X where
  toFun p := (B p.1, B p.2.1, B p.2.2.1,
    g p.1 - g p.2.2.1 + α * p.2.2.2.1,
    -g p.2.1 + g p.2.2.1 + α * p.2.2.2.2)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' a p := by ext <;> simp [smul_add, smul_sub] <;> ring

/-- The commutant equations are sufficient as well as necessary. -/
theorem blockEnd_stable (J : X →ₗ[K] X) (h : X →ₗ[K] K)
    (α : K) (B : X →ₗ[K] X) (g : X →ₗ[K] K)
    (hc : ∀ x, B (J x) = J (B x))
    (hh : ∀ x, h (B x) - α * h x = -g (J x)) :
    Stable (spaces K X J h) (blockEnd α B g) := by
  intro i p hp
  fin_cases i
  · change p.2.1 = 0 ∧ p.2.2.1 = 0 ∧ p.2.2.2.2 = 0 at hp
    change B p.2.1 = 0 ∧ B p.2.2.1 = 0 ∧ -g p.2.1 + g p.2.2.1 + α * p.2.2.2.2 = 0
    simp [hp.1, hp.2.1, hp.2.2]
  · change p.1 = 0 ∧ p.2.2.1 = 0 ∧ p.2.2.2.1 = 0 at hp
    change B p.1 = 0 ∧ B p.2.2.1 = 0 ∧ g p.1 - g p.2.2.1 + α * p.2.2.2.1 = 0
    simp [hp.1, hp.2.1, hp.2.2]
  · change p.1 = 0 ∧ p.2.1 = 0 ∧ p.2.2.2.1 + p.2.2.2.2 = 0 at hp
    change B p.1 = 0 ∧ B p.2.1 = 0 ∧
      (g p.1 - g p.2.2.1 + α * p.2.2.2.1) +
      (-g p.2.1 + g p.2.2.1 + α * p.2.2.2.2) = 0
    simp only [hp.1, hp.2.1, map_zero, zero_sub, neg_zero, zero_add]
    exact ⟨True.intro, True.intro, by linear_combination α * hp.2.2⟩
  · change p.2.1 = p.2.2.1 ∧ p.2.2.2.2 = 0 at hp
    change B p.2.1 = B p.2.2.1 ∧ -g p.2.1 + g p.2.2.1 + α * p.2.2.2.2 = 0
    simp [hp.1, hp.2]
  · change p.1 = p.2.2.1 ∧ p.2.2.2.1 = 0 at hp
    change B p.1 = B p.2.2.1 ∧ g p.1 - g p.2.2.1 + α * p.2.2.2.1 = 0
    simp [hp.1, hp.2]
  · change p.2.1 = p.1 + J p.1 ∧ p.2.2.2.1 + p.2.2.2.2 = h p.1 at hp
    change B p.2.1 = B p.1 + J (B p.1) ∧
      (g p.1 - g p.2.2.1 + α * p.2.2.2.1) +
      (-g p.2.1 + g p.2.2.1 + α * p.2.2.2.2) = h (B p.1)
    constructor
    · rw [hp.1, map_add, hc]
    · rw [hp.1, map_add]
      linear_combination α * hp.2 - hh p.1

/-- Idempotence of the two-by-two marked operator gives idempotence of the
corresponding six-space endomorphism. -/
theorem blockEnd_idempotent (α : K) (B : X →ₗ[K] X) (g : X →ₗ[K] K)
    (hα : α * α = α) (hB : ∀ x, B (B x) = B x)
    (hg : ∀ x, g (B x) + α * g x = g x) :
    ∀ p, blockEnd α B g (blockEnd α B g p) = blockEnd α B g p := by
  intro p
  apply Prod.ext (hB p.1)
  apply Prod.ext (hB p.2.1)
  apply Prod.ext (hB p.2.2.1)
  apply Prod.ext
  · change g (B p.1) - g (B p.2.2.1) + α *
      (g p.1 - g p.2.2.1 + α * p.2.2.2.1) =
      g p.1 - g p.2.2.1 + α * p.2.2.2.1
    linear_combination hg p.1 - hg p.2.2.1 + hα * p.2.2.2.1
  · change -g (B p.2.1) + g (B p.2.2.1) + α *
      (-g p.2.1 + g p.2.2.1 + α * p.2.2.2.2) =
      -g p.2.1 + g p.2.2.1 + α * p.2.2.2.2
    linear_combination -hg p.2.1 + hg p.2.2.1 + hα * p.2.2.2.2

/-- Indecomposability excludes every nontrivial marked-operator projection. -/
theorem graph_projection_parameters_trivial
    (J : X →ₗ[K] X) (h : X →ₗ[K] K)
    (hi : Indecomposable (spaces K X J h) ⊤)
    (α : K) (B : X →ₗ[K] X) (g : X →ₗ[K] K)
    (hc : ∀ x, B (J x) = J (B x))
    (hh : ∀ x, h (B x) - α * h x = -g (J x))
    (hα : α * α = α) (hB : ∀ x, B (B x) = B x)
    (hg : ∀ x, g (B x) + α * g x = g x) :
    (α = 0 ∧ B = 0 ∧ g = 0) ∨ (α = 1 ∧ B = LinearMap.id ∧ g = 0) := by
  obtain hz | ho := hi.projection_eq_zero_or_id (blockEnd α B g)
    (blockEnd_stable J h α B g hc hh) (blockEnd_idempotent α B g hα hB hg)
  · left
    have ha := congrArg (fun f : Module.End K (Ambient K X) =>
      (f (scalarV K X 1)).2.2.2.1) hz
    refine ⟨by simpa [blockEnd, scalarV] using ha, ?_, ?_⟩
    · ext x
      exact congrArg (fun f : Module.End K (Ambient K X) => (f (E₁ K X x)).1) hz
    · ext x
      have he := congrArg (fun f : Module.End K (Ambient K X) => (f (E₁ K X x)).2.2.2.1) hz
      simpa [blockEnd, E₁] using he
  · right
    have ha := congrArg (fun f : Module.End K (Ambient K X) =>
      (f (scalarV K X 1)).2.2.2.1) ho
    refine ⟨by simpa [blockEnd, scalarV] using ha, ?_, ?_⟩
    · ext x
      exact congrArg (fun f : Module.End K (Ambient K X) => (f (E₁ K X x)).1) ho
    · ext x
      have he := congrArg (fun f : Module.End K (Ambient K X) => (f (E₁ K X x)).2.2.2.1) ho
      simpa [blockEnd, E₁] using he

/-- The auxiliary nilpotent operator, with its distinguished scalar kernel line. -/
def augmentedOperator (J : X →ₗ[K] X) (h : X →ₗ[K] K) :
    (X × K) →ₗ[K] (X × K) where
  toFun p := (J p.1, h p.1)
  map_add' p q := by simp
  map_smul' a p := by simp

/-- Endomorphisms preserving the distinguished line have this block form. -/
def markedEnd (α : K) (B : X →ₗ[K] X) (g : X →ₗ[K] K) :
    (X × K) →ₗ[K] (X × K) where
  toFun p := (B p.1, -g p.1 + α * p.2)
  map_add' p q := by ext <;> simp; ring
  map_smul' a p := by ext <;> simp; ring

theorem markedEnd_commutes_iff (J : X →ₗ[K] X) (h : X →ₗ[K] K)
    (α : K) (B : X →ₗ[K] X) (g : X →ₗ[K] K) :
    Commute (markedEnd α B g) (augmentedOperator J h) ↔
    (∀ x, B (J x) = J (B x)) ∧ (∀ x, h (B x) - α * h x = -g (J x)) := by
  constructor
  · intro he
    have hh (x : X) := congrArg (fun f : Module.End K (X × K) => f (x,0)) he.eq
    constructor
    · intro x; exact congrArg Prod.fst (hh x)
    · intro x
      have hx := congrArg Prod.snd (hh x)
      change -g (J x) + α * h x = h (B x) at hx
      linear_combination -hx
  · rintro ⟨hc, hh⟩
    change markedEnd α B g * augmentedOperator J h =
      augmentedOperator J h * markedEnd α B g
    apply LinearMap.ext
    intro p
    apply Prod.ext
    · exact hc p.1
    · change -g (J p.1) + α * h p.1 = h (B p.1)
      linear_combination -hh p.1

/-- Every linear map preserving the marked scalar line admits the indicated
block parameters, without choosing a basis of X. -/
theorem markedEnd_parameters (P : Module.End K (X × K))
    (hl : P (0,1) ∈ Submodule.span K {(0,1)}) :
    ∃ (α : K) (B : X →ₗ[K] X) (g : X →ₗ[K] K), P = markedEnd α B g := by
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp hl
  let B := (LinearMap.fst K X K).comp (P.comp (LinearMap.inl K X K))
  let g := -((LinearMap.snd K X K).comp (P.comp (LinearMap.inl K X K)))
  refine ⟨α, B, g, LinearMap.ext fun p => ?_⟩
  have he : P p = P (p.1,0) + p.2 • P (0,1) := by
    rw [← map_smul, ← map_add]
    congr 1
    simp
  rw [he, ← hα]
  apply Prod.ext
  · simp [markedEnd, B]
  · simp [markedEnd, g, smul_smul, mul_comm]

/-- Actual marked idempotents are trivial when the six graph spaces are
indecomposable. This is the interface to a marked-nilpotent cyclicity theorem. -/
theorem marked_projection_trivial (J : X →ₗ[K] X) (h : X →ₗ[K] K)
    (hi : Indecomposable (spaces K X J h) ⊤)
    (P : Module.End K (X × K))
    (hc : Commute P (augmentedOperator J h))
    (hl : P (0,1) ∈ Submodule.span K {(0,1)})
    (hp : ∀ x, P (P x) = P x) : P = 0 ∨ P = 1 := by
  obtain ⟨α, B, g, rfl⟩ := markedEnd_parameters P hl
  obtain ⟨hc, hh⟩ := (markedEnd_commutes_iff J h α B g).mp hc
  have hα : α * α = α := by
    have he := congrArg Prod.snd (hp (0,1))
    simpa [markedEnd] using he
  have hB (x : X) : B (B x) = B x := congrArg Prod.fst (hp (x,0))
  have hg (x : X) : g (B x) + α * g x = g x := by
    have he := congrArg Prod.snd (hp (x,0))
    change -g (B x) + α * (-g x + α * 0) = -g x + α * 0 at he
    linear_combination -he
  obtain ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ :=
    graph_projection_parameters_trivial J h hi α B g hc hh hα hB hg
  · left; ext p <;> simp [markedEnd]
  · right; ext p <;> simp [markedEnd]

/-- Nilpotence of J lifts to nilpotence of the marked augmented operator. -/
theorem augmentedOperator_nilpotent (J : X →ₗ[K] X) (h : X →ₗ[K] K)
    (hn : IsNilpotent J) : IsNilpotent (augmentedOperator J h) := by
  obtain ⟨n, hn⟩ := hn
  have hf (m : ℕ) (p : X × K) : ((augmentedOperator J h ^ m) p).1 = (J ^ m) p.1 := by
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [pow_succ', Module.End.mul_apply]
      change J (((augmentedOperator J h) ^ m) p).1 = J ((J ^ m) p.1)
      rw [ih]
  refine ⟨n+1, LinearMap.ext fun p => ?_⟩
  rw [pow_succ', Module.End.mul_apply]
  change (J (((augmentedOperator J h)^n) p).1,
    h (((augmentedOperator J h)^n) p).1) = (0,0)
  rw [hf, hn]
  simp

/-- The canonical endomorphism with private block J, zero tripod scalar,
and off-diagonal functional -h. -/
def canonicalEnd (J : X →ₗ[K] X) (h : X →ₗ[K] K) :
    Ambient K X →ₗ[K] Ambient K X where
  toFun p := (J p.1, J p.2.1, J p.2.2.1,
    -h p.1 + h p.2.2.1, h p.2.1 - h p.2.2.1)
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, map_add]; ext <;> simp <;> ring
  map_smul' a p := by ext <;> simp [smul_add, smul_sub] <;> ring

 theorem canonicalEnd_stable (J : X →ₗ[K] X) (h : X →ₗ[K] K) :
    Stable (spaces K X J h) (canonicalEnd J h) := by
  intro i p hp
  fin_cases i
  · change p.2.1 = 0 ∧ p.2.2.1 = 0 ∧ p.2.2.2.2 = 0 at hp
    change J p.2.1 = 0 ∧ J p.2.2.1 = 0 ∧ h p.2.1 - h p.2.2.1 = 0
    simp [hp.1, hp.2.1]
  · change p.1 = 0 ∧ p.2.2.1 = 0 ∧ p.2.2.2.1 = 0 at hp
    change J p.1 = 0 ∧ J p.2.2.1 = 0 ∧ -h p.1 + h p.2.2.1 = 0
    simp [hp.1, hp.2.1]
  · change p.1 = 0 ∧ p.2.1 = 0 ∧ p.2.2.2.1 + p.2.2.2.2 = 0 at hp
    change J p.1 = 0 ∧ J p.2.1 = 0 ∧
      (-h p.1 + h p.2.2.1) + (h p.2.1 - h p.2.2.1) = 0
    simp [hp.1, hp.2.1]
  · change p.2.1 = p.2.2.1 ∧ p.2.2.2.2 = 0 at hp
    change J p.2.1 = J p.2.2.1 ∧ h p.2.1 - h p.2.2.1 = 0
    simp [hp.1]
  · change p.1 = p.2.2.1 ∧ p.2.2.2.1 = 0 at hp
    change J p.1 = J p.2.2.1 ∧ -h p.1 + h p.2.2.1 = 0
    simp [hp.1]
  · change p.2.1 = p.1 + J p.1 ∧ p.2.2.2.1 + p.2.2.2.2 = h p.1 at hp
    change J p.2.1 = J p.1 + J (J p.1) ∧
      (-h p.1 + h p.2.2.1) + (h p.2.1 - h p.2.2.1) = h (J p.1)
    constructor
    · simp [hp.1]
    · rw [hp.1, map_add]; ring

 theorem canonicalEnd_pow_first (J : X →ₗ[K] X) (h : X →ₗ[K] K)
    (n : ℕ) (p : Ambient K X) : ((canonicalEnd J h ^ n) p).1 = (J ^ n) p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply]
    change J (((canonicalEnd J h) ^ n) p).1 = J ((J ^ n) p.1)
    rw [ih]

/-- Over a finite field, indecomposability of a graph configuration forces
its graph operator J to be nilpotent. No normal-form classification is used. -/
theorem nilpotent_of_graph_indecomposable [Finite K] [FiniteDimensional K X]
    (J : X →ₗ[K] X) (h : X →ₗ[K] K)
    (hi : Indecomposable (spaces K X J h) ⊤) : IsNilpotent J := by
  let f : stableEnd (spaces K X J h) := ⟨canonicalEnd J h, canonicalEnd_stable J h⟩
  obtain hn | hu := stableEnd.nilpotent_or_unit hi f
  · obtain ⟨n, hn⟩ := hn
    refine ⟨n, LinearMap.ext fun x => ?_⟩
    have hh := congrArg (fun g : stableEnd (spaces K X J h) =>
      ((g : Module.End K (Ambient K X)) (E₁ K X x)).1) hn
    change ((canonicalEnd J h ^ n) (E₁ K X x)).1 = 0 at hh
    simpa only [canonicalEnd_pow_first, E₁] using hh
  · obtain ⟨u, hu⟩ := hu
    have hz : (f : Module.End K (Ambient K X)) (scalarV K X 1) = 0 := by
      simp [f, canonicalEnd, scalarV]
    have hh : ((↑u⁻¹ : stableEnd (spaces K X J h)) : Module.End K (Ambient K X))
        ((f : Module.End K (Ambient K X)) (scalarV K X 1)) = scalarV K X 1 := by
      rw [← hu]
      exact congrArg (fun g : stableEnd (spaces K X J h) =>
        (g : Module.End K (Ambient K X)) (scalarV K X 1)) (Units.inv_mul u)
    rw [hz, map_zero] at hh
    have bad := congrArg (fun p : Ambient K X => p.2.2.2.1) hh
    exfalso
    simp [scalarV] at bad

/-- A factorization h = g J separates the tripod from the private blocks. -/
def tripodProjection (g : X →ₗ[K] K) : Ambient K X →ₗ[K] Ambient K X where
  toFun p := (0, 0, 0, g p.1 - g p.2.2.1 + p.2.2.2.1,
    -g p.2.1 + g p.2.2.1 + p.2.2.2.2)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' a p := by ext <;> simp [smul_add, smul_sub] <;> ring

theorem tripodProjection_stable (J : X →ₗ[K] X) (g h : X →ₗ[K] K)
    (hh : ∀ x, h x = g (J x)) :
    Stable (spaces K X J h) (tripodProjection g) := by
  intro i p hp
  fin_cases i
  · change p.2.1 = 0 ∧ p.2.2.1 = 0 ∧ p.2.2.2.2 = 0 at hp
    change (0 : X) = 0 ∧ (0 : X) = 0 ∧ -g p.2.1 + g p.2.2.1 + p.2.2.2.2 = 0
    simp [hp.1, hp.2.1, hp.2.2]
  · change p.1 = 0 ∧ p.2.2.1 = 0 ∧ p.2.2.2.1 = 0 at hp
    change (0 : X) = 0 ∧ (0 : X) = 0 ∧ g p.1 - g p.2.2.1 + p.2.2.2.1 = 0
    simp [hp.1, hp.2.1, hp.2.2]
  · change p.1 = 0 ∧ p.2.1 = 0 ∧ p.2.2.2.1 + p.2.2.2.2 = 0 at hp
    change (0 : X) = 0 ∧ (0 : X) = 0 ∧
      (g p.1 - g p.2.2.1 + p.2.2.2.1) +
      (-g p.2.1 + g p.2.2.1 + p.2.2.2.2) = 0
    simp only [hp.1, hp.2.1, map_zero, zero_sub, neg_zero, zero_add]
    exact ⟨True.intro, True.intro, by linear_combination hp.2.2⟩
  · change p.2.1 = p.2.2.1 ∧ p.2.2.2.2 = 0 at hp
    change (0 : X) = 0 ∧ -g p.2.1 + g p.2.2.1 + p.2.2.2.2 = 0
    simp [hp.1, hp.2]
  · change p.1 = p.2.2.1 ∧ p.2.2.2.1 = 0 at hp
    change (0 : X) = 0 ∧ g p.1 - g p.2.2.1 + p.2.2.2.1 = 0
    simp [hp.1, hp.2]
  · change p.2.1 = p.1 + J p.1 ∧ p.2.2.2.1 + p.2.2.2.2 = h p.1 at hp
    change (0 : X) = 0 + J 0 ∧
      (g p.1 - g p.2.2.1 + p.2.2.2.1) +
      (-g p.2.1 + g p.2.2.1 + p.2.2.2.2) = h 0
    constructor
    · simp
    · rw [hp.1, map_add, map_zero]
      have he := hp.2
      rw [hh] at he
      linear_combination he

/-- Kernel containment gives a factorization through J over any field. -/
theorem functional_factors (J : X →ₗ[K] X) (h : X →ₗ[K] K)
    (hh : LinearMap.ker J ≤ LinearMap.ker h) :
    ∃ g : X →ₗ[K] K, ∀ x, h x = g (J x) := by
  let q := (LinearMap.ker J).liftQ h hh
  let l := q.comp J.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := l.exists_extend
  refine ⟨g, fun x => ?_⟩
  have he := LinearMap.congr_fun hg (⟨J x, ⟨x, rfl⟩⟩ : LinearMap.range J)
  simpa [l, q, LinearMap.quotKerEquivRange_symm_apply_image] using he.symm

/-- An indecomposable nonempty graph model necessarily has a nonzero coupling
on ker J. This is weaker than injectivity of the coupling on that kernel. -/
theorem coupling_nonzero_on_kernel [Nontrivial X]
    (J : X →ₗ[K] X) (h : X →ₗ[K] K)
    (hi : Indecomposable (spaces K X J h) ⊤) :
    ∃ x, J x = 0 ∧ h x ≠ 0 := by
  by_contra hn
  have hk : LinearMap.ker J ≤ LinearMap.ker h := by
    intro x hx
    change h x = 0
    by_contra hh
    exact hn ⟨x, hx, hh⟩
  obtain ⟨g, hg⟩ := functional_factors J h hk
  obtain hz | ho := hi.projection_eq_zero_or_id (tripodProjection g)
    (tripodProjection_stable J g h hg)
    (by intro p; simp [tripodProjection])
  · have he := congrArg (fun f : Module.End K (Ambient K X) =>
      (f (scalarV K X 1)).2.2.2.1) hz
    simp [tripodProjection, scalarV] at he
  · obtain ⟨x, hx⟩ := exists_ne (0 : X)
    have he := congrArg (fun f : Module.End K (Ambient K X) => (f (E₁ K X x)).1) ho
    exact hx (by simpa [tripodProjection, E₁] using he.symm)

/-- For an indecomposable graph model, the coupling detects the whole kernel.
This uses the proved marked-nilpotent chain theorem, not Jordan classification. -/
theorem coupling_detects_kernel [Finite K] [FiniteDimensional K X]
    (J : X →ₗ[K] X) (h : X →ₗ[K] K)
    (hi : Indecomposable (spaces K X J h) ⊤) :
    ∀ x, J x = 0 → h x = 0 → x = 0 := by
  have hn := augmentedOperator_nilpotent J h (nilpotent_of_graph_indecomposable J h hi)
  have hl : ((0,1) : X × K) ≠ 0 := by simp
  obtain ⟨_, hk⟩ := MarkedNilpotent.single_chain_and_kernel
    (augmentedOperator J h) hn (0,1) hl (by simp [augmentedOperator])
    (marked_projection_trivial J h hi)
  intro x hJ hh
  have hx : ((x,0) : X × K) ∈ LinearMap.ker (augmentedOperator J h) := by
    change (J x, h x) = (0,0)
    rw [hJ, hh]
  rw [hk] at hx
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
  have he := congrArg Prod.fst ha
  simpa using he.symm

/-- Observability coordinates for a nilpotent operator and a detecting row. -/
def observability (J : X →ₗ[K] X) (h : X →ₗ[K] K) (d : ℕ) :
    X →ₗ[K] (Fin d → K) where
  toFun x i := h ((J ^ i.val) x)
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

theorem observability_injective (J : X →ₗ[K] X) (h : X →ₗ[K] K) (d : ℕ)
    (hn : J ^ d = 0)
    (hd : ∀ x, J x = 0 → h x = 0 → x = 0) :
    Function.Injective (observability J h d) := by
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  have ho (k : ℕ) (hk : k < d) : h ((J^k) x) = 0 :=
    congrFun hx ⟨k, hk⟩
  have hp (k : ℕ) : k ≤ d → (J^(d-k)) x = 0 := by
    induction k with
    | zero => intro _; simp [hn]
    | succ k ih =>
      intro hk
      apply hd
      · rw [← Module.End.mul_apply, ← pow_succ']
        have he : d - (k+1) + 1 = d-k := by omega
        rw [he]
        exact ih (by omega)
      · exact ho _ (by omega)
  simpa using hp d le_rfl

theorem nilpotent_pow_finrank [FiniteDimensional K X]
    (J : X →ₗ[K] X) (hn : IsNilpotent J) : J ^ Module.finrank K X = 0 := by
  obtain ⟨m, hm⟩ := hn
  ext x
  apply Module.End.ker_pow_le_ker_pow_finrank J m
  simp [hm]

/-- The actual detecting-row coordinates are a linear equivalence, not merely
an existence assertion about a Jordan basis. -/
noncomputable def observabilityEquiv [FiniteDimensional K X]
    (J : X →ₗ[K] X) (h : X →ₗ[K] K) (hn : IsNilpotent J)
    (hd : ∀ x, J x = 0 → h x = 0 → x = 0) :
    X ≃ₗ[K] (Fin (Module.finrank K X) → K) :=
  LinearEquiv.ofBijective (observability J h (Module.finrank K X))
    ⟨observability_injective J h _ (nilpotent_pow_finrank J hn) hd,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by simp)).mp (observability_injective J h _ (nilpotent_pow_finrank J hn) hd)⟩

/-- Apply one change of coordinates simultaneously to all private blocks. -/
def privateEquiv {Y : Type*} [AddCommGroup Y] [Module K Y] (e : X ≃ₗ[K] Y) :
    Ambient K X ≃ₗ[K] Ambient K Y :=
  e.prodCongr (e.prodCongr (e.prodCongr (LinearEquiv.refl K (K × K))))

/-- Conjugating J and transporting h gives an actual labeled flag isomorphism. -/
theorem graph_configurationIso_of_conjugacy {Y : Type*} [AddCommGroup Y] [Module K Y]
    (J : X →ₗ[K] X) (h : X →ₗ[K] K) (J' : Y →ₗ[K] Y) (h' : Y →ₗ[K] K)
    (e : X ≃ₗ[K] Y) (heJ : ∀ x, e (J x) = J' (e x))
    (heh : ∀ x, h x = h' (e x)) :
    ConfigurationIso (spaces K X J h) (spaces K Y J' h') := by
  have hf (i : Fin 6) (p : Ambient K X) :
      privateEquiv e p ∈ spaces K Y J' h' i ↔ p ∈ spaces K X J h i := by
    fin_cases i
    · simp [spaces, side₁, privateEquiv]
    · simp [spaces, side₂, privateEquiv]
    · simp [spaces, side₃, privateEquiv]
    · simp [spaces, total₁, privateEquiv]
    · simp [spaces, total₂, privateEquiv]
    · change (e p.2.1 = e p.1 + J' (e p.1) ∧
        p.2.2.2.1 + p.2.2.2.2 = h' (e p.1)) ↔
        (p.2.1 = p.1 + J p.1 ∧ p.2.2.2.1 + p.2.2.2.2 = h p.1)
      rw [← heJ, ← map_add, e.injective.eq_iff, ← heh]
  refine ⟨privateEquiv e, ?_, ?_⟩
  · intro i p hp; exact (hf i p).mpr hp
  · intro i p hp
    apply (hf i ((privateEquiv e).symm p)).mp
    simpa using hp

/-- Dimension-indexed observability coordinates compatible with the source's
Jordan-block convention (whose parameter n means block size n+1). -/
noncomputable def observabilityEquivOfDim [FiniteDimensional K X]
    (J : X →ₗ[K] X) (h : X →ₗ[K] K) (hn : IsNilpotent J)
    (hd : ∀ x, J x = 0 → h x = 0 → x = 0)
    (n : ℕ) (hdim : Module.finrank K X = n+1) : X ≃ₗ[K] JordanResonance.V K n :=
  LinearEquiv.ofBijective (observability J h (n+1))
    ⟨observability_injective J h _ (by simpa [hdim] using nilpotent_pow_finrank J hn) hd,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by simpa using hdim)).mp
        (observability_injective J h _ (by simpa [hdim] using nilpotent_pow_finrank J hn) hd)⟩

theorem observabilityEquivOfDim_conjugates [FiniteDimensional K X]
    (J : X →ₗ[K] X) (h : X →ₗ[K] K) (hn : IsNilpotent J)
    (hd : ∀ x, J x = 0 → h x = 0 → x = 0)
    (n : ℕ) (hdim : Module.finrank K X = n+1) (x : X) :
    observabilityEquivOfDim J h hn hd n hdim (J x) =
      JordanResonance.shift K n (observabilityEquivOfDim J h hn hd n hdim x) := by
  funext i
  change h ((J^i.val) (J x)) =
    if hh : i.val+1 < n+1 then h ((J^(⟨i.val+1,hh⟩ : Fin (n+1)).val) x) else 0
  split_ifs with hh
  · rw [← Module.End.mul_apply, ← pow_succ]
  · have he : i.val+1 = n+1 := by omega
    rw [← Module.End.mul_apply, ← pow_succ, he]
    have hj : J^(n+1) = 0 := by simpa [hdim] using nilpotent_pow_finrank J hn
    rw [hj]; simp

theorem observabilityEquivOfDim_head [FiniteDimensional K X]
    (J : X →ₗ[K] X) (h : X →ₗ[K] K) (hn : IsNilpotent J)
    (hd : ∀ x, J x = 0 → h x = 0 → x = 0)
    (n : ℕ) (hdim : Module.finrank K X = n+1) (x : X) :
    h x = JordanResonance.head K n (observabilityEquivOfDim J h hn hd n hdim x) := by
  rfl

/-- Completeness within graph coordinates: every indecomposable graph model
is isomorphic to the manuscript's standard single-Jordan-block model.
This theorem does not assume or prove that arbitrary flags admit graph coordinates. -/
theorem graph_model_classification [Finite K] [FiniteDimensional K X]
    (J : X →ₗ[K] X) (h : X →ₗ[K] K)
    (hi : Indecomposable (spaces K X J h) ⊤)
    (n : ℕ) (hdim : Module.finrank K X = n+1) :
    ConfigurationIso (spaces K X J h)
      (spaces K (JordanResonance.V K n) (JordanResonance.shift K n) (JordanResonance.head K n)) := by
  let hn := nilpotent_of_graph_indecomposable J h hi
  let hd := coupling_detects_kernel J h hi
  exact graph_configurationIso_of_conjugacy J h _ _ (observabilityEquivOfDim J h hn hd n hdim)
    (observabilityEquivOfDim_conjugates J h hn hd n hdim)
    (observabilityEquivOfDim_head J h hn hd n hdim)

/-- For disjoint sides, the remote projection has no kernel beyond the own
side exactly when the enlarged space misses the remote side. This identifies
the remaining arbitrary-flag transversality target without assuming it. -/
theorem remote_transversality_iff {V : Type*} [AddCommGroup V] [Module K V]
    (A B U : Submodule K V) (hAU : A ≤ U) (hAB : Disjoint A B) :
    U ⊓ (A ⊔ B) = A ↔ U ⊓ B = ⊥ := by
  constructor
  · intro he
    apply eq_bot_iff.mpr
    intro x hx
    have hA : x ∈ A := by
      rw [← he]
      exact ⟨hx.1, Submodule.mem_sup_right hx.2⟩
    exact hAB.le_bot ⟨hA, hx.2⟩
  · intro he
    rw [inf_comm, sup_inf_assoc_of_le B hAU, inf_comm B U, he, sup_bot_eq]

/-- The graph-model criterion is also sufficient over an arbitrary field. -/
theorem graph_indecomposable_of_nilpotent_detecting
    (J : X →ₗ[K] X) (h : X →ₗ[K] K) (hn : IsNilpotent J)
    (hd : ∀ x, J x = 0 → h x = 0 → x = 0) :
    Indecomposable (spaces K X J h) ⊤ := by
  apply indecomposable_of_projection_eq_zero_or_id
  · exact top_ne_bot
  · intro f hf hi
    obtain ⟨m, hm⟩ := hn
    obtain ⟨α, hα⟩ := scalar_plus_nilpotent J h hd m hm f hf
    apply NilpotentFiltration.idempotent_eq_zero_or_one_of_sub_smul_nilpotent
      (a := α) (by apply LinearMap.ext; intro x; exact hi x)
    exact ⟨m+1, hα⟩

/-- Exact characterization of indecomposability within graph coordinates.
The converse is proved here, not postulated as a normal-form hypothesis. -/
theorem graph_indecomposable_iff [Finite K] [FiniteDimensional K X]
    (J : X →ₗ[K] X) (h : X →ₗ[K] K) :
    Indecomposable (spaces K X J h) ⊤ ↔
    IsNilpotent J ∧ (∀ x, J x = 0 → h x = 0 → x = 0) := by
  constructor
  · intro hi
    exact ⟨nilpotent_of_graph_indecomposable J h hi, coupling_detects_kernel J h hi⟩
  · rintro ⟨hn, hd⟩
    exact graph_indecomposable_of_nilpotent_detecting J h hn hd

end UploadBroadcast.ResonantClassification
