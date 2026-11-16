import UploadBroadcast.QuiverRepresentation

/-!
# Actual kernel/cokernel reflection on local stars

These constructions concern linear maps and their commuting squares, not just
integer dimension vectors. The boundary space `W` can be a finite direct sum
of neighbouring vertex spaces. Local inverses require respectively surjectivity
and injectivity; no classification theorem or reflection axiom is assumed.
-/
namespace UploadBroadcast.ReflectionEquivalence

universe u
variable {K W X W' X' W'' X'' : Type u} [Field K]
  [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
  [AddCommGroup W'] [Module K W'] [AddCommGroup X'] [Module K X']
  [AddCommGroup W''] [Module K W''] [AddCommGroup X''] [Module K X'']

/-- At a sink replace the central space by the kernel and reverse the arrows. -/
def sink (f : W →ₗ[K] X) : LinearMap.ker f →ₗ[K] W := (LinearMap.ker f).subtype

/-- At a source replace the central space by the cokernel and reverse the arrows. -/
def source (g : X →ₗ[K] W) : W →ₗ[K] (W ⧸ LinearMap.range g) :=
  (LinearMap.range g).mkQ

theorem sink_injective (f : W →ₗ[K] X) : Function.Injective (sink f) :=
  Subtype.val_injective

theorem source_surjective (g : X →ₗ[K] W) : Function.Surjective (source g) :=
  Submodule.mkQ_surjective _

/-- A commuting square between incoming aggregate maps. -/
@[ext] structure SinkHom (f : W →ₗ[K] X) (f' : W' →ₗ[K] X') where
  boundary : W →ₗ[K] W'
  center : X →ₗ[K] X'
  comm : f'.comp boundary = center.comp f

/-- A commuting square between outgoing aggregate maps. -/
@[ext] structure SourceHom (g : X →ₗ[K] W) (g' : X' →ₗ[K] W') where
  boundary : W →ₗ[K] W'
  center : X →ₗ[K] X'
  comm : g'.comp center = boundary.comp g

namespace SinkHom

def id (f : W →ₗ[K] X) : SinkHom f f := ⟨LinearMap.id, LinearMap.id, by simp⟩
def comp {f : W →ₗ[K] X} {f' : W' →ₗ[K] X'} {f'' : W'' →ₗ[K] X''}
    (b : SinkHom f' f'') (a : SinkHom f f') : SinkHom f f'' where
  boundary := b.boundary.comp a.boundary
  center := b.center.comp a.center
  comm := by rw [← LinearMap.comp_assoc, b.comm, LinearMap.comp_assoc, a.comm,
    ← LinearMap.comp_assoc]

end SinkHom

namespace SourceHom

def id (g : X →ₗ[K] W) : SourceHom g g := ⟨LinearMap.id, LinearMap.id, by simp⟩
def comp {g : X →ₗ[K] W} {g' : X' →ₗ[K] W'} {g'' : X'' →ₗ[K] W''}
    (b : SourceHom g' g'') (a : SourceHom g g') : SourceHom g g'' where
  boundary := b.boundary.comp a.boundary
  center := b.center.comp a.center
  comm := by rw [← LinearMap.comp_assoc, b.comm, LinearMap.comp_assoc, a.comm,
    ← LinearMap.comp_assoc]

end SourceHom

/-- Reflection sends a commuting square to its restriction on kernels. -/
def reflectSinkHom {f : W →ₗ[K] X} {f' : W' →ₗ[K] X'} (a : SinkHom f f') :
    SourceHom (sink f) (sink f') where
  boundary := a.boundary
  center := (a.boundary.comp (sink f)).codRestrict (LinearMap.ker f') (by
    intro x
    change f' (a.boundary x.val) = 0
    have h := LinearMap.congr_fun a.comm x.val
    simpa using h)
  comm := rfl

/-- Reflection sends a commuting square to its induced map on cokernels. -/
def reflectSourceHom {g : X →ₗ[K] W} {g' : X' →ₗ[K] W'} (a : SourceHom g g') :
    SinkHom (source g) (source g') where
  boundary := a.boundary
  center := (LinearMap.range g).mapQ (LinearMap.range g') a.boundary (by
    rintro _ ⟨x, rfl⟩
    exact ⟨a.center x, LinearMap.congr_fun a.comm x⟩)
  comm := by ext x; rfl

@[simp] theorem reflectSinkHom_id (f : W →ₗ[K] X) :
    reflectSinkHom (SinkHom.id f) = SourceHom.id (sink f) := by
  ext x <;> rfl

@[simp] theorem reflectSinkHom_comp {f : W →ₗ[K] X} {f' : W' →ₗ[K] X'}
    {f'' : W'' →ₗ[K] X''} (b : SinkHom f' f'') (a : SinkHom f f') :
    reflectSinkHom (b.comp a) = (reflectSinkHom b).comp (reflectSinkHom a) := by
  ext x <;> rfl

@[simp] theorem reflectSourceHom_id (g : X →ₗ[K] W) :
    reflectSourceHom (SourceHom.id g) = SinkHom.id (source g) := by
  apply SinkHom.ext
  · rfl
  · ext x
    rfl

@[simp] theorem reflectSourceHom_comp {g : X →ₗ[K] W} {g' : X' →ₗ[K] W'}
    {g'' : X'' →ₗ[K] W''} (b : SourceHom g' g'') (a : SourceHom g g') :
    reflectSourceHom (b.comp a) = (reflectSourceHom b).comp (reflectSourceHom a) := by
  apply SinkHom.ext
  · rfl
  · ext x
    rfl

/-- The reflected-then-reflected sink space is the original central space. -/
noncomputable def sinkRecovery (f : W →ₗ[K] X) (hf : Function.Surjective f) :
    (W ⧸ LinearMap.range (sink f)) ≃ₗ[K] X :=
  (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype (LinearMap.ker f))).trans
    (f.quotKerEquivOfSurjective hf)

/-- This is an isomorphism of local stars: it recovers the arrows, not just dimensions. -/
@[simp] theorem sinkRecovery_arrow (f : W →ₗ[K] X) (hf : Function.Surjective f) (w : W) :
    sinkRecovery f hf (source (sink f) w) = f w := rfl

/-- The kernel of the reflected quotient identifies with the original source space. -/
noncomputable def sourceRecovery (g : X →ₗ[K] W) (hg : Function.Injective g) :
    X ≃ₗ[K] LinearMap.ker (source g) :=
  (LinearEquiv.ofInjective g hg).trans
    (LinearEquiv.ofEq _ _ (Submodule.ker_mkQ (LinearMap.range g)).symm)

@[simp] theorem sourceRecovery_arrow (g : X →ₗ[K] W) (hg : Function.Injective g) (x : X) :
    sink (source g) (sourceRecovery g hg x) = g x := rfl

/-- Naturality of the sink recovery on all commuting squares. -/
theorem sinkRecovery_natural {f : W →ₗ[K] X} {f' : W' →ₗ[K] X'}
    (a : SinkHom f f') (hf : Function.Surjective f) (hf' : Function.Surjective f')
    (x : W ⧸ LinearMap.range (sink f)) :
    sinkRecovery f' hf' ((reflectSourceHom (reflectSinkHom a)).center x) =
      a.center (sinkRecovery f hf x) := by
  induction x using Submodule.Quotient.induction_on with
  | H w => exact LinearMap.congr_fun a.comm w

/-- Naturality of the source recovery on all commuting squares. -/
theorem sourceRecovery_natural {g : X →ₗ[K] W} {g' : X' →ₗ[K] W'}
    (a : SourceHom g g') (hg : Function.Injective g) (hg' : Function.Injective g') (x : X) :
    (reflectSinkHom (reflectSourceHom a)).center (sourceRecovery g hg x) =
      sourceRecovery g' hg' (a.center x) := by
  apply Subtype.ext
  exact (LinearMap.congr_fun a.comm x).symm

/-- Descent of a square on reflected kernels to the original surjective maps. -/
noncomputable def unreflectSinkHom {f : W →ₗ[K] X} {f' : W' →ₗ[K] X'}
    (hf : Function.Surjective f) (hf' : Function.Surjective f')
    (a : SourceHom (sink f) (sink f')) : SinkHom f f' where
  boundary := a.boundary
  center := (sinkRecovery f' hf').toLinearMap.comp
    ((reflectSourceHom a).center.comp (sinkRecovery f hf).symm.toLinearMap)
  comm := by
    ext w
    have h : (sinkRecovery f hf).symm (f w) = source (sink f) w :=
      (sinkRecovery f hf).symm_apply_eq.mpr (sinkRecovery_arrow f hf w).symm
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h]
    exact sinkRecovery_arrow f' hf' (a.boundary w)

@[simp] theorem unreflect_reflectSinkHom {f : W →ₗ[K] X} {f' : W' →ₗ[K] X'}
    (hf : Function.Surjective f) (hf' : Function.Surjective f') (a : SinkHom f f') :
    unreflectSinkHom hf hf' (reflectSinkHom a) = a := by
  apply SinkHom.ext
  · rfl
  · apply LinearMap.ext
    intro x
    obtain ⟨w, rfl⟩ := hf x
    exact (LinearMap.congr_fun (unreflectSinkHom hf hf' (reflectSinkHom a)).comm w).symm.trans
      (LinearMap.congr_fun a.comm w)

@[simp] theorem reflect_unreflectSinkHom {f : W →ₗ[K] X} {f' : W' →ₗ[K] X'}
    (hf : Function.Surjective f) (hf' : Function.Surjective f')
    (a : SourceHom (sink f) (sink f')) :
    reflectSinkHom (unreflectSinkHom hf hf' a) = a := by
  apply SourceHom.ext
  · rfl
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (LinearMap.congr_fun a.comm x).symm

/-- Fully faithful local sink reflection: every square lifts uniquely. -/
noncomputable def sinkHomEquiv {f : W →ₗ[K] X} {f' : W' →ₗ[K] X'}
    (hf : Function.Surjective f) (hf' : Function.Surjective f') :
    SinkHom f f' ≃ SourceHom (sink f) (sink f') where
  toFun := reflectSinkHom
  invFun := unreflectSinkHom hf hf'
  left_inv := unreflect_reflectSinkHom hf hf'
  right_inv := reflect_unreflectSinkHom hf hf'

/-- The inverse on squares at injective sources. -/
noncomputable def unreflectSourceHom {g : X →ₗ[K] W} {g' : X' →ₗ[K] W'}
    (hg : Function.Injective g) (hg' : Function.Injective g')
    (a : SinkHom (source g) (source g')) : SourceHom g g' where
  boundary := a.boundary
  center := (sourceRecovery g' hg').symm.toLinearMap.comp
    ((reflectSinkHom a).center.comp (sourceRecovery g hg).toLinearMap)
  comm := by
    ext x
    have h := sourceRecovery_arrow g' hg'
      ((sourceRecovery g' hg').symm ((reflectSinkHom a).center (sourceRecovery g hg x)))
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

@[simp] theorem unreflect_reflectSourceHom {g : X →ₗ[K] W} {g' : X' →ₗ[K] W'}
    (hg : Function.Injective g) (hg' : Function.Injective g') (a : SourceHom g g') :
    unreflectSourceHom hg hg' (reflectSourceHom a) = a := by
  apply SourceHom.ext
  · rfl
  · apply LinearMap.ext
    intro x
    apply hg'
    exact (LinearMap.congr_fun (unreflectSourceHom hg hg' (reflectSourceHom a)).comm x).trans
      (LinearMap.congr_fun a.comm x).symm

@[simp] theorem reflect_unreflectSourceHom {g : X →ₗ[K] W} {g' : X' →ₗ[K] W'}
    (hg : Function.Injective g) (hg' : Function.Injective g')
    (a : SinkHom (source g) (source g')) :
    reflectSourceHom (unreflectSourceHom hg hg' a) = a := by
  apply SinkHom.ext
  · rfl
  · apply LinearMap.ext
    intro x
    obtain ⟨w, rfl⟩ := source_surjective g x
    exact (LinearMap.congr_fun
      (reflectSourceHom (unreflectSourceHom hg hg' a)).comm w).symm.trans
      (LinearMap.congr_fun a.comm w)

/-- Fully faithful local source reflection. -/
noncomputable def sourceHomEquiv {g : X →ₗ[K] W} {g' : X' →ₗ[K] W'}
    (hg : Function.Injective g) (hg' : Function.Injective g') :
    SourceHom g g' ≃ SinkHom (source g) (source g') where
  toFun := reflectSourceHom
  invFun := unreflectSourceHom hg hg'
  left_inv := unreflect_reflectSourceHom hg hg'
  right_inv := reflect_unreflectSourceHom hg hg'

namespace SinkHom

def zero (f : W →ₗ[K] X) (f' : W' →ₗ[K] X') : SinkHom f f' := ⟨0, 0, by simp⟩

end SinkHom

namespace SourceHom

def zero (g : X →ₗ[K] W) (g' : X' →ₗ[K] W') : SourceHom g g' := ⟨0, 0, by simp⟩

end SourceHom

@[simp] theorem reflectSinkHom_zero (f : W →ₗ[K] X) (f' : W' →ₗ[K] X') :
    reflectSinkHom (SinkHom.zero f f') = SourceHom.zero (sink f) (sink f') := by
  ext x <;> rfl

@[simp] theorem reflectSourceHom_zero (g : X →ₗ[K] W) (g' : X' →ₗ[K] W') :
    reflectSourceHom (SourceHom.zero g g') = SinkHom.zero (source g) (source g') := by
  apply SinkHom.ext
  · rfl
  · ext x
    simp [reflectSourceHom, SourceHom.zero, SinkHom.zero]

/-- Triviality of idempotent endomorphisms, with an explicit boundary restriction.
`P` can require that boundary maps are vertexwise and commute with all arrows
away from the reflected vertex. This is not itself a definition of a global
quiver's indecomposability. -/
def SinkIdempotentsTrivial (f : W →ₗ[K] X) (P : (W →ₗ[K] W) → Prop) : Prop :=
  ∀ a : SinkHom f f, P a.boundary → a.comp a = a →
    a = SinkHom.zero f f ∨ a = SinkHom.id f

def SourceIdempotentsTrivial (g : X →ₗ[K] W) (P : (W →ₗ[K] W) → Prop) : Prop :=
  ∀ a : SourceHom g g, P a.boundary → a.comp a = a →
    a = SourceHom.zero g g ∨ a = SourceHom.id g

/-- Reflection preserves the idempotent obstruction to direct-sum decomposition,
including any unchanged restrictions on boundary maps. -/
theorem sink_idempotents_iff (f : W →ₗ[K] X) (hf : Function.Surjective f)
    (P : (W →ₗ[K] W) → Prop) :
    SinkIdempotentsTrivial f P ↔ SourceIdempotentsTrivial (sink f) P := by
  constructor
  · intro h a ha haa
    let b := unreflectSinkHom hf hf a
    have hb : b.comp b = b := by
      apply (sinkHomEquiv hf hf).injective
      change reflectSinkHom (b.comp b) = reflectSinkHom b
      simp only [reflectSinkHom_comp, b, reflect_unreflectSinkHom, haa]
    rcases h b ha hb with hz | hi
    · left
      have := congrArg reflectSinkHom hz
      simpa only [b, reflect_unreflectSinkHom, reflectSinkHom_zero] using this
    · right
      have := congrArg reflectSinkHom hi
      simpa only [b, reflect_unreflectSinkHom, reflectSinkHom_id] using this
  · intro h a ha haa
    have hh : (reflectSinkHom a).comp (reflectSinkHom a) = reflectSinkHom a := by
      rw [← reflectSinkHom_comp, haa]
    rcases h (reflectSinkHom a) ha hh with hz | hi
    · left
      apply (sinkHomEquiv hf hf).injective
      simpa only [sinkHomEquiv, Equiv.coe_fn_mk, reflectSinkHom_zero] using hz
    · right
      apply (sinkHomEquiv hf hf).injective
      simpa only [sinkHomEquiv, Equiv.coe_fn_mk, reflectSinkHom_id] using hi

theorem source_idempotents_iff (g : X →ₗ[K] W) (hg : Function.Injective g)
    (P : (W →ₗ[K] W) → Prop) :
    SourceIdempotentsTrivial g P ↔ SinkIdempotentsTrivial (source g) P := by
  constructor
  · intro h a ha haa
    let b := unreflectSourceHom hg hg a
    have hb : b.comp b = b := by
      apply (sourceHomEquiv hg hg).injective
      change reflectSourceHom (b.comp b) = reflectSourceHom b
      simp only [reflectSourceHom_comp, b, reflect_unreflectSourceHom, haa]
    rcases h b ha hb with hz | hi
    · left
      have := congrArg reflectSourceHom hz
      simpa only [b, reflect_unreflectSourceHom, reflectSourceHom_zero] using this
    · right
      have := congrArg reflectSourceHom hi
      simpa only [b, reflect_unreflectSourceHom, reflectSourceHom_id] using this
  · intro h a ha haa
    have hh : (reflectSourceHom a).comp (reflectSourceHom a) = reflectSourceHom a := by
      rw [← reflectSourceHom_comp, haa]
    rcases h (reflectSourceHom a) ha hh with hz | hi
    · left
      apply (sourceHomEquiv hg hg).injective
      simpa only [sourceHomEquiv, Equiv.coe_fn_mk, reflectSourceHom_zero] using hz
    · right
      apply (sourceHomEquiv hg hg).injective
      simpa only [sourceHomEquiv, Equiv.coe_fn_mk, reflectSourceHom_id] using hi

/-- Reflection preserves an actual two-sided inverse pair of incoming squares. -/
theorem sink_preserves_inverse {f : W →ₗ[K] X} {f' : W' →ₗ[K] X'}
    (a : SinkHom f f') (b : SinkHom f' f)
    (hab : b.comp a = SinkHom.id f) (hba : a.comp b = SinkHom.id f') :
    (reflectSinkHom b).comp (reflectSinkHom a) = SourceHom.id (sink f) ∧
      (reflectSinkHom a).comp (reflectSinkHom b) = SourceHom.id (sink f') := by
  constructor <;> rw [← reflectSinkHom_comp]
  · rw [hab, reflectSinkHom_id]
  · rw [hba, reflectSinkHom_id]

/-- Reflection preserves an actual two-sided inverse pair of outgoing squares. -/
theorem source_preserves_inverse {g : X →ₗ[K] W} {g' : X' →ₗ[K] W'}
    (a : SourceHom g g') (b : SourceHom g' g)
    (hab : b.comp a = SourceHom.id g) (hba : a.comp b = SourceHom.id g') :
    (reflectSourceHom b).comp (reflectSourceHom a) = SinkHom.id (source g) ∧
      (reflectSourceHom a).comp (reflectSourceHom b) = SinkHom.id (source g') := by
  constructor <;> rw [← reflectSourceHom_comp]
  · rw [hab, reflectSourceHom_id]
  · rw [hba, reflectSourceHom_id]

/-- Kernel reflection respects direct sums through an explicit equivalence. -/
def sinkProdEquiv (f : W →ₗ[K] X) (f' : W' →ₗ[K] X') :
    (LinearMap.ker f × LinearMap.ker f') ≃ₗ[K] LinearMap.ker (f.prodMap f') where
  toFun x := ⟨(x.1.val, x.2.val), by
    change (f x.1.val, f' x.2.val) = (0, 0)
    rw [x.1.property, x.2.property]⟩
  invFun x := (⟨x.val.1, congrArg Prod.fst x.property⟩,
    ⟨x.val.2, congrArg Prod.snd x.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem sinkProdEquiv_arrow (f : W →ₗ[K] X) (f' : W' →ₗ[K] X')
    (x : LinearMap.ker f × LinearMap.ker f') :
    sink (f.prodMap f') (sinkProdEquiv f f' x) = (sink f x.1, sink f' x.2) := rfl

theorem range_prodMap_eq (g : X →ₗ[K] W) (g' : X' →ₗ[K] W') :
    LinearMap.range (g.prodMap g') = (LinearMap.range g).prod (LinearMap.range g') := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(a, b), Prod.ext ha hb⟩

/-- Cokernel reflection also commutes with binary direct sums. -/
noncomputable def sourceProdEquiv (g : X →ₗ[K] W) (g' : X' →ₗ[K] W') :
    ((W × W') ⧸ LinearMap.range (g.prodMap g')) ≃ₗ[K]
      ((W ⧸ LinearMap.range g) × (W' ⧸ LinearMap.range g')) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [LinearMap.ker_prodMap, source, source, Submodule.ker_mkQ,
      Submodule.ker_mkQ, range_prodMap_eq])).trans
    (((source g).prodMap (source g')).quotKerEquivOfSurjective (by
      rintro ⟨a, b⟩
      obtain ⟨x, rfl⟩ := source_surjective g a
      obtain ⟨y, rfl⟩ := source_surjective g' b
      exact ⟨(x, y), rfl⟩))

@[simp] theorem sourceProdEquiv_arrow (g : X →ₗ[K] W) (g' : X' →ₗ[K] W') (x : W × W') :
    sourceProdEquiv g g' (source (g.prodMap g') x) = (source g x.1, source g' x.2) := rfl

/-- Dimension reflection follows from the actual kernel map and surjectivity. -/
theorem sink_finrank [FiniteDimensional K W] (f : W →ₗ[K] X)
    (hf : Function.Surjective f) :
    Module.finrank K (LinearMap.ker f) + Module.finrank K X = Module.finrank K W := by
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hf, finrank_top] at h
  exact add_comm _ _ |>.trans h

/-- The source formula follows from the actual cokernel and injectivity. -/
theorem source_finrank [FiniteDimensional K W] (g : X →ₗ[K] W)
    (hg : Function.Injective g) :
    Module.finrank K (W ⧸ LinearMap.range g) + Module.finrank K X = Module.finrank K W := by
  simpa only [LinearMap.finrank_range_of_inj hg] using
    (LinearMap.range g).finrank_quotient_add_finrank

/-- Every vector-space submodule has an actual linear projection. -/
theorem exists_projection (U : Submodule K X) :
    ∃ p : X →ₗ[K] X, (∀ x, p x ∈ U) ∧ (∀ x ∈ U, p x = x) ∧ p.comp p = p := by
  obtain ⟨r, hr⟩ := U.subtype.exists_leftInverse_of_injective U.ker_subtype
  refine ⟨U.subtype.comp r, ?_, ?_, ?_⟩
  · intro x; exact (r x).property
  · intro x hx
    exact congrArg Subtype.val (LinearMap.congr_fun hr ⟨x, hx⟩)
  · ext x
    exact congrArg Subtype.val (LinearMap.congr_fun hr (r x))

/-- Failure of surjectivity supplies a nonzero central idempotent annihilating
all incoming arrows. This is the concrete simple-summand obstruction. -/
theorem sink_defect_idempotent (f : W →ₗ[K] X) (hf : ¬ Function.Surjective f) :
    ∃ e : X →ₗ[K] X, e ≠ 0 ∧ e.comp e = e ∧ e.comp f = 0 := by
  obtain ⟨p, hp, hpfix, hpp⟩ := exists_projection (LinearMap.range f)
  let e : X →ₗ[K] X := LinearMap.id - p
  refine ⟨e, ?_, ?_, ?_⟩
  · intro he
    apply hf
    intro x
    have hx : x = p x := by
      have hh := LinearMap.congr_fun he x
      change x - p x = 0 at hh
      exact sub_eq_zero.mp hh
    rw [hx]
    exact hp x
  · ext x
    have hh := LinearMap.congr_fun hpp x
    change p (p x) = p x at hh
    simp [e, map_sub, hh]
  · ext w
    have hh := hpfix (f w) ⟨w, rfl⟩
    simp [e, hh]

/-- Failure of injectivity supplies a nonzero central idempotent killed by all
outgoing arrows. -/
theorem source_defect_idempotent (g : X →ₗ[K] W) (hg : ¬ Function.Injective g) :
    ∃ e : X →ₗ[K] X, e ≠ 0 ∧ e.comp e = e ∧ g.comp e = 0 := by
  obtain ⟨p, hp, hpfix, hpp⟩ := exists_projection (LinearMap.ker g)
  refine ⟨p, ?_, hpp, ?_⟩
  · intro he
    apply hg
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro x hx
      have hh := hpfix x hx
      rw [he, LinearMap.zero_apply] at hh
      exact hh.symm
    · exact bot_le
  · ext x
    exact hp x

section Attached

open QuiverRepresentation

variable {V E I : Type u} [Fintype I] [DecidableEq I]
  {Q : Orientation V E} (R : Rep K Q) (neighbour : I → V)

/-- Actual representation after reversing the arrows at the new sink. -/
def reflectAttachedSink (f : Boundary R neighbour →ₗ[K] X) :
    Rep K (attachSourceOrientation Q neighbour) := attachSource R neighbour (sink f)

/-- Actual representation after reversing the arrows at the new source. -/
def reflectAttachedSource (g : X →ₗ[K] Boundary R neighbour) :
    Rep K (attachSinkOrientation Q neighbour) := attachSink R neighbour (source g)

variable {R} {neighbour} {S : Rep K Q}

/-- The vertexwise map on the unchanged neighbours. -/
def boundaryMap (h : ∀ v, R.space v →ₗ[K] S.space v) :
    Boundary R neighbour →ₗ[K] Boundary S neighbour :=
  LinearMap.pi (fun i => (h (neighbour i)).comp (LinearMap.proj i))

omit [Fintype I] in
@[simp] theorem boundaryMap_single (h : ∀ v, R.space v →ₗ[K] S.space v)
    (i : I) (x : R.space (neighbour i)) :
    boundaryMap (neighbour := neighbour) h (Pi.single i x) =
      Pi.single i (h (neighbour i) x) := by
  ext j
  by_cases he : i = j
  · subst j; simp [boundaryMap]
  · simp [boundaryMap, Pi.single_eq_of_ne (Ne.symm he)]

/-- Extract the aggregate commuting square from a morphism of entire sink diagrams. -/
def attachedSinkSquare {f : Boundary R neighbour →ₗ[K] X}
    {f' : Boundary S neighbour →ₗ[K] X'}
    (h : Hom (attachSink R neighbour f) (attachSink S neighbour f')) : SinkHom f f' where
  boundary := boundaryMap (fun v => h.map (some v))
  center := h.map none
  comm := by
    apply LinearMap.pi_ext
    intro i x
    change f' (boundaryMap (fun v => h.map (some v)) (Pi.single i x)) = _
    rw [boundaryMap_single]
    exact (LinearMap.congr_fun (h.comm (Sum.inr i)) x).symm

/-- Extract the aggregate commuting square from a morphism of entire source diagrams. -/
def attachedSourceSquare {g : X →ₗ[K] Boundary R neighbour}
    {g' : X' →ₗ[K] Boundary S neighbour}
    (h : Hom (attachSource R neighbour g) (attachSource S neighbour g')) : SourceHom g g' where
  boundary := boundaryMap (fun v => h.map (some v))
  center := h.map none
  comm := by
    apply LinearMap.ext
    intro x
    funext i
    exact (LinearMap.congr_fun (h.comm (Sum.inr i)) x).symm

/-- Reflection on morphisms of full representations with arbitrary peripheral arrows. -/
def reflectAttachedSinkHom {f : Boundary R neighbour →ₗ[K] X}
    {f' : Boundary S neighbour →ₗ[K] X'}
    (h : Hom (attachSink R neighbour f) (attachSink S neighbour f')) :
    Hom (attachSource R neighbour (sink f)) (attachSource S neighbour (sink f')) where
  map
    | none => (reflectSinkHom (attachedSinkSquare h)).center
    | some v => h.map (some v)
  comm e := by
    cases e with
    | inl e => exact h.comm (Sum.inl e)
    | inr i =>
      apply LinearMap.ext
      intro x
      rfl

/-- Cokernel reflection on morphisms of full representations. -/
def reflectAttachedSourceHom {g : X →ₗ[K] Boundary R neighbour}
    {g' : X' →ₗ[K] Boundary S neighbour}
    (h : Hom (attachSource R neighbour g) (attachSource S neighbour g')) :
    Hom (attachSink R neighbour (source g)) (attachSink S neighbour (source g')) where
  map
    | none => (reflectSourceHom (attachedSourceSquare h)).center
    | some v => h.map (some v)
  comm e := by
    cases e with
    | inl e => exact h.comm (Sum.inl e)
    | inr i =>
      apply LinearMap.ext
      intro x
      change (source g') (boundaryMap (fun v => h.map (some v)) (Pi.single i x)) =
        (source g') (Pi.single i ((h.map (some (neighbour i))) x))
      rw [boundaryMap_single]
      rfl

/-- Inverse transport on full sink-diagram morphisms. -/
noncomputable def unreflectAttachedSinkHom {f : Boundary R neighbour →ₗ[K] X}
    {f' : Boundary S neighbour →ₗ[K] X'}
    (hf : Function.Surjective f) (hf' : Function.Surjective f')
    (h : Hom (attachSource R neighbour (sink f)) (attachSource S neighbour (sink f'))) :
    Hom (attachSink R neighbour f) (attachSink S neighbour f') where
  map
    | none => (unreflectSinkHom hf hf' (attachedSourceSquare h)).center
    | some v => h.map (some v)
  comm e := by
    cases e with
    | inl e => exact h.comm (Sum.inl e)
    | inr i =>
      apply LinearMap.ext
      intro x
      have hh := LinearMap.congr_fun
        (unreflectSinkHom hf hf' (attachedSourceSquare h)).comm (Pi.single i x)
      change f' (boundaryMap (fun v => h.map (some v)) (Pi.single i x)) = _ at hh
      rw [boundaryMap_single] at hh
      exact hh.symm

@[simp] theorem unreflect_reflectAttachedSinkHom {f : Boundary R neighbour →ₗ[K] X}
    {f' : Boundary S neighbour →ₗ[K] X'}
    (hf : Function.Surjective f) (hf' : Function.Surjective f')
    (h : Hom (attachSink R neighbour f) (attachSink S neighbour f')) :
    unreflectAttachedSinkHom hf hf' (reflectAttachedSinkHom h) = h := by
  apply Hom.ext
  intro v
  cases v with
  | some v => rfl
  | none =>
    apply LinearMap.ext
    intro x
    obtain ⟨w, rfl⟩ := hf x
    exact (LinearMap.congr_fun
      (unreflectSinkHom hf hf' (attachedSourceSquare (reflectAttachedSinkHom h))).comm w).symm.trans
      (LinearMap.congr_fun (attachedSinkSquare h).comm w)

@[simp] theorem reflect_unreflectAttachedSinkHom {f : Boundary R neighbour →ₗ[K] X}
    {f' : Boundary S neighbour →ₗ[K] X'}
    (hf : Function.Surjective f) (hf' : Function.Surjective f')
    (h : Hom (attachSource R neighbour (sink f)) (attachSource S neighbour (sink f'))) :
    reflectAttachedSinkHom (unreflectAttachedSinkHom hf hf' h) = h := by
  apply Hom.ext
  intro v
  cases v with
  | some v => rfl
  | none =>
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (LinearMap.congr_fun (attachedSourceSquare h).comm x).symm

/-- Fully faithful reflection for actual quiver representations in the local
chart, including all arrows in the unchanged peripheral quiver. -/
noncomputable def attachedSinkHomEquiv {f : Boundary R neighbour →ₗ[K] X}
    {f' : Boundary S neighbour →ₗ[K] X'}
    (hf : Function.Surjective f) (hf' : Function.Surjective f') :
    Hom (attachSink R neighbour f) (attachSink S neighbour f') ≃
      Hom (attachSource R neighbour (sink f)) (attachSource S neighbour (sink f')) where
  toFun := reflectAttachedSinkHom
  invFun := unreflectAttachedSinkHom hf hf'
  left_inv := unreflect_reflectAttachedSinkHom hf hf'
  right_inv := reflect_unreflectAttachedSinkHom hf hf'

@[simp] theorem reflectAttachedSinkHom_id (f : Boundary R neighbour →ₗ[K] X) :
    reflectAttachedSinkHom (Hom.id (attachSink R neighbour f)) =
      Hom.id (attachSource R neighbour (sink f)) := by
  apply Hom.ext
  intro v
  cases v <;> rfl

@[simp] theorem reflectAttachedSinkHom_comp {T : Rep K Q}
    {f : Boundary R neighbour →ₗ[K] X} {f' : Boundary S neighbour →ₗ[K] X'}
    {f'' : Boundary T neighbour →ₗ[K] X''}
    (b : Hom (attachSink S neighbour f') (attachSink T neighbour f''))
    (a : Hom (attachSink R neighbour f) (attachSink S neighbour f')) :
    reflectAttachedSinkHom (b.comp a) =
      (reflectAttachedSinkHom b).comp (reflectAttachedSinkHom a) := by
  apply Hom.ext
  intro v
  cases v <;> rfl

@[simp] theorem reflectAttachedSinkHom_zero {f : Boundary R neighbour →ₗ[K] X}
    {f' : Boundary S neighbour →ₗ[K] X'} :
    reflectAttachedSinkHom (Hom.zero (attachSink R neighbour f) (attachSink S neighbour f')) =
      Hom.zero (attachSource R neighbour (sink f)) (attachSource S neighbour (sink f')) := by
  apply Hom.ext
  intro v
  cases v <;> rfl

/-- Idempotent-triviality is preserved for the whole attached representation,
with every unchanged arrow's commutativity imposed. -/
theorem attachedSink_idempotents_iff (f : Boundary R neighbour →ₗ[K] X)
    (hf : Function.Surjective f) :
    IdempotentsTrivial (attachSink R neighbour f) ↔
      IdempotentsTrivial (attachSource R neighbour (sink f)) := by
  constructor
  · intro h a haa
    let b := unreflectAttachedSinkHom hf hf a
    have hb : b.comp b = b := by
      apply (attachedSinkHomEquiv hf hf).injective
      change reflectAttachedSinkHom (b.comp b) = reflectAttachedSinkHom b
      simp only [reflectAttachedSinkHom_comp, b, reflect_unreflectAttachedSinkHom, haa]
    rcases h b hb with hz | hi
    · left
      have := congrArg reflectAttachedSinkHom hz
      simpa only [b, reflect_unreflectAttachedSinkHom, reflectAttachedSinkHom_zero] using this
    · right
      have := congrArg reflectAttachedSinkHom hi
      simpa only [b, reflect_unreflectAttachedSinkHom, reflectAttachedSinkHom_id] using this
  · intro h a haa
    have hh : (reflectAttachedSinkHom a).comp (reflectAttachedSinkHom a) =
        reflectAttachedSinkHom a := by rw [← reflectAttachedSinkHom_comp, haa]
    rcases h (reflectAttachedSinkHom a) hh with hz | hi
    · left
      apply (attachedSinkHomEquiv hf hf).injective
      simpa only [attachedSinkHomEquiv, Equiv.coe_fn_mk, reflectAttachedSinkHom_zero] using hz
    · right
      apply (attachedSinkHomEquiv hf hf).injective
      simpa only [attachedSinkHomEquiv, Equiv.coe_fn_mk, reflectAttachedSinkHom_id] using hi

/-- Inverse transport on full source-diagram morphisms. -/
noncomputable def unreflectAttachedSourceHom {g : X →ₗ[K] Boundary R neighbour}
    {g' : X' →ₗ[K] Boundary S neighbour}
    (hg : Function.Injective g) (hg' : Function.Injective g')
    (h : Hom (attachSink R neighbour (source g)) (attachSink S neighbour (source g'))) :
    Hom (attachSource R neighbour g) (attachSource S neighbour g') where
  map
    | none => (unreflectSourceHom hg hg' (attachedSinkSquare h)).center
    | some v => h.map (some v)
  comm e := by
    cases e with
    | inl e => exact h.comm (Sum.inl e)
    | inr i =>
      apply LinearMap.ext
      intro x
      exact (congrFun (LinearMap.congr_fun
        (unreflectSourceHom hg hg' (attachedSinkSquare h)).comm x) i).symm

@[simp] theorem unreflect_reflectAttachedSourceHom {g : X →ₗ[K] Boundary R neighbour}
    {g' : X' →ₗ[K] Boundary S neighbour}
    (hg : Function.Injective g) (hg' : Function.Injective g')
    (h : Hom (attachSource R neighbour g) (attachSource S neighbour g')) :
    unreflectAttachedSourceHom hg hg' (reflectAttachedSourceHom h) = h := by
  apply Hom.ext
  intro v
  cases v with
  | some v => rfl
  | none =>
    apply LinearMap.ext
    intro x
    apply hg'
    exact (LinearMap.congr_fun
      (unreflectSourceHom hg hg' (attachedSinkSquare (reflectAttachedSourceHom h))).comm x).trans
      (LinearMap.congr_fun (attachedSourceSquare h).comm x).symm

@[simp] theorem reflect_unreflectAttachedSourceHom {g : X →ₗ[K] Boundary R neighbour}
    {g' : X' →ₗ[K] Boundary S neighbour}
    (hg : Function.Injective g) (hg' : Function.Injective g')
    (h : Hom (attachSink R neighbour (source g)) (attachSink S neighbour (source g'))) :
    reflectAttachedSourceHom (unreflectAttachedSourceHom hg hg' h) = h := by
  apply Hom.ext
  intro v
  cases v with
  | some v => rfl
  | none =>
    apply LinearMap.ext
    intro x
    obtain ⟨w, rfl⟩ := source_surjective g x
    exact (LinearMap.congr_fun
      (attachedSinkSquare (reflectAttachedSourceHom (unreflectAttachedSourceHom hg hg' h))).comm w).symm.trans
      (LinearMap.congr_fun (attachedSinkSquare h).comm w)

/-- Fully faithful source reflection for actual quiver representations. -/
noncomputable def attachedSourceHomEquiv {g : X →ₗ[K] Boundary R neighbour}
    {g' : X' →ₗ[K] Boundary S neighbour}
    (hg : Function.Injective g) (hg' : Function.Injective g') :
    Hom (attachSource R neighbour g) (attachSource S neighbour g') ≃
      Hom (attachSink R neighbour (source g)) (attachSink S neighbour (source g')) where
  toFun := reflectAttachedSourceHom
  invFun := unreflectAttachedSourceHom hg hg'
  left_inv := unreflect_reflectAttachedSourceHom hg hg'
  right_inv := reflect_unreflectAttachedSourceHom hg hg'

omit [Fintype I] in
@[simp] theorem reflectAttachedSourceHom_id (g : X →ₗ[K] Boundary R neighbour) :
    reflectAttachedSourceHom (Hom.id (attachSource R neighbour g)) =
      Hom.id (attachSink R neighbour (source g)) := by
  apply Hom.ext
  intro v
  cases v with
  | some v => rfl
  | none =>
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with | H w => rfl

omit [Fintype I] in
@[simp] theorem reflectAttachedSourceHom_comp {T : Rep K Q}
    {g : X →ₗ[K] Boundary R neighbour} {g' : X' →ₗ[K] Boundary S neighbour}
    {g'' : X'' →ₗ[K] Boundary T neighbour}
    (b : Hom (attachSource S neighbour g') (attachSource T neighbour g''))
    (a : Hom (attachSource R neighbour g) (attachSource S neighbour g')) :
    reflectAttachedSourceHom (b.comp a) =
      (reflectAttachedSourceHom b).comp (reflectAttachedSourceHom a) := by
  apply Hom.ext
  intro v
  cases v with
  | some v => rfl
  | none =>
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with | H w => rfl

omit [Fintype I] in
@[simp] theorem reflectAttachedSourceHom_zero {g : X →ₗ[K] Boundary R neighbour}
    {g' : X' →ₗ[K] Boundary S neighbour} :
    reflectAttachedSourceHom (Hom.zero (attachSource R neighbour g) (attachSource S neighbour g')) =
      Hom.zero (attachSink R neighbour (source g)) (attachSink S neighbour (source g')) := by
  apply Hom.ext
  intro v
  cases v with
  | some v => rfl
  | none =>
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H w => exact Submodule.Quotient.mk_zero _

theorem attachedSource_idempotents_iff (g : X →ₗ[K] Boundary R neighbour)
    (hg : Function.Injective g) :
    IdempotentsTrivial (attachSource R neighbour g) ↔
      IdempotentsTrivial (attachSink R neighbour (source g)) := by
  constructor
  · intro h a haa
    let b := unreflectAttachedSourceHom hg hg a
    have hb : b.comp b = b := by
      apply (attachedSourceHomEquiv hg hg).injective
      change reflectAttachedSourceHom (b.comp b) = reflectAttachedSourceHom b
      simp only [reflectAttachedSourceHom_comp, b, reflect_unreflectAttachedSourceHom, haa]
    rcases h b hb with hz | hi
    · left
      have := congrArg reflectAttachedSourceHom hz
      simpa only [b, reflect_unreflectAttachedSourceHom, reflectAttachedSourceHom_zero] using this
    · right
      have := congrArg reflectAttachedSourceHom hi
      simpa only [b, reflect_unreflectAttachedSourceHom, reflectAttachedSourceHom_id] using this
  · intro h a haa
    have hh : (reflectAttachedSourceHom a).comp (reflectAttachedSourceHom a) =
        reflectAttachedSourceHom a := by rw [← reflectAttachedSourceHom_comp, haa]
    rcases h (reflectAttachedSourceHom a) hh with hz | hi
    · left
      apply (attachedSourceHomEquiv hg hg).injective
      simpa only [attachedSourceHomEquiv, Equiv.coe_fn_mk, reflectAttachedSourceHom_zero] using hz
    · right
      apply (attachedSourceHomEquiv hg hg).injective
      simpa only [attachedSourceHomEquiv, Equiv.coe_fn_mk, reflectAttachedSourceHom_id] using hi

/-- Isomorphisms of complete sink representations reflect to actual isomorphisms. -/
def reflectAttachedSinkIso {f : Boundary R neighbour →ₗ[K] X}
    {f' : Boundary S neighbour →ₗ[K] X'}
    (h : Iso (attachSink R neighbour f) (attachSink S neighbour f')) :
    Iso (attachSource R neighbour (sink f)) (attachSource S neighbour (sink f')) :=
  Iso.ofInverse (reflectAttachedSinkHom h.toHom) (reflectAttachedSinkHom h.symm.toHom)
    (by rw [← reflectAttachedSinkHom_comp, Iso.symm_comp, reflectAttachedSinkHom_id])
    (by rw [← reflectAttachedSinkHom_comp, Iso.comp_symm, reflectAttachedSinkHom_id])

/-- Isomorphisms of complete source representations reflect to actual isomorphisms. -/
def reflectAttachedSourceIso {g : X →ₗ[K] Boundary R neighbour}
    {g' : X' →ₗ[K] Boundary S neighbour}
    (h : Iso (attachSource R neighbour g) (attachSource S neighbour g')) :
    Iso (attachSink R neighbour (source g)) (attachSink S neighbour (source g')) :=
  Iso.ofInverse (reflectAttachedSourceHom h.toHom) (reflectAttachedSourceHom h.symm.toHom)
    (by rw [← reflectAttachedSourceHom_comp, Iso.symm_comp, reflectAttachedSourceHom_id])
    (by rw [← reflectAttachedSourceHom_comp, Iso.comp_symm, reflectAttachedSourceHom_id])

/-- Isomorphisms of reflected surjective sink representations lift uniquely on morphisms. -/
noncomputable def unreflectAttachedSinkIso {f : Boundary R neighbour →ₗ[K] X}
    {f' : Boundary S neighbour →ₗ[K] X'}
    (hf : Function.Surjective f) (hf' : Function.Surjective f')
    (h : Iso (attachSource R neighbour (sink f)) (attachSource S neighbour (sink f'))) :
    Iso (attachSink R neighbour f) (attachSink S neighbour f') :=
  Iso.ofInverse (unreflectAttachedSinkHom hf hf' h.toHom)
    (unreflectAttachedSinkHom hf' hf h.symm.toHom)
    (by
      apply (attachedSinkHomEquiv hf hf).injective
      change reflectAttachedSinkHom _ = reflectAttachedSinkHom _
      rw [reflectAttachedSinkHom_comp, reflect_unreflectAttachedSinkHom,
        reflect_unreflectAttachedSinkHom, Iso.symm_comp, reflectAttachedSinkHom_id])
    (by
      apply (attachedSinkHomEquiv hf' hf').injective
      change reflectAttachedSinkHom _ = reflectAttachedSinkHom _
      rw [reflectAttachedSinkHom_comp, reflect_unreflectAttachedSinkHom,
        reflect_unreflectAttachedSinkHom, Iso.comp_symm, reflectAttachedSinkHom_id])

/-- The corresponding lift for reflected injective source representations. -/
noncomputable def unreflectAttachedSourceIso {g : X →ₗ[K] Boundary R neighbour}
    {g' : X' →ₗ[K] Boundary S neighbour}
    (hg : Function.Injective g) (hg' : Function.Injective g')
    (h : Iso (attachSink R neighbour (source g)) (attachSink S neighbour (source g'))) :
    Iso (attachSource R neighbour g) (attachSource S neighbour g') :=
  Iso.ofInverse (unreflectAttachedSourceHom hg hg' h.toHom)
    (unreflectAttachedSourceHom hg' hg h.symm.toHom)
    (by
      apply (attachedSourceHomEquiv hg hg).injective
      change reflectAttachedSourceHom _ = reflectAttachedSourceHom _
      rw [reflectAttachedSourceHom_comp, reflect_unreflectAttachedSourceHom,
        reflect_unreflectAttachedSourceHom, Iso.symm_comp, reflectAttachedSourceHom_id])
    (by
      apply (attachedSourceHomEquiv hg' hg').injective
      change reflectAttachedSourceHom _ = reflectAttachedSourceHom _
      rw [reflectAttachedSourceHom_comp, reflect_unreflectAttachedSourceHom,
        reflect_unreflectAttachedSourceHom, Iso.comp_symm, reflectAttachedSourceHom_id])

variable (R) (neighbour)

/-- The double reflection is isomorphic to the original representation on every
vertex and every arrow, leaving the entire peripheral quiver unchanged. -/
noncomputable def attachedSinkRecovery (f : Boundary R neighbour →ₗ[K] X)
    (hf : Function.Surjective f) :
    Iso (attachSink R neighbour (source (sink f))) (attachSink R neighbour f) where
  map
    | none => sinkRecovery f hf
    | some v => LinearEquiv.refl K (R.space v)
  comm e := by
    cases e with
    | inl e => simp [attachSink, attachSinkOrientation]
    | inr i =>
      apply LinearMap.ext
      intro x
      exact sinkRecovery_arrow f hf ((LinearMap.single K _ i) x)

/-- The opposite double reflection also recovers all peripheral and incident
arrows, not merely the dimension at the reflected vertex. -/
noncomputable def attachedSourceRecovery (g : X →ₗ[K] Boundary R neighbour)
    (hg : Function.Injective g) :
    Iso (attachSource R neighbour g) (attachSource R neighbour (sink (source g))) where
  map
    | none => sourceRecovery g hg
    | some v => LinearEquiv.refl K (R.space v)
  comm e := by
    cases e with
    | inl e => simp [attachSource, attachSourceOrientation]
    | inr i =>
      apply LinearMap.ext
      intro x
      exact (congrFun (sourceRecovery_arrow g hg x) i).symm

/-- Naturality of recovery as morphisms of the entire sink representation. -/
theorem attachedSinkRecovery_natural {S : Rep K Q}
    {f : Boundary R neighbour →ₗ[K] X} {f' : Boundary S neighbour →ₗ[K] X'}
    (h : Hom (attachSink R neighbour f) (attachSink S neighbour f'))
    (hf : Function.Surjective f) (hf' : Function.Surjective f') :
    (attachedSinkRecovery S neighbour f' hf').toHom.comp
        (reflectAttachedSourceHom (reflectAttachedSinkHom h)) =
      h.comp (attachedSinkRecovery R neighbour f hf).toHom := by
  apply Hom.ext
  intro v
  cases v with
  | some v => rfl
  | none =>
    apply LinearMap.ext
    intro x
    exact sinkRecovery_natural (attachedSinkSquare h) hf hf' x

/-- Naturality of recovery as morphisms of the entire source representation. -/
theorem attachedSourceRecovery_natural {S : Rep K Q}
    {g : X →ₗ[K] Boundary R neighbour} {g' : X' →ₗ[K] Boundary S neighbour}
    (h : Hom (attachSource R neighbour g) (attachSource S neighbour g'))
    (hg : Function.Injective g) (hg' : Function.Injective g') :
    (reflectAttachedSinkHom (reflectAttachedSourceHom h)).comp
        (attachedSourceRecovery R neighbour g hg).toHom =
      (attachedSourceRecovery S neighbour g' hg').toHom.comp h := by
  apply Hom.ext
  intro v
  cases v with
  | some v => rfl
  | none =>
    apply LinearMap.ext
    intro x
    exact sourceRecovery_natural (attachedSourceSquare h) hg hg' x

omit [Fintype I] in
theorem attachedSink_isZero_iff (f : Boundary R neighbour →ₗ[K] X)
    (hf : Function.Surjective f) :
    IsZero (attachSink R neighbour f) ↔ IsZero (attachSource R neighbour (sink f)) := by
  constructor
  · intro h v x
    cases v with
    | some v => exact h (some v) x
    | none =>
      apply Subtype.ext
      funext i
      exact h (some (neighbour i)) (x.val i)
  · intro h v x
    cases v with
    | some v => exact h (some v) x
    | none =>
      obtain ⟨w, rfl⟩ := hf x
      have hw : w = 0 := funext (fun i => h (some (neighbour i)) (w i))
      rw [hw, map_zero]

omit [Fintype I] in
theorem attachedSource_isZero_iff (g : X →ₗ[K] Boundary R neighbour)
    (hg : Function.Injective g) :
    IsZero (attachSource R neighbour g) ↔ IsZero (attachSink R neighbour (source g)) := by
  constructor
  · intro h v x
    cases v with
    | some v => exact h (some v) x
    | none =>
      obtain ⟨w, rfl⟩ := source_surjective g x
      have hw : w = 0 := funext (fun i => h (some (neighbour i)) (w i))
      rw [hw, map_zero]
  · intro h v x
    cases v with
    | some v => exact h (some v) x
    | none =>
      apply hg
      rw [map_zero]
      exact funext (fun i => h (some (neighbour i)) (g x i))

/-- Actual direct-sum indecomposability is preserved by sink reflection. -/
theorem attachedSink_indecomposable_iff (f : Boundary R neighbour →ₗ[K] X)
    (hf : Function.Surjective f) :
    Indecomposable (attachSink R neighbour f) ↔
      Indecomposable (attachSource R neighbour (sink f)) := by
  rw [indecomposable_iff, indecomposable_iff,
    attachedSink_isZero_iff R neighbour f hf, attachedSink_idempotents_iff f hf]

/-- Actual direct-sum indecomposability is preserved by source reflection. -/
theorem attachedSource_indecomposable_iff (g : X →ₗ[K] Boundary R neighbour)
    (hg : Function.Injective g) :
    Indecomposable (attachSource R neighbour g) ↔
      Indecomposable (attachSink R neighbour (source g)) := by
  rw [indecomposable_iff, indecomposable_iff,
    attachedSource_isZero_iff R neighbour g hg, attachedSource_idempotents_iff g hg]

omit [Fintype I] in
/-- An idempotent-trivial representation with a nonzero peripheral vertex
has the local surjectivity needed for sink reflection. -/
theorem attachedSink_surjective_of_idempotents (f : Boundary R neighbour →ₗ[K] X)
    (h : IdempotentsTrivial (attachSink R neighbour f))
    (v : V) [Nontrivial (R.space v)] : Function.Surjective f := by
  by_contra hf
  obtain ⟨e, he, hee, hef⟩ := sink_defect_idempotent f hf
  let a : Hom (attachSink R neighbour f) (attachSink R neighbour f) := {
    map := fun j => match j with
      | none => e
      | some _ => 0
    comm := by
      intro j
      cases j with
      | inl j => simp [attachSink, attachSinkOrientation]
      | inr i =>
        apply LinearMap.ext
        intro x
        simpa [attachSink, attachSinkOrientation] using
          LinearMap.congr_fun hef ((LinearMap.single K _ i) x) }
  have haa : a.comp a = a := by
    apply Hom.ext
    intro j
    cases j with
    | none => exact hee
    | some j => simp [a, Hom.comp]
  rcases h a haa with hz | hi
  · apply he
    exact congrArg (fun b => b.map none) hz
  · have hh := congrArg (fun b => b.map (some v)) hi
    change (0 : R.space v →ₗ[K] R.space v) = LinearMap.id at hh
    obtain ⟨x, hx⟩ := exists_ne (0 : R.space v)
    exact hx (LinearMap.congr_fun hh x).symm

omit [Fintype I] [DecidableEq I] in
/-- The dual local injectivity condition follows by an explicit kernel projection. -/
theorem attachedSource_injective_of_idempotents (g : X →ₗ[K] Boundary R neighbour)
    (h : IdempotentsTrivial (attachSource R neighbour g))
    (v : V) [Nontrivial (R.space v)] : Function.Injective g := by
  by_contra hg
  obtain ⟨e, he, hee, hge⟩ := source_defect_idempotent g hg
  let a : Hom (attachSource R neighbour g) (attachSource R neighbour g) := {
    map := fun j => match j with
      | none => e
      | some _ => 0
    comm := by
      intro j
      cases j with
      | inl j => simp [attachSource, attachSourceOrientation]
      | inr i =>
        apply LinearMap.ext
        intro x
        exact (congrFun (LinearMap.congr_fun hge x) i).symm }
  have haa : a.comp a = a := by
    apply Hom.ext
    intro j
    cases j with
    | none => exact hee
    | some j => simp [a, Hom.comp]
  rcases h a haa with hz | hi
  · apply he
    exact congrArg (fun b => b.map none) hz
  · have hh := congrArg (fun b => b.map (some v)) hi
    change (0 : R.space v →ₗ[K] R.space v) = LinearMap.id at hh
    obtain ⟨x, hx⟩ := exists_ne (0 : R.space v)
    exact hx (LinearMap.congr_fun hh x).symm

/-- Away from the vertex-supported exception, sink reflection preserves actual
indecomposability without assuming its required surjectivity separately. -/
theorem attachedSink_reflects_indecomposable (f : Boundary R neighbour →ₗ[K] X)
    (h : Indecomposable (attachSink R neighbour f))
    (v : V) [Nontrivial (R.space v)] :
    Indecomposable (attachSource R neighbour (sink f)) := by
  exact (attachedSink_indecomposable_iff R neighbour f
    (attachedSink_surjective_of_idempotents R neighbour f h.idempotentsTrivial v)).mp h

/-- The dual statement, with injectivity proved from the actual representation. -/
theorem attachedSource_reflects_indecomposable (g : X →ₗ[K] Boundary R neighbour)
    (h : Indecomposable (attachSource R neighbour g))
    (v : V) [Nontrivial (R.space v)] :
    Indecomposable (attachSink R neighbour (source g)) := by
  exact (attachedSource_indecomposable_iff R neighbour g
    (attachedSource_injective_of_idempotents R neighbour g h.idempotentsTrivial v)).mp h

omit [Fintype I] in
/-- If an indecomposable is supported only at the sink, the exceptional
central space really has dimension one. -/
theorem attachedSink_simple_exception (f : Boundary R neighbour →ₗ[K] X)
    (h : Indecomposable (attachSink R neighbour f)) (hR : IsZero R) :
    Module.finrank K X = 1 := by
  classical
  have hn : ∃ x : X, x ≠ 0 := by
    by_contra! hn
    apply h.1
    intro v x
    cases v with
    | none => exact hn x
    | some v => exact hR v x
  obtain ⟨x, hx⟩ := hn
  have hf0 : f = 0 := by
    apply LinearMap.ext
    intro w
    have hw : w = 0 := funext (fun i => hR (neighbour i) (w i))
    rw [hw, map_zero]
    rfl
  obtain ⟨p, hp, hpfix, hpp⟩ := exists_projection (Submodule.span K {x})
  let a : Hom (attachSink R neighbour f) (attachSink R neighbour f) := {
    map := fun v => match v with | none => p | some _ => 0
    comm := by
      intro e
      cases e <;> simp [attachSink, attachSinkOrientation, hf0] }
  have haa : a.comp a = a := by
    apply Hom.ext
    intro v
    cases v with
    | none => exact hpp
    | some v => simp [a, Hom.comp]
  rcases h.idempotentsTrivial a haa with hz | hi
  · have hp0 : p = 0 := congrArg (fun b => b.map none) hz
    have hh := hpfix x (Submodule.subset_span (Set.mem_singleton x))
    rw [hp0, LinearMap.zero_apply] at hh
    exact False.elim (hx hh.symm)
  · have hpid : p = LinearMap.id := congrArg (fun b => b.map none) hi
    have ht : Submodule.span K {x} = ⊤ := by
      apply top_unique
      intro y _
      have hh := hp y
      rwa [hpid, LinearMap.id_apply] at hh
    have hh : Module.finrank K (Submodule.span K {x}) = 1 := finrank_span_singleton hx
    rw [ht, finrank_top] at hh
    exact hh

omit [Fintype I] [DecidableEq I] in
/-- The source-supported exceptional indecomposable is also one-dimensional. -/
theorem attachedSource_simple_exception (g : X →ₗ[K] Boundary R neighbour)
    (h : Indecomposable (attachSource R neighbour g)) (hR : IsZero R) :
    Module.finrank K X = 1 := by
  classical
  have hn : ∃ x : X, x ≠ 0 := by
    by_contra! hn
    apply h.1
    intro v x
    cases v with
    | none => exact hn x
    | some v => exact hR v x
  obtain ⟨x, hx⟩ := hn
  have hg0 : g = 0 := by
    ext x i
    exact hR (neighbour i) (g x i)
  obtain ⟨p, hp, hpfix, hpp⟩ := exists_projection (Submodule.span K {x})
  let a : Hom (attachSource R neighbour g) (attachSource R neighbour g) := {
    map := fun v => match v with | none => p | some _ => 0
    comm := by
      intro e
      cases e <;> simp [attachSource, attachSourceOrientation, hg0] }
  have haa : a.comp a = a := by
    apply Hom.ext
    intro v
    cases v with
    | none => exact hpp
    | some v => simp [a, Hom.comp]
  rcases h.idempotentsTrivial a haa with hz | hi
  · have hp0 : p = 0 := congrArg (fun b => b.map none) hz
    have hh := hpfix x (Submodule.subset_span (Set.mem_singleton x))
    rw [hp0, LinearMap.zero_apply] at hh
    exact False.elim (hx hh.symm)
  · have hpid : p = LinearMap.id := congrArg (fun b => b.map none) hi
    have ht : Submodule.span K {x} = ⊤ := by
      apply top_unique
      intro y _
      have hh := hp y
      rwa [hpid, LinearMap.id_apply] at hh
    have hh : Module.finrank K (Submodule.span K {x}) = 1 := finrank_span_singleton hx
    rw [ht, finrank_top] at hh
    exact hh

omit [DecidableEq I] in
/-- The numerical sink formula now uses the sum of the actual neighbour-space dimensions. -/
theorem attachedSink_finrank [∀ i, FiniteDimensional K (R.space (neighbour i))]
    (f : Boundary R neighbour →ₗ[K] X) (hf : Function.Surjective f) :
    Module.finrank K (LinearMap.ker f) + Module.finrank K X =
      ∑ i, Module.finrank K (R.space (neighbour i)) := by
  rw [← Module.finrank_pi_fintype]
  exact sink_finrank f hf

omit [DecidableEq I] in
/-- The dual numerical formula is derived from the actual quotient. -/
theorem attachedSource_finrank [∀ i, FiniteDimensional K (R.space (neighbour i))]
    (g : X →ₗ[K] Boundary R neighbour) (hg : Function.Injective g) :
    Module.finrank K (Boundary R neighbour ⧸ LinearMap.range g) + Module.finrank K X =
      ∑ i, Module.finrank K (R.space (neighbour i)) := by
  rw [← Module.finrank_pi_fintype]
  exact source_finrank g hg

end Attached

end UploadBroadcast.ReflectionEquivalence
