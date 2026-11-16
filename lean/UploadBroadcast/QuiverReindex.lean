import UploadBroadcast.ReflectionEquivalence

/-! Reindexing actual quiver representations and local sink/source charts. -/
namespace UploadBroadcast.QuiverRepresentation

universe u
variable {K V E V' E' V'' E'' : Type u} [Field K]
  {Q : Orientation V E} {Q' : Orientation V' E'} {Q'' : Orientation V'' E''}

/-- Transport a vertex module along a genuine equality of vertex labels. -/
def vertexCast (R : Rep K Q) {v w : V} (h : v = w) : R.space v ≃ₗ[K] R.space w := by
  subst w
  exact LinearEquiv.refl K _

@[simp] theorem vertexCast_rfl (R : Rep K Q) (v : V) :
    vertexCast R (rfl : v = v) = LinearEquiv.refl K _ := rfl

@[simp] theorem vertexCast_symm_apply (R : Rep K Q) {v w : V} (h : v = w) (x : R.space v) :
    vertexCast R h.symm (vertexCast R h x) = x := by cases h; rfl

@[simp] theorem vertexCast_apply_symm (R : Rep K Q) {v w : V} (h : v = w) (x : R.space w) :
    vertexCast R h (vertexCast R h.symm x) = x := by cases h; rfl

@[simp] theorem vertexCast_trans (R : Rep K Q) {v w z : V} (h : v = w) (h' : w = z)
    (x : R.space v) : vertexCast R h' (vertexCast R h x) = vertexCast R (h.trans h') x := by
  cases h; cases h'; rfl

/-- A relabelling preserves all source and target incidences. -/
structure GraphIso (Q : Orientation V E) (Q' : Orientation V' E') where
  vertex : V ≃ V'
  edge : E ≃ E'
  source : ∀ e, vertex (Q.source e) = Q'.source (edge e)
  target : ∀ e, vertex (Q.target e) = Q'.target (edge e)

/-- Pull an actual representation back through a graph relabelling. -/
def pullback (a : GraphIso Q Q') (R : Rep K Q') : Rep K Q where
  space v := R.space (a.vertex v)
  arrow e := (vertexCast R (a.target e).symm).toLinearMap.comp
    ((R.arrow (a.edge e)).comp (vertexCast R (a.source e)).toLinearMap)

theorem Hom.vertexCast_comm {R S : Rep K Q} (f : Hom R S) {v w : V}
    (h : v = w) (x : R.space v) :
    f.map w (vertexCast R h x) = vertexCast S h (f.map v x) := by
  cases h; rfl

/-- Reindex every component of a morphism without changing its linear map. -/
def pullbackHom (a : GraphIso Q Q') {R S : Rep K Q'} (f : Hom R S) :
    Hom (pullback a R) (pullback a S) where
  map v := f.map (a.vertex v)
  comm e := by
    apply LinearMap.ext
    intro x
    change f.map _ (vertexCast R _ (R.arrow _ (vertexCast R _ x))) =
      vertexCast S _ (S.arrow _ (vertexCast S _ (f.map _ x)))
    calc
      _ = vertexCast S (a.target e).symm
          (f.map _ (R.arrow _ (vertexCast R (a.source e) x))) := f.vertexCast_comm _ _
      _ = vertexCast S (a.target e).symm
          (S.arrow _ (f.map _ (vertexCast R (a.source e) x))) :=
        congrArg (vertexCast S (a.target e).symm)
          (LinearMap.congr_fun (f.comm (a.edge e)) (vertexCast R (a.source e) x))
      _ = _ := congrArg (vertexCast S (a.target e).symm)
        (congrArg (S.arrow (a.edge e)) (f.vertexCast_comm (a.source e) x))

@[simp] theorem pullback_arrow_cast (a : GraphIso Q Q') (R : Rep K Q') (e : E)
    (x : (pullback a R).space (Q.source e)) :
    vertexCast R (a.target e) ((pullback a R).arrow e x) =
      R.arrow (a.edge e) (vertexCast R (a.source e) x) := by
  simp only [pullback, LinearMap.comp_apply, LinearEquiv.coe_coe, vertexCast_apply_symm]

/-- Conjugate a family of linear maps back along the vertex equivalence. -/
def unpullbackMap (a : GraphIso Q Q') {R S : Rep K Q'}
    (f : ∀ v, (pullback a R).space v →ₗ[K] (pullback a S).space v)
    (v' : V') : R.space v' →ₗ[K] S.space v' :=
  (vertexCast S (a.vertex.apply_symm_apply v')).toLinearMap.comp
    ((f (a.vertex.symm v')).comp
      (vertexCast R (a.vertex.apply_symm_apply v').symm).toLinearMap)

@[simp] theorem unpullbackMap_image (a : GraphIso Q Q') {R S : Rep K Q'}
    (f : ∀ v, (pullback a R).space v →ₗ[K] (pullback a S).space v) (v : V) :
    unpullbackMap a f (a.vertex v) = f v := by
  apply LinearMap.ext
  intro x
  have aux : ∀ (w : V) (h : w = v),
      vertexCast S (congrArg a.vertex h)
        (f w (vertexCast R (congrArg a.vertex h).symm x)) = f v x := by
    intro w h
    cases h
    rfl
  exact aux _ (a.vertex.symm_apply_apply v)

theorem family_vertexCast_comm {R S : Rep K Q'}
    (f : ∀ v, R.space v →ₗ[K] S.space v) {v w : V'} (h : v = w) (x : R.space v) :
    f w (vertexCast R h x) = vertexCast S h (f v x) := by
  cases h; rfl

/-- Every morphism of reindexed diagrams comes uniquely from the original diagram. -/
def unpullbackHom (a : GraphIso Q Q') {R S : Rep K Q'}
    (f : Hom (pullback a R) (pullback a S)) : Hom R S where
  map := unpullbackMap a f.map
  comm e' := by
    obtain ⟨e, rfl⟩ := a.edge.surjective e'
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (vertexCast R (a.source e)).surjective x
    simp only [LinearMap.comp_apply]
    rw [← pullback_arrow_cast a R]
    rw [family_vertexCast_comm, family_vertexCast_comm,
      unpullbackMap_image, unpullbackMap_image]
    rw [← pullback_arrow_cast a S]
    exact congrArg (vertexCast S (a.target e)) (LinearMap.congr_fun (f.comm e) y)

@[simp] theorem unpullback_pullbackHom (a : GraphIso Q Q') {R S : Rep K Q'} (f : Hom R S) :
    unpullbackHom a (pullbackHom a f) = f := by
  apply Hom.ext
  intro v'
  obtain ⟨v, rfl⟩ := a.vertex.surjective v'
  exact unpullbackMap_image a _ v

@[simp] theorem pullback_unpullbackHom (a : GraphIso Q Q') {R S : Rep K Q'}
    (f : Hom (pullback a R) (pullback a S)) : pullbackHom a (unpullbackHom a f) = f := by
  apply Hom.ext
  intro v
  exact unpullbackMap_image a _ v

def pullbackHomEquiv (a : GraphIso Q Q') (R S : Rep K Q') :
    Hom R S ≃ Hom (pullback a R) (pullback a S) where
  toFun := pullbackHom a
  invFun := unpullbackHom a
  left_inv := unpullback_pullbackHom a
  right_inv := pullback_unpullbackHom a

@[simp] theorem pullbackHom_id (a : GraphIso Q Q') (R : Rep K Q') :
    pullbackHom a (Hom.id R) = Hom.id (pullback a R) := rfl

@[simp] theorem pullbackHom_zero (a : GraphIso Q Q') (R S : Rep K Q') :
    pullbackHom a (Hom.zero R S) = Hom.zero (pullback a R) (pullback a S) := rfl

@[simp] theorem pullbackHom_comp (a : GraphIso Q Q') {R S T : Rep K Q'}
    (f : Hom R S) (g : Hom S T) : pullbackHom a (g.comp f) = (pullbackHom a g).comp (pullbackHom a f) := rfl

theorem pullback_isZero_iff (a : GraphIso Q Q') (R : Rep K Q') :
    IsZero R ↔ IsZero (pullback a R) := by
  constructor
  · intro h v x; exact h (a.vertex v) x
  · intro h v x
    obtain ⟨v, rfl⟩ := a.vertex.surjective v
    exact h v x

theorem pullback_idempotents_iff (a : GraphIso Q Q') (R : Rep K Q') :
    IdempotentsTrivial R ↔ IdempotentsTrivial (pullback a R) := by
  constructor
  · intro h b hbb
    let c := unpullbackHom a b
    have hcc : c.comp c = c := by
      apply (pullbackHomEquiv a R R).injective
      change pullbackHom a _ = pullbackHom a _
      rw [pullbackHom_comp]
      simpa only [c, pullback_unpullbackHom] using hbb
    rcases h c hcc with hz | hi
    · left
      have hh := congrArg (pullbackHom a) hz
      simpa only [c, pullback_unpullbackHom, pullbackHom_zero] using hh
    · right
      have hh := congrArg (pullbackHom a) hi
      simpa only [c, pullback_unpullbackHom, pullbackHom_id] using hh
  · intro h b hbb
    have hcc : (pullbackHom a b).comp (pullbackHom a b) = pullbackHom a b := by
      rw [← pullbackHom_comp, hbb]
    rcases h (pullbackHom a b) hcc with hz | hi
    · left
      apply (pullbackHomEquiv a R R).injective
      exact hz
    · right
      apply (pullbackHomEquiv a R R).injective
      exact hi

theorem pullback_indecomposable_iff (a : GraphIso Q Q') (R : Rep K Q') :
    Indecomposable R ↔ Indecomposable (pullback a R) := by
  rw [indecomposable_iff, indecomposable_iff, pullback_isZero_iff a R,
    pullback_idempotents_iff a R]

/-- Forward transport on isomorphisms. -/
def pullbackIso (a : GraphIso Q Q') {R S : Rep K Q'} (f : Iso R S) :
    Iso (pullback a R) (pullback a S) where
  map v := f.map (a.vertex v)
  comm e := (pullbackHom a f.toHom).comm e

/-- Undo graph reindexing on an actual isomorphism. -/
def unpullbackIso (a : GraphIso Q Q') {R S : Rep K Q'}
    (f : Iso (pullback a R) (pullback a S)) : Iso R S :=
  Iso.ofInverse (unpullbackHom a f.toHom) (unpullbackHom a f.symm.toHom)
    (by
      apply (pullbackHomEquiv a R R).injective
      change pullbackHom a _ = pullbackHom a _
      rw [pullbackHom_comp, pullback_unpullbackHom, pullback_unpullbackHom,
        Iso.symm_comp, pullbackHom_id])
    (by
      apply (pullbackHomEquiv a S S).injective
      change pullbackHom a _ = pullbackHom a _
      rw [pullbackHom_comp, pullback_unpullbackHom, pullback_unpullbackHom,
        Iso.comp_symm, pullbackHom_id])

/-- Conjugation identifies morphisms between isomorphic diagram pairs. -/
def Iso.homCongr {R S R' S' : Rep K Q} (a : Iso R R') (b : Iso S S') :
    Hom R S ≃ Hom R' S' where
  toFun f := b.toHom.comp (f.comp a.symm.toHom)
  invFun f := b.symm.toHom.comp (f.comp a.toHom)
  left_inv f := by
    apply Hom.ext
    intro v
    apply LinearMap.ext
    intro x
    simp [Hom.comp, Iso.toHom, Iso.symm]
  right_inv f := by
    apply Hom.ext
    intro v
    apply LinearMap.ext
    intro x
    simp [Hom.comp, Iso.toHom, Iso.symm]

namespace GraphIso

def refl (Q : Orientation V E) : GraphIso Q Q := ⟨Equiv.refl _, Equiv.refl _, fun _ => rfl, fun _ => rfl⟩

def symm (a : GraphIso Q Q') : GraphIso Q' Q where
  vertex := a.vertex.symm
  edge := a.edge.symm
  source e := by
    apply a.vertex.injective
    simpa using (a.source (a.edge.symm e)).symm
  target e := by
    apply a.vertex.injective
    simpa using (a.target (a.edge.symm e)).symm

def trans (a : GraphIso Q Q') (b : GraphIso Q' Q'') : GraphIso Q Q'' where
  vertex := a.vertex.trans b.vertex
  edge := a.edge.trans b.edge
  source e := by
    change b.vertex (a.vertex (Q.source e)) = _
    rw [a.source, b.source]
    rfl
  target e := by
    change b.vertex (a.vertex (Q.target e)) = _
    rw [a.target, b.target]
    rfl

end GraphIso

theorem Iso.isZero_iff {R S : Rep K Q} (f : Iso R S) : IsZero R ↔ IsZero S := by
  constructor
  · intro h v x
    obtain ⟨y, rfl⟩ := (f.map v).surjective x
    rw [h v y, map_zero]
  · intro h v x
    apply (f.map v).injective
    rw [h v (f.map v x), map_zero]

theorem Iso.indecomposable {R S : Rep K Q} (f : Iso R S) (h : Indecomposable R) :
    Indecomposable S := by
  refine ⟨fun hs => h.1 (f.isZero_iff.mpr hs), ?_⟩
  intro A B g
  exact h.2 A B (f.trans g)

theorem Iso.indecomposable_iff {R S : Rep K Q} (f : Iso R S) :
    Indecomposable R ↔ Indecomposable S := ⟨f.indecomposable, f.symm.indecomposable⟩

section SinkChart
variable [DecidableEq V] [DecidableEq E] (Q : Orientation V E) (s : V)

abbrev AwayVertex := {v : V // v ≠ s}
abbrev SinkAwayEdge := {e : E // Q.target e ≠ s}
abbrev SinkIncident := {e : E // Q.target e = s}

/-- The part of a sink-oriented quiver away from the chosen sink. -/
def sinkPeripheral (hs : Q.IsSink s) : Orientation (AwayVertex s) (SinkAwayEdge Q s) where
  source e := ⟨Q.source e.val, hs e.val⟩
  target e := ⟨Q.target e.val, e.property⟩

def sinkNeighbour (hs : Q.IsSink s) (e : SinkIncident Q s) : AwayVertex s :=
  ⟨Q.source e.val, hs e.val⟩

def chartVertexEquiv : Option (AwayVertex s) ≃ V where
  toFun | none => s | some v => v.val
  invFun v := if h : v = s then none else some ⟨v, h⟩
  left_inv v := by cases v with
    | none => simp
    | some v => simp [v.property]
  right_inv v := by by_cases h : v = s <;> simp [h]

def sinkChartEdgeEquiv : Sum (SinkAwayEdge Q s) (SinkIncident Q s) ≃ E where
  toFun | .inl e => e.val | .inr e => e.val
  invFun e := if h : Q.target e = s then .inr ⟨e, h⟩ else .inl ⟨e, h⟩
  left_inv e := by cases e with
    | inl e => simp [e.property]
    | inr e => simp [e.property]
  right_inv e := by by_cases h : Q.target e = s <;> simp [h]

/-- Every sink has an actual finite-star chart, preserving every graph incidence. -/
def sinkChartGraph (hs : Q.IsSink s) :
    GraphIso (attachSinkOrientation (sinkPeripheral Q s hs) (sinkNeighbour Q s hs)) Q where
  vertex := chartVertexEquiv s
  edge := sinkChartEdgeEquiv Q s
  source e := by cases e <;> rfl
  target e := by cases e with
    | inl e => rfl
    | inr e => exact e.property.symm

/-- The same chart after reversing exactly the incident arrows. -/
def sinkReflectedChartGraph (hs : Q.IsSink s) :
    GraphIso (attachSourceOrientation (sinkPeripheral Q s hs) (sinkNeighbour Q s hs))
      (Q.reflect s) where
  vertex := chartVertexEquiv s
  edge := sinkChartEdgeEquiv Q s
  source e := by
    cases e with
    | inl e =>
      change Q.source e.val = _
      simp [Orientation.reflect, sinkChartEdgeEquiv, hs e.val, e.property]
    | inr e =>
      change s = _
      simp [Orientation.reflect, sinkChartEdgeEquiv, e.property]
  target e := by
    cases e with
    | inl e =>
      change Q.target e.val = _
      simp [Orientation.reflect, sinkChartEdgeEquiv, hs e.val, e.property]
    | inr e =>
      change Q.source e.val = _
      simp [Orientation.reflect, sinkChartEdgeEquiv, e.property]

variable {Q s}

def sinkPeripheralRep (R : Rep K Q) (hs : Q.IsSink s) : Rep K (sinkPeripheral Q s hs) where
  space v := R.space v.val
  arrow e := R.arrow e.val

variable [Fintype E]

noncomputable def sinkIncoming (R : Rep K Q) (hs : Q.IsSink s) :
    Boundary (sinkPeripheralRep R hs) (sinkNeighbour Q s hs) →ₗ[K] R.space s :=
  aggregateIncoming (sinkPeripheralRep R hs) (sinkNeighbour Q s hs)
    (fun e => (vertexCast R e.property).toLinearMap.comp (R.arrow e.val))

/-- The sink chart recovers every original arrow, with no normal-form assumption. -/
noncomputable def sinkChartIso (R : Rep K Q) (hs : Q.IsSink s) :
    Iso (pullback (sinkChartGraph Q s hs) R)
      (attachSink (sinkPeripheralRep R hs) (sinkNeighbour Q s hs) (sinkIncoming R hs)) where
  map v := by cases v <;> exact LinearEquiv.refl K _
  comm e := by
    cases e with
    | inl e => rfl
    | inr e =>
      apply LinearMap.ext
      intro x
      change vertexCast R e.property (R.arrow e.val x) =
        sinkIncoming R hs (Pi.single e x)
      simp only [sinkIncoming, aggregateIncoming, LinearMap.lsum_piSingle,
        LinearMap.comp_apply, LinearEquiv.coe_coe]
      rfl

theorem sinkChart_indecomposable_iff (R : Rep K Q) (hs : Q.IsSink s) :
    Indecomposable R ↔ Indecomposable
      (attachSink (sinkPeripheralRep R hs) (sinkNeighbour Q s hs) (sinkIncoming R hs)) :=
  (pullback_indecomposable_iff (sinkChartGraph Q s hs) R).trans (sinkChartIso R hs).indecomposable_iff

/-- Kernel reflection on the original vertex and edge labels. -/
noncomputable def sinkReflect (R : Rep K Q) (hs : Q.IsSink s) : Rep K (Q.reflect s) :=
  pullback (sinkReflectedChartGraph Q s hs).symm
    (attachSource (sinkPeripheralRep R hs) (sinkNeighbour Q s hs)
      (ReflectionEquivalence.sink (sinkIncoming R hs)))

/-- Reindexing preserves the actual module at every vertex away from the sink. -/
noncomputable def sinkReflectAwayEquiv (R : Rep K Q) (hs : Q.IsSink s)
    (v : V) (hv : v ≠ s) : (sinkReflect R hs).space v ≃ₗ[K] R.space v := by
  exact vertexCast (attachSource (sinkPeripheralRep R hs) (sinkNeighbour Q s hs)
    (ReflectionEquivalence.sink (sinkIncoming R hs)))
    (show (chartVertexEquiv s).symm v = some ⟨v, hv⟩ by simp [chartVertexEquiv, hv])

/-- At the selected vertex the actual new module is the aggregate kernel. -/
noncomputable def sinkReflectCenterEquiv (R : Rep K Q) (hs : Q.IsSink s) :
    (sinkReflect R hs).space s ≃ₗ[K] LinearMap.ker (sinkIncoming R hs) := by
  exact vertexCast (attachSource (sinkPeripheralRep R hs) (sinkNeighbour Q s hs)
    (ReflectionEquivalence.sink (sinkIncoming R hs)))
    (show (chartVertexEquiv s).symm s = none by simp [chartVertexEquiv])

/-- Generic sink reflection preserves indecomposability unless all other vertex
spaces vanish. The required aggregate surjectivity is proved, not assumed. -/
theorem sinkReflect_indecomposable (R : Rep K Q) (hs : Q.IsSink s)
    (hR : Indecomposable R) (v : V) (hv : v ≠ s) [Nontrivial (R.space v)] :
    Indecomposable (sinkReflect R hs) := by
  letI : Nontrivial ((sinkPeripheralRep R hs).space ⟨v, hv⟩) := ‹Nontrivial (R.space v)›
  apply (pullback_indecomposable_iff (sinkReflectedChartGraph Q s hs).symm _).mp
  exact ReflectionEquivalence.attachedSink_reflects_indecomposable
    (sinkPeripheralRep R hs) (sinkNeighbour Q s hs) (sinkIncoming R hs)
    ((sinkChart_indecomposable_iff R hs).mp hR) ⟨v, hv⟩

theorem sinkIncoming_surjective (R : Rep K Q) (hs : Q.IsSink s)
    (hR : Indecomposable R) (v : V) (hv : v ≠ s) [Nontrivial (R.space v)] :
    Function.Surjective (sinkIncoming R hs) := by
  letI : Nontrivial ((sinkPeripheralRep R hs).space ⟨v, hv⟩) := ‹Nontrivial (R.space v)›
  exact ReflectionEquivalence.attachedSink_surjective_of_idempotents
    (sinkPeripheralRep R hs) (sinkNeighbour Q s hs) (sinkIncoming R hs)
    ((sinkChart_indecomposable_iff R hs).mp hR).idempotentsTrivial ⟨v, hv⟩

instance sinkReflect_finite (R : Rep K Q) (hs : Q.IsSink s)
    [∀ v, FiniteDimensional K (R.space v)] (v : V) :
    FiniteDimensional K ((sinkReflect R hs).space v) := by
  letI : ∀ e : SinkIncident Q s, FiniteDimensional K
      ((sinkPeripheralRep R hs).space (sinkNeighbour Q s hs e)) :=
    fun e => inferInstanceAs (FiniteDimensional K (R.space (Q.source e.val)))
  by_cases hv : v = s
  · subst v
    exact (sinkReflectCenterEquiv R hs).symm.finiteDimensional
  · exact (sinkReflectAwayEquiv R hs v hv).symm.finiteDimensional

theorem sinkReflect_finrank_away (R : Rep K Q) (hs : Q.IsSink s) (v : V) (hv : v ≠ s) :
    Module.finrank K ((sinkReflect R hs).space v) = Module.finrank K (R.space v) :=
  (sinkReflectAwayEquiv R hs v hv).finrank_eq

theorem sinkReflect_finrank_center (R : Rep K Q) (hs : Q.IsSink s)
    [∀ v, FiniteDimensional K (R.space v)] (hf : Function.Surjective (sinkIncoming R hs)) :
    Module.finrank K ((sinkReflect R hs).space s) + Module.finrank K (R.space s) =
      ∑ e : SinkIncident Q s, Module.finrank K (R.space (Q.source e.val)) := by
  letI : ∀ e : SinkIncident Q s, FiniteDimensional K
      ((sinkPeripheralRep R hs).space (sinkNeighbour Q s hs e)) :=
    fun e => inferInstanceAs (FiniteDimensional K (R.space (Q.source e.val)))
  rw [(sinkReflectCenterEquiv R hs).finrank_eq]
  exact ReflectionEquivalence.attachedSink_finrank
    (sinkPeripheralRep R hs) (sinkNeighbour Q s hs) (sinkIncoming R hs) hf

end SinkChart

section SourceChart
variable [DecidableEq V] [DecidableEq E] (Q : Orientation V E) (s : V)

abbrev SourceAwayEdge := {e : E // Q.source e ≠ s}
abbrev SourceIncident := {e : E // Q.source e = s}

def sourcePeripheral (hs : Q.IsSource s) : Orientation (AwayVertex s) (SourceAwayEdge Q s) where
  source e := ⟨Q.source e.val, e.property⟩
  target e := ⟨Q.target e.val, hs e.val⟩

def sourceNeighbour (hs : Q.IsSource s) (e : SourceIncident Q s) : AwayVertex s :=
  ⟨Q.target e.val, hs e.val⟩

def sourceChartEdgeEquiv : Sum (SourceAwayEdge Q s) (SourceIncident Q s) ≃ E where
  toFun | .inl e => e.val | .inr e => e.val
  invFun e := if h : Q.source e = s then .inr ⟨e, h⟩ else .inl ⟨e, h⟩
  left_inv e := by cases e with
    | inl e => simp [e.property]
    | inr e => simp [e.property]
  right_inv e := by by_cases h : Q.source e = s <;> simp [h]

def sourceChartGraph (hs : Q.IsSource s) :
    GraphIso (attachSourceOrientation (sourcePeripheral Q s hs) (sourceNeighbour Q s hs)) Q where
  vertex := chartVertexEquiv s
  edge := sourceChartEdgeEquiv Q s
  source e := by cases e with
    | inl e => rfl
    | inr e => exact e.property.symm
  target e := by cases e <;> rfl

def sourceReflectedChartGraph (hs : Q.IsSource s) :
    GraphIso (attachSinkOrientation (sourcePeripheral Q s hs) (sourceNeighbour Q s hs))
      (Q.reflect s) where
  vertex := chartVertexEquiv s
  edge := sourceChartEdgeEquiv Q s
  source e := by
    cases e with
    | inl e =>
      change Q.source e.val = _
      simp [Orientation.reflect, sourceChartEdgeEquiv, hs e.val, e.property]
    | inr e =>
      change Q.target e.val = _
      simp [Orientation.reflect, sourceChartEdgeEquiv, e.property]
  target e := by
    cases e with
    | inl e =>
      change Q.target e.val = _
      simp [Orientation.reflect, sourceChartEdgeEquiv, hs e.val, e.property]
    | inr e =>
      change s = _
      simp [Orientation.reflect, sourceChartEdgeEquiv, e.property]

variable {Q s}

def sourcePeripheralRep (R : Rep K Q) (hs : Q.IsSource s) : Rep K (sourcePeripheral Q s hs) where
  space v := R.space v.val
  arrow e := R.arrow e.val

def sourceOutgoing (R : Rep K Q) (hs : Q.IsSource s) :
    R.space s →ₗ[K] Boundary (sourcePeripheralRep R hs) (sourceNeighbour Q s hs) :=
  LinearMap.pi (fun e => (R.arrow e.val).comp (vertexCast R e.property.symm).toLinearMap)

def sourceChartIso (R : Rep K Q) (hs : Q.IsSource s) :
    Iso (pullback (sourceChartGraph Q s hs) R)
      (attachSource (sourcePeripheralRep R hs) (sourceNeighbour Q s hs) (sourceOutgoing R hs)) where
  map v := by cases v <;> exact LinearEquiv.refl K _
  comm e := by cases e <;> rfl

omit [DecidableEq E] in
theorem sourceChart_indecomposable_iff (R : Rep K Q) (hs : Q.IsSource s) :
    Indecomposable R ↔ Indecomposable
      (attachSource (sourcePeripheralRep R hs) (sourceNeighbour Q s hs) (sourceOutgoing R hs)) :=
  (pullback_indecomposable_iff (sourceChartGraph Q s hs) R).trans (sourceChartIso R hs).indecomposable_iff

/-- Cokernel reflection on the original vertex and edge labels. -/
noncomputable def sourceReflect (R : Rep K Q) (hs : Q.IsSource s) : Rep K (Q.reflect s) :=
  pullback (sourceReflectedChartGraph Q s hs).symm
    (attachSink (sourcePeripheralRep R hs) (sourceNeighbour Q s hs)
      (ReflectionEquivalence.source (sourceOutgoing R hs)))

noncomputable def sourceReflectAwayEquiv (R : Rep K Q) (hs : Q.IsSource s)
    (v : V) (hv : v ≠ s) : (sourceReflect R hs).space v ≃ₗ[K] R.space v := by
  exact vertexCast (attachSink (sourcePeripheralRep R hs) (sourceNeighbour Q s hs)
    (ReflectionEquivalence.source (sourceOutgoing R hs)))
    (show (chartVertexEquiv s).symm v = some ⟨v, hv⟩ by simp [chartVertexEquiv, hv])

noncomputable def sourceReflectCenterEquiv (R : Rep K Q) (hs : Q.IsSource s) :
    (sourceReflect R hs).space s ≃ₗ[K]
      (Boundary (sourcePeripheralRep R hs) (sourceNeighbour Q s hs) ⧸
        LinearMap.range (sourceOutgoing R hs)) := by
  exact vertexCast (attachSink (sourcePeripheralRep R hs) (sourceNeighbour Q s hs)
    (ReflectionEquivalence.source (sourceOutgoing R hs)))
    (show (chartVertexEquiv s).symm s = none by simp [chartVertexEquiv])

variable [Fintype E]

theorem sourceReflect_indecomposable (R : Rep K Q) (hs : Q.IsSource s)
    (hR : Indecomposable R) (v : V) (hv : v ≠ s) [Nontrivial (R.space v)] :
    Indecomposable (sourceReflect R hs) := by
  letI : Nontrivial ((sourcePeripheralRep R hs).space ⟨v, hv⟩) := ‹Nontrivial (R.space v)›
  apply (pullback_indecomposable_iff (sourceReflectedChartGraph Q s hs).symm _).mp
  exact ReflectionEquivalence.attachedSource_reflects_indecomposable
    (sourcePeripheralRep R hs) (sourceNeighbour Q s hs) (sourceOutgoing R hs)
    ((sourceChart_indecomposable_iff R hs).mp hR) ⟨v, hv⟩

omit [Fintype E] [DecidableEq E] in
theorem sourceOutgoing_injective (R : Rep K Q) (hs : Q.IsSource s)
    (hR : Indecomposable R) (v : V) (hv : v ≠ s) [Nontrivial (R.space v)] :
    Function.Injective (sourceOutgoing R hs) := by
  letI : Nontrivial ((sourcePeripheralRep R hs).space ⟨v, hv⟩) := ‹Nontrivial (R.space v)›
  exact ReflectionEquivalence.attachedSource_injective_of_idempotents
    (sourcePeripheralRep R hs) (sourceNeighbour Q s hs) (sourceOutgoing R hs)
    ((sourceChart_indecomposable_iff R hs).mp hR).idempotentsTrivial ⟨v, hv⟩

instance sourceReflect_finite (R : Rep K Q) (hs : Q.IsSource s)
    [∀ v, FiniteDimensional K (R.space v)] (v : V) :
    FiniteDimensional K ((sourceReflect R hs).space v) := by
  letI : ∀ e : SourceIncident Q s, FiniteDimensional K
      ((sourcePeripheralRep R hs).space (sourceNeighbour Q s hs e)) :=
    fun e => inferInstanceAs (FiniteDimensional K (R.space (Q.target e.val)))
  by_cases hv : v = s
  · subst v
    exact (sourceReflectCenterEquiv R hs).symm.finiteDimensional
  · exact (sourceReflectAwayEquiv R hs v hv).symm.finiteDimensional

omit [Fintype E] in
theorem sourceReflect_finrank_away (R : Rep K Q) (hs : Q.IsSource s) (v : V) (hv : v ≠ s) :
    Module.finrank K ((sourceReflect R hs).space v) = Module.finrank K (R.space v) :=
  (sourceReflectAwayEquiv R hs v hv).finrank_eq

theorem sourceReflect_finrank_center (R : Rep K Q) (hs : Q.IsSource s)
    [∀ v, FiniteDimensional K (R.space v)] (hg : Function.Injective (sourceOutgoing R hs)) :
    Module.finrank K ((sourceReflect R hs).space s) + Module.finrank K (R.space s) =
      ∑ e : SourceIncident Q s, Module.finrank K (R.space (Q.target e.val)) := by
  letI : ∀ e : SourceIncident Q s, FiniteDimensional K
      ((sourcePeripheralRep R hs).space (sourceNeighbour Q s hs e)) :=
    fun e => inferInstanceAs (FiniteDimensional K (R.space (Q.target e.val)))
  rw [(sourceReflectCenterEquiv R hs).finrank_eq]
  exact ReflectionEquivalence.attachedSource_finrank
    (sourcePeripheralRep R hs) (sourceNeighbour Q s hs) (sourceOutgoing R hs) hg

end SourceChart

/-- The only support is at one named vertex. -/
def SupportedAt (R : Rep K Q) (s : V) : Prop := ∀ v, v ≠ s → ∀ x : R.space v, x = 0

def VertexSimple (R : Rep K Q) (s : V) : Prop :=
  SupportedAt R s ∧ Module.finrank K (R.space s) = 1

theorem exists_nonzero_away {R : Rep K Q} {s : V} (h : ¬ SupportedAt R s) :
    ∃ v, v ≠ s ∧ Nontrivial (R.space v) := by
  classical
  unfold SupportedAt at h
  push_neg at h
  obtain ⟨v, hv, x, hx⟩ := h
  exact ⟨v, hv, ⟨⟨x, 0, hx⟩⟩⟩

section Steps
variable [DecidableEq V] [DecidableEq E] [Fintype E] {s : V}

theorem sink_simple_of_supported (R : Rep K Q) (hs : Q.IsSink s)
    (hR : Indecomposable R) (hp : SupportedAt R s) : VertexSimple R s := by
  refine ⟨hp, ?_⟩
  exact ReflectionEquivalence.attachedSink_simple_exception
    (sinkPeripheralRep R hs) (sinkNeighbour Q s hs) (sinkIncoming R hs)
    ((sinkChart_indecomposable_iff R hs).mp hR)
    (fun v x => hp v.val v.property x)

omit [Fintype E] [DecidableEq E] in
theorem source_simple_of_supported (R : Rep K Q) (hs : Q.IsSource s)
    (hR : Indecomposable R) (hp : SupportedAt R s) : VertexSimple R s := by
  refine ⟨hp, ?_⟩
  exact ReflectionEquivalence.attachedSource_simple_exception
    (sourcePeripheralRep R hs) (sourceNeighbour Q s hs) (sourceOutgoing R hs)
    ((sourceChart_indecomposable_iff R hs).mp hR)
    (fun v x => hp v.val v.property x)

theorem sink_step (R : Rep K Q) (hs : Q.IsSink s) (hR : Indecomposable R) :
    VertexSimple R s ∨
      (Indecomposable (sinkReflect R hs) ∧ Function.Surjective (sinkIncoming R hs)) := by
  classical
  by_cases hp : SupportedAt R s
  · exact Or.inl (sink_simple_of_supported R hs hR hp)
  · obtain ⟨v, hv, hn⟩ := exists_nonzero_away hp
    letI := hn
    exact Or.inr ⟨sinkReflect_indecomposable R hs hR v hv, sinkIncoming_surjective R hs hR v hv⟩

theorem source_step (R : Rep K Q) (hs : Q.IsSource s) (hR : Indecomposable R) :
    VertexSimple R s ∨
      (Indecomposable (sourceReflect R hs) ∧ Function.Injective (sourceOutgoing R hs)) := by
  classical
  by_cases hp : SupportedAt R s
  · exact Or.inl (source_simple_of_supported R hs hR hp)
  · obtain ⟨v, hv, hn⟩ := exists_nonzero_away hp
    letI := hn
    exact Or.inr ⟨sourceReflect_indecomposable R hs hR v hv, sourceOutgoing_injective R hs hR v hv⟩

/-- Full morphism equivalence for sink reflections in the original vertex labels. -/
noncomputable def sinkReflectHomEquiv (R S : Rep K Q) (hs : Q.IsSink s)
    (hR : Function.Surjective (sinkIncoming R hs))
    (hS : Function.Surjective (sinkIncoming S hs)) :
    Hom R S ≃ Hom (sinkReflect R hs) (sinkReflect S hs) :=
  (pullbackHomEquiv (sinkChartGraph Q s hs) R S).trans
    (((sinkChartIso R hs).homCongr (sinkChartIso S hs)).trans
      ((ReflectionEquivalence.attachedSinkHomEquiv hR hS).trans
        (pullbackHomEquiv (sinkReflectedChartGraph Q s hs).symm _ _)))

noncomputable def sourceReflectHomEquiv (R S : Rep K Q) (hs : Q.IsSource s)
    (hR : Function.Injective (sourceOutgoing R hs))
    (hS : Function.Injective (sourceOutgoing S hs)) :
    Hom R S ≃ Hom (sourceReflect R hs) (sourceReflect S hs) :=
  (pullbackHomEquiv (sourceChartGraph Q s hs) R S).trans
    (((sourceChartIso R hs).homCongr (sourceChartIso S hs)).trans
      ((ReflectionEquivalence.attachedSourceHomEquiv hR hS).trans
        (pullbackHomEquiv (sourceReflectedChartGraph Q s hs).symm _ _)))

/-- Reverse uniqueness: isomorphic reflected sink objects imply isomorphic
original objects under the actual local surjectivity hypotheses. -/
noncomputable def sinkUnreflectIso (R S : Rep K Q) (hs : Q.IsSink s)
    (hR : Function.Surjective (sinkIncoming R hs))
    (hS : Function.Surjective (sinkIncoming S hs))
    (f : Iso (sinkReflect R hs) (sinkReflect S hs)) : Iso R S :=
  unpullbackIso (sinkChartGraph Q s hs)
    ((sinkChartIso R hs).trans
      ((ReflectionEquivalence.unreflectAttachedSinkIso hR hS
        (unpullbackIso (sinkReflectedChartGraph Q s hs).symm f)).trans (sinkChartIso S hs).symm))

noncomputable def sourceUnreflectIso (R S : Rep K Q) (hs : Q.IsSource s)
    (hR : Function.Injective (sourceOutgoing R hs))
    (hS : Function.Injective (sourceOutgoing S hs))
    (f : Iso (sourceReflect R hs) (sourceReflect S hs)) : Iso R S :=
  unpullbackIso (sourceChartGraph Q s hs)
    ((sourceChartIso R hs).trans
      ((ReflectionEquivalence.unreflectAttachedSourceIso hR hS
        (unpullbackIso (sourceReflectedChartGraph Q s hs).symm f)).trans (sourceChartIso S hs).symm))

end Steps

end UploadBroadcast.QuiverRepresentation
