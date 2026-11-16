# Original-field components: source mapping and verification

Frozen source: `../source/TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.
The reviewed statement is `lem:base-field-components`, beginning at line 2330,
label at line 2331, mathematical statement at lines 2332–2336.

## Complete endpoint

`UploadBroadcast.TaskDecomposition.Task.source_base_field_components`

For every finite field K and finite-dimensional ambient K-vector space V,
the endpoint takes exactly the original nested three-arm task, genuine
representation indecomposability, spanning sides, and positive integer excess.
For an arbitrary extension field L it proves all three conclusions:

1. The literal vertexwise tensor extension of the representation is indecomposable.
2. Its original dimension vector is a real root, defined as the Weyl orbit of
   a simple root under the actual affine E6 integral simple reflections.
3. Its original Tits value is one.

The extension has no finiteness, finite-degree, algebraic-closure, or chosen
splitting-field assumption. Because L and its field/algebra structures are
arbitrary theorem parameters, item 1 establishes absolute indecomposability,
including extension to an algebraic closure.

## Hypothesis-by-hypothesis source correspondence

- `K` has `Field K` and `Finite K`: this is the source's finite field k=F_q,
  without choosing a particular presentation of a finite field.
- `T : TaskDecomposition.Task K V` contains the actual submodules A_i and U_i
  and the proofs A_i≤U_i, indexed by `Fin 3`. `Task.toRep` has V at the central
  vertex, U_i at the middle vertices, and A_i at the outer vertices. The
  arrows are the submodule inclusions, so they are injective by construction.
  This matches the source's displayed representation `(A_i ⊆ U_i ⊆ F)`.
- The input is `QuiverRepresentation.Indecomposable T.toRep`. Its definition
  requires a nonzero representation and rules out every nontrivial actual
  product decomposition. `Task.toRep_indec_iff` proves equivalence with
  simultaneous internal splitting of all six designated subspaces.
- `(T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤` is precisely F=Σ_i A_i.
- `Structural.excess T.dimensionVector.f ... > 0` is exactly the integer
  Σ_i dim A_i−dim F>0. The dimension vector is formed from the actual module
  dimensions. The alternative `positive_excess_*` APIs use the equivalent
  natural-number inequality dim F<Σ_i dim A_i.
- There is no active-demand assumption. In particular, the passive tripod
  with A_i=U_i is retained and proved absolutely indecomposable.
- No cross-transversality, prescribed dimension vector, root bound, normal
  form, scalar endomorphism condition, or extension-splitting oracle is an input.

Finite-dimensionality makes explicit the finite-dimensional representation
convention already implicit in the source's finite dimension vector.

## Absolute indecomposability is genuinely tensorial

`TensorTaskExtension.lean` defines `Task.tensorRep L` with the literal modules
L⊗_K M_v at every vertex and the literal tensor-extended maps on every arrow.
It proves injectivity of tensor-extended subspace inclusions over arbitrary
extensions by extending an actual linear left inverse.

`subspaceTensorEquiv` identifies L⊗_K P with P.baseChange L, and its ambient
inclusion is exactly the tensor-extended original inclusion.
`Task.tensorRepIso` assembles these vertex maps into an explicit
arrow-commuting representation isomorphism from `Task.tensorRep L` to
`(Task.extend).toRep`. `Task.tensorRep_indec_iff` then proves exact equivalence
of the two indecomposability formulations. Thus the main result is not just
about unchanged field dimensions or a newly chosen model over L.

For nonzero defect, `Task.nonzero_defect_extend_indec` applies the proved
reflection/scalar-endomorphism argument to the actual six subspaces.
For zero defect, `RegularResonantClassification.classification` derives an
actual label-preserving isomorphism to the passive tripod or a canonical
resonant block from the source hypotheses. `ConfigurationIso.baseChange`
extends this actual isomorphism; it does not substitute a dimension equality.
The canonical resonant block uses the explicit tensor naturality theorem in
`ResonantBaseChange.lean`. The passive branch derives scalar endomorphisms
from its three distinct lines and applies arbitrary-extension scalar-end
indecomposability. `graph_extend_indec_of_six` checks the precise six labels
when moving between the Fin 6 and Fin 3 × Bool presentations.

## Real roots are not defined to mean Tits value one

`E6RealRoots.IsRealRoot` is generated from the seven coordinate simple roots
by `E6Reflection.reflectDimension`: at vertex s this replaces d_s with
Σ_{v adjacent s} d_v−d_s, and fixes every other coordinate. These are exactly
the simple reflections for the affine E6 Cartan matrix with diagonal 2,
off-diagonal −1 on the six diagram edges, and zero elsewhere. The definition
contains no Tits equation.

`E6RealRoots.nonnegative_realRoot_iff_norm_one` proves the required equivalence
for nonnegative integral vectors. Its proof establishes:

- positive semidefiniteness by the denominator-free seven-square identity;
- the norm-zero kernel consists precisely of integral multiples of δ;
- a norm-zero vector with any zero coordinate is zero;
- reflection preserves norm and is involutive;
- a norm-one nonnegative vector has a positive Cartan gradient;
- if reflection would produce a negative coordinate, the original vector
  was already the corresponding simple root;
- otherwise reflection preserves nonnegativity and strictly lowers the
  sum of coordinates, giving a terminating induction to a simple root.

This handles zero defect as well as nonzero defect. The source endpoint
applies it to the actual, automatically nonnegative representation dimensions.
The separate `positive_excess_real_root` API exposes this conclusion directly.

The proof is an alternative to the source's splitting-field/Kac-uniqueness/
Krull–Schmidt route. Those external assertions are not assumptions or custom
axioms of the formal endpoint.

## Mechanical evidence and coverage decision

- `lake build UploadBroadcast.BaseFieldComponents` builds all three new
  modules and their dependencies; log: `logs/base-field-components-lake.log`.
- `verification/BaseFieldComponentsAudit.lean` independently checks the full
  source-shaped signature and audits the transitive reachable axioms for
  the endpoint, tensor bridge, root equivalence, and component wrapper.
  Log: `logs/base-field-components-axioms.log`.
- Allowed reachable axioms are only `propext`, `Classical.choice`, and
  `Quot.sound`. No admitted proof, custom axiom, native evaluation escape,
  or target-as-premise shortcut is used.
- The new modules are included in `UploadBroadcast.lean` for the final
  integrated build and repository-wide audit.

With both literal tensor-extension indecomposability and genuine Weyl real-root
membership compiled and checked, `lem:base-field-components` can be marked
`reviewed_complete`. This promotes only this named source claim. It does not
assert full-paper verification or completion of unrelated current work.
