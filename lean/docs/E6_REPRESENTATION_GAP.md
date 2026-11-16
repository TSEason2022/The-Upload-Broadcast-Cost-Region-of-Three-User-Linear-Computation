# Affine E6 representation-theory boundary

**Historical/module-local development note.** This records the boundary of the intermediate modules at the time it was written. Statements below about remaining work are not the current project-wide gap list. For the subsequent source-facing classification, see `base-field-components-semantic-audit-20261008.md` and `resonant-classification-status.md`. Current completion status is governed by `../coverage.json`, `../README.md`, and the final frozen-source verification report.

## Verified new reduction

`UploadBroadcast/ReflectionReduction.lean` uses integral dimension vectors in
order `(f; u1,u2,u3; a1,a2,a3)` for the orientation `A_i → U_i → F`.
It proves, without any representation-classification hypotheses:

* The full sink sequence (center, middles, outers) and full source sequence
  (outers, middles, center) are inverse transformations.
* Both preserve the Tits form and the affine defect
  `d = -3f + sum u_i + sum a_i`.
* Six sink sequences give `x + d δ`; six source sequences give `x - d δ`.
* The corresponding n-block formulas hold for every natural n.
* If d is positive, some source block has negative central coordinate. If d is
  negative, some sink block has negative central coordinate.
* At d = 0 both six-cycle transformations are the identity.
* The resonant vector `(3n+2; 2n+1,2n+1,2n+1; n+1,n+1,n+1)` has
  d = 0, Tits value 1, and positive excess 1.

These are dimension-level facts, not construction of reflection functors and
not proof that a representation is a real root. In particular, nonnegative
coordinates alone do not certify that an arbitrary list of reflected linear
maps has the asserted dimensions.

## A non-axiomatic route and its exact remaining obligations

The most economical specialized replacement for general Kac has two branches.

1. Define representations of all orientations of this seven-vertex tree,
   their morphisms, and vertexwise scalar extension. Identify the existing
   nested-subspace configuration category with the injective-arrow part of
   this category; prove equivalence of both indecomposability predicates.
2. At a sink use the kernel of the direct-sum incoming map, at a source the
   cokernel of the outgoing map. Prove that a non-simple indecomposable has
   the needed surjective/injective map, the opposite reflection recovers it,
   and reflection preserves indecomposability and scalar extension.
3. For nonzero defect the verified termination calculation forces a simple
   exception. Reverse the actual equivalences from that one-dimensional
   vertex-simple representation. This proves absolute indecomposability,
   Tits value 1, and uniqueness over the original field for this branch;
   merely tracking dimension vectors is insufficient.
4. Zero defect requires an additional classification, not further cycles of
   the same algorithm. Construct a normal-form equivalence for the relevant
   regular representations, identify which indecomposables satisfy the
   injective-arrow and spanning requirements, and prove that positive excess
   forces the resonant family over the original field. Proving that each
   displayed resonant model is indecomposable is only the forward direction;
   it does not prove that every eligible representation has that model.
5. To recover the manuscript's chosen canonical forms in the nonzero-defect
   branch, prove their actual indecomposability and match their dimensions,
   then apply the uniqueness proved in step 3. Numeric membership in a table
   does not supply this isomorphism.

This route avoids finite absolute splitting and finite-field real-root descent
for the nonzero-defect branch. It does not yet replace them for the whole
lemma. The existing finite-field descent theorem correctly proves a different
step: descent once an actual suitable extended retract has been supplied.

## What the representation APIs now establish

`QuiverRepresentation.lean` and `ReflectionEquivalence.lean` now implement actual
arbitrary-orientation module representations, their morphisms, vertexwise
sums, kernel/cokernel reflection, inverse isomorphisms, and preservation of
actual indecomposability. The exceptional supported simple objects and the
surjectivity/injectivity conditions are proved. Thus steps 1–2 above have a
substantial generic implementation; the nested-flag interface and actual E6
chart iteration remain integration obligations.

`ResonantBaseChange.lean` identifies all six tensor-extended subspaces with the
same model over the extension field and proves absolute indecomposability.
`MarkedNilpotent.lean` constructs an actual single-chain basis from marked
indecomposability. `ResonantClassification.lean` uses it to classify already
normalized graph configurations via an explicit observability equivalence.
Neither result yet shows that arbitrary eligible flags have the required
cross-intersection transversality and hence admit that graph presentation.

`RootClassification` still takes Tits value 1 as a hypothesis. The actual
representation-to-root/uniqueness bridge is not obtained by substituting a
numeric table entry. Finite-field descent proves descent of a supplied
extended retract, not the existence of such a retract. No unproved
classification principle is added as an axiom.

## Source guidance

William Crawley-Boevey, *Lectures on Representations of Quivers*:
https://www.math.uni-bielefeld.de/~wcrawley/quivlecs.pdf
Sections 7–9 separately treat preprojective/preinjective and regular modules.
The notes fix an algebraically closed ground field at their beginning, so
citing their classification does not itself give an original-finite-field
Lean theorem. Their introduction explicitly uses Auslander–Reiten methods
rather than reflection functors. The dimension calculations above are
independently verified in Lean, not imported from these notes.

## Status

The positive-excess base-field-components lemma and the complete canonical-form
classification remain open. This file must not be counted as verifying those
manuscript claims. No `E6Representation` theorem claiming otherwise is added.

## Checks run on 2026-10-08

* `lake build UploadBroadcast.ReflectionReduction`: success, no warnings.
* `lake env lean scripts/AuditReflectionReduction.lean`: 32 namespace theorems
  (including generated equations/extensionality) passed the allowed-axiom check.
* `python3 scripts/audit_source.py`: success across 80 Lean files at check time.

Logs are `logs/reflection-reduction-build.log`,
`logs/reflection-reduction-axioms.log`, and
`logs/reflection-reduction-source-audit.log`. This is a module-level check;
whole-project integration remains the parent build's responsibility.
