# Simultaneous subspace decomposition and finite-copy descent

## Checked implementation

`UploadBroadcast/TaskDecomposition.lean` treats a labeled family of subspaces
of a finite-dimensional vector space, specialized to the manuscript's three
nested pairs `A i ≤ U i`. A `Split` is a disjoint ambient sum that splits every
labeled space by intersection. `Decomposition` is a finite binary certificate
whose nonzero leaves have no nontrivial simultaneous split.

`exists_decomposition` is unconditional: strong induction on ambient component
finrank strictly decreases at every nontrivial split. `finite_components`
extracts a finite list of indecomposable components, their ambient sum,
all six space sums, and equality of the sum of dimensions with ambient
dimension. Ambient and labeled-space dimension additivity and task excess
additivity are checked separately.

`UploadBroadcast/StableEnd.lean` defines the actual subring of endomorphisms
preserving every labeled space. The proof chain is:

1. A stable idempotent gives a simultaneous kernel/range split.
2. Indecomposability forces stable idempotents to be zero or identity.
3. Over a finite field, the stable endomorphism ring is finite.
4. The finite-monoid positive-idempotent-power theorem in
   `FiniteMonoidPower.lean` makes every stable endomorphism nilpotent or a unit.
5. Geometric-sum inversion of one minus a nilpotent proves the ring local.
6. A unit finite sum in a noncommutative local ring has a unit summand.
7. A nonzero retract of an indecomposable configuration is isomorphic to it.

`iso_of_sum_factorizations` proves that if `id_S = Σ g_j ∘ f_j`, with all
maps preserving labels and both configurations indecomposable, then `S ≅ T`.
`iso_of_retract_copies` packages this as the exact special Krull–Schmidt step
needed by the manuscript: an indecomposable retract of finitely many copies
of one indecomposable finite-field configuration is isomorphic to that
configuration. These theorems do not assume Krull–Schmidt, localness, or the
requested isomorphism as hypotheses.

Audits: `verification/TaskDecompositionAxioms.lean` and
`verification/StableEndAxioms.lean`. The audited results use only the standard
Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Boundaries

This is not a proof of full Krull–Schmidt uniqueness for arbitrary lists of
pairwise different summands. The special finite-copy theorem is sufficient
for the uniqueness step in the displayed manuscript descent argument.

The following representation-theoretic dependencies still require genuine
proofs and are not consequences of the numerical root classification:

- Scalar extension to a finite splitting field into absolutely indecomposable
  summands, with inheritance of injective arrows and spanning side spaces.
- Kac's theorem identifying dimensions of absolutely indecomposables as
  positive roots and, for this affine quiver, proving Tits value zero or one.
- Existence and uniqueness over finite fields of the absolutely
  indecomposable representation associated with each real root.
- The scalar-restriction identifications and summand transport producing the
  finite-copy retraction to which `iso_of_retract_copies` applies.

The last step is linear-algebraic transport infrastructure. The Kac statements
are substantial mathematical foundations and cannot be replaced by a
hypothesis that a desired vector already has Tits value one.
