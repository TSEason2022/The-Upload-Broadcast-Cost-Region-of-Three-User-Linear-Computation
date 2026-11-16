# Finite-field descent: verified bridge and remaining dependencies

**Historical/module-local development note.** This records the boundary of the intermediate modules at the time it was written. Statements below about remaining work are not the current project-wide gap list. The finite-field descent API remains conditional on the explicitly listed summand data. For the subsequent complete source-facing classification route, see `base-field-components-semantic-audit-20261008.md`. Current completion status is governed by `../coverage.json`, `../README.md`, and the final frozen-source verification report.

The modules `ScalarExtensionConfiguration.lean` and `FiniteFieldDescent.lean`
formalize the actual tensor-product transport required in the proof of
`lem:base-field-components` (the positive-excess component lemma).

## Verified statements

- Extend each labeled subspace using Mathlib's `Submodule.baseChange` in
  `L ⊗[K] V`; nesting and configuration-preserving linear maps are preserved.
- The extended subspace is exactly the range of the tensor-extended inclusion.
- Given a finite basis of `L/K`, a tensor is in the extended subspace if and
  only if every restriction-of-scalars coordinate is in the original subspace.
- Consequently the restricted configuration is isomorphic, with all labels,
  to the corresponding finite family of copies of the original configuration.
- Scalar extension preserves sums, intersections, simultaneous splits,
  injectivity, and designated dimensions.
- An actual simultaneous internal split supplies a projection preserving all
  designated subspaces, as well as its actual inclusion and retraction identity.
- `iso_of_extended_summand` proves that if a simultaneous summand of `T_L` is
  isomorphic to `S_L`, and `S,T` are ground-field indecomposable configurations,
  then `S` and `T` are isomorphic. The ground field is finite and the extension
  is finite-dimensional. This uses the finite-copy Krull–Schmidt result proved
  in `StableEnd.lean`, not an assumed uniqueness principle.

The final theorem's summand and isomorphism are explicit hypotheses. It does
not assert their existence, and therefore does not by itself prove the
manuscript's positive-excess lemma.

## Dependencies still needed for the manuscript argument

1. A finite extension over which a finite-dimensional configuration decomposes
   into absolutely indecomposable configurations.
2. A representation-theoretic result that the dimension vector of an absolutely
   indecomposable inward affine-E6 representation is a positive root, and hence
   has Tits value zero or one. Numeric properties of roots alone do not supply
   this implication.
3. Existence and uniqueness over each finite field of an absolutely
   indecomposable representation of each real root, including compatibility
   under field extension. This produces the ground-field configuration `S`
   required in `iso_of_extended_summand`.
4. Transfer of absolute indecomposability and dimension-vector properties along
   the resulting configuration isomorphism.

Search of the pinned Mathlib representation/category-theory sources found no
Kac theorem, relevant Gabriel classification, reflection-functor development,
or absolute-indecomposability API providing (1)–(3). The similarly named
Gabriel–Popescu theorem is unrelated. An E6-specific constructive alternative
would require proving appropriate reflection functors or a complete
configuration normal-form theorem with existence and uniqueness. Neither is
implied by the separately verified numerical root classification.

No missing dependency above has been introduced as an axiom or disguised as
an unconditional paper theorem.
