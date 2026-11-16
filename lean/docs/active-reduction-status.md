# Active reduction: checked scope and remaining dependencies

**Historical/module-local development note.** This records the boundary of the intermediate modules at the time it was written. Statements below about remaining work are not the current project-wide gap list. For the later source-facing construction and review, see `active-reduction-source-audit-20261008.md`. Current completion status is governed by `../coverage.json`, `../README.md`, and the final frozen-source verification report.

Source: `prop:active-pair`, `lem:active-empty-row`, equations `graph-data`,
`upload-matrices`, and Appendix A's coordinate-invariance discussion.

## Proved, with actual code semantics

`PassiveCode.lean` constructs `Task.Code` transports for a split linear
ambient projection whose removed demand coefficients are locally known.
The structure contains only coefficient-space linear maps and equalities;
it contains no coding or rate-region conclusion. The constructor
`passiveRetractionOfProjection` builds it from ambient maps and subspace
containments.

* `PassiveRetraction.delete` fixes the removed source symbols to zero.
* `PassiveRetraction.restore` ignores them in uploads and adds their locally
  known values back at each decoder.
* Both preserve zero error for arbitrary nonlinear encoders, relay, and
  decoders; no finite-dimensional or finite-field assumptions are needed
  for these code constructions.
* Range-containment lemmas control both upload alphabets and the attainable
  broadcast alphabet. Over a finite field in finite dimension,
  `PassiveRetraction.achievableAt_eq` proves equality at every blocklength,
  and `costRegion_eq` proves equality of regularized regions.
* `sideOnlyDirectSumRetraction` constructs the maps for an actual task
  direct sum. `sideOnly_achievableAt_eq` therefore proves deletion of ANY
  side-only summand (including passive pair/private/tripod summands once
  their algebraic separation has been established).

## Proved algebraic constituents

`ActiveReduction.lean` proves:

* `squareZeroShear`: the invertible map I-N with inverse I+N.
* `sum_square_zero`, `corrections_annihilate`, and
  `simultaneous_shear_preserves`: actual simultaneous shear and exact
  preservation of every invariant side subspace.
* `active_pair_graph`: for D <= K x Y, construct the graph correction into
  a chosen passive complement of D intersect K. The demand condition is
  equivalent to k-psi(y) being active and y being in the projection of D.
* `active_pair_separation`: the shear sends D exactly to the product of
  its active pair subspace and its projected remaining demand subspace.
* `graph_data_map`: the tripod part modulo the PURE demand space gives a
  well-defined linear function of the private part. The pure space is
  explicitly the comap along the tripod inclusion, hence the intersection,
  and is not confused with the projected tripod demands.
* `cancel_passive_projection`, `cancel_idempotent_projection`: actual
  factorization and elimination of a passive projection annihilating G(ker B).
* `tripod_coordinate_rigidity`: a linear map preserving the v, r, and r-v
  sides acts by one common row map on the two tripod copies.
* `obstruction_gauge_eq`, `mixed_rank_gauge_invariant`,
  `common_rank_basis_invariant`, and `private_gauge_signs`: map/rank
  invariance and the exact signs of the private-coordinate gauge correction.

## Not yet proved as a single source theorem

Neither full `prop:active-pair` nor full `lem:active-empty-row` is claimed
complete. Remaining prerequisites and assembly are:

1. Construct the arbitrary three-subspace decomposition (after quotienting
   the common intersection), including pair/private/tripod coordinates.
2. Identify the active dimensions with the original modular quotient ranks.
3. Lift all three quotient shears simultaneously into that constructed
   ambient decomposition and instantiate the preservation hypotheses.
4. Construct and lift the pure-span/obstruction-range complements; identify
   the separated passive tripod summand in the resulting task and invoke
   the operational deletion theorem.
5. Prove full invariance of all six dimension parameters between arbitrary
   normal-form choices, including source basis changes on ker B and private
   projection ranks. The proven gauge/common-basis identities are pieces
   of this proof, not a substitute for it.

No theorem in these modules assumes the desired region equality, active
normal form, or upload formula as a structure field. Verification file
`verification/ActiveReductionAxioms.lean` audits the named results.
