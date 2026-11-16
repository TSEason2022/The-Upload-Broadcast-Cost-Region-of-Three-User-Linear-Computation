# Binary relay constructions and original-field R2 wedge

These files prove the relay-level portions of manuscript lemmas
`binary-menu` and `binary-additional-menus`, plus integral charged-menu
packing used in `binary-integer-relay`.

## Actual-family endpoints

All of these use the original `Task`, its actual simultaneous-subspace
indecomposability, and `NonzeroFamilyRanks.Dimensions`. They do not assume
an induced profile or an open-orbit specialization.

- `NonzeroBinaryMenus.full_binary_menu`: every canonical T1/O and additional
  R0/T2/R1/T3/H menu choice. Actual feasible, locally generated hyperplane;
  exact dimension; six first-entry bounds; all nine second entries unchanged.
- `NonzeroBinaryMenus.full_extra_menu_fits`: actual scalar choice fitting an
  integer reservation paying the additional component's charge.
- `R2PermutedMenus.full_binary_R2_menu`: all six literal directed-path menu
  members on the same task.
- `R2PermutedMenus.full_binary_R2_fits_capacity`: actual R2 relay fitting any
  integer capacity vector with at least one unit in each opposite pair.
- `NonzeroExceptionalRelays.full_small_exception_profile`: H+delta and
  R2+delta, dimension-two relays, no increased profile entry.
- `NonzeroExceptionalRelays.full_tripod_exception_profile`: T3+delta,
  dimension-four relay, no increased profile entry.
- `NonzeroR2Wedge.full_relationWedge_nonzero`: actual R2 wedge nonvanishing
  over the original field from its relation dimension, injective projections,
  remote-intersection ranks, and joint separation.
- `R2ExactProfile.full_R2_profile_and_upload`: q >= 3 profile-preserving R2
  relay with exact dimension and exact sum of local upload dimensions.

The exceptional-relay proofs construct scalar broadcasts of the common line
or plane. Their all-fifteen bounds use the already proved operational
broadcast converse. The original exceptional profiles are derived from the
original-space rank formulas before proving nonincrease.

## General original-field ingredients

`BinaryRelayMenus` proves two-subspace avoidance, annihilator selection,
actual hyperplane and codimension-two relay existence, exact dimensions,
and remote conditional-rank transport. `BinaryRelayProfiles` and
`BinaryCodimTwoProfiles` prove the actual span identities and full profile
transport. These work over every field, without an extension-field choice.

`TaskUserPermutation` transports indecomposability under actual user
relabeling. `R2PermutedMenus` checks the coordinate permutations against all
six literal table generators, avoiding any assumed symmetry isomorphism.

## Integer allocation

`BinaryMenuAllocation` proves every additional menu's scalar integer fitting,
charge domination by its computed profile margins, and finite simultaneous
integer packing. `BinaryAugmentedAllocation` proves resonant-first selection
and finite charged-menu assembly under the repaired orientation constraints
and strengthened opposite-pair constraints.

This numerical assembly does not itself construct a relay for an arbitrary
undecomposed global task. Global source classification, actual component
assembly, cycle-repair bookkeeping, and connection to the operational upload
optimum must be supplied by the global theorem. This distinction is preserved
in the theorem statements.

## Verification

Run `source scripts/env.sh` before the Lean commands. The dedicated transitive
audit is `lake env lean scripts/AuditBinaryRelays.lean`. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. The root module and coverage
registry are maintained separately; these files do not edit them.
