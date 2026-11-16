# Literal menu and residue table review, 2026-10-08

## Scope and result

The literal rows, parameter boundaries, field restrictions, profile-coordinate order,
and user permutations in `tab:menus` (source line 1353), `tab:residues` (2376),
and `tab:binary-extra-menus` (3221) match the Lean declarations below. No
source/Lean discrepancy was found in these three tables.

Source: frozen `../source/TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.
The hash was reread during this review. This is a source comparison using
existing compiled theorem and axiom-audit evidence, not a new clean release
build. No Lean source was changed and no expensive build was rerun for it.
The primitive-flag, primitive-relay, and theta-block construction tables are
outside this review.

All declaration names below are under `UploadBroadcast`. Source coordinates
are one-based: Lean first-entry indices 0–5 correspond to source F1–F6.
`Profile.firstOrder` is exactly (123,132,213,231,312,321).
`BinaryMenuAllocation.pairLeft/pairRight` are (0,5), (1,3), (2,4), hence the
source charge/margin order (16,24,35). `ActualPairCapacities.secondIndex` is
(1,1), (2,2), (0,0), matching source Q22, Q33, Q11 with the correct sign
2Q minus the two first entries.

## Table tab:menus: all ten rows

Here k is the literal `R2PermutedMenus.pathPerm` index. Menus are sets, so
choice ordering and repeated padding do not change their meaning.

| Source row | k | Exact increment menu | Displayed margin lower bound |
|---|---:|---|---|
| T1^(1) | 1 | {e5,e3} | (1,1,2) |
| T1^(2) | 3 | {e6,e1} | (2,1,1) |
| T1^(3) | 4 | {e4,e2} | (1,2,1) |
| O^(1) | 4 | {e4+e6,e2,e1} | (1,1,0) |
| O^(2) | 0 | {e4,e3,e2+e5} | (0,1,1) |
| O^(3) | 1 | {e6,e5,e1+e3} | (1,0,1) |
| R | — | {e1+e3,e2+e5,e4+e6} | (1,1,1) |
| Z16 | 3 | {e1,e6} | (1,0,0) |
| Z24 | 4 | {e2,e4} | (0,1,0) |
| Z35 | 1 | {e3,e5} | (0,0,1) |

T1/O mapping: `NonzeroSameChartPermutations.indexed_arms` proves that the
indicated permutations place the enlarged signal or side at the source user.
`indexed_menu_table`, `sourceT1Menu`, and `sourceOMenu` give exactly the six
literal menu rows. `same_chart_all_permuted_choices` proves actual optimal
relays, exact first-entry increments, and all nine unchanged Q entries for
all n >= 1 and finite fields of cardinality >= 3. Its full-profile clauses,
or `NonzeroFamilyRanks.full_first_profile/full_second_profile`, compute the
listed margin vector at n=1; at general n it is that vector plus
(n-1)(1,1,1). Thus these are the full displayed source lower bounds.

Boundary mapping: `BoundaryComponentMenus.geometry`, `T1_exact_profile`, and
`T1_all_permuted_choices` cover T1 at n=0. The enlarged users are respectively
2, 3, 1 for Z16, Z24, Z35. The exact full profile has doubled second entry 1;
its actual margins are exactly the three displayed unit vectors. The same
indexed T1 menu table identifies the two exact choices in each row.

Regular mapping: `ResonantRelay.increment` is the displayed three-element
menu; `RegularExactMenus.jordan_exact_profile`, `from_actual_chart`, and
`from_actual_regular` establish exact increments and unchanged Q entries on
actual original tasks, with operational upload optimality. **The library
parameter n denotes source R_(n+1).** `ResonantRelay.every_positive_length`
uses source indexing explicitly, and `ActualPairCapacities.resonant_margin`
gives library margin n+1 in each pair. Source n=1 is therefore library n=0
and gives (1,1,1), without omitting or duplicating the boundary.

`ResidualProfiles.positive_index_menu`, `boundary_menu`, `regular_menu`, and
`profiles` combine these exact statements. Boundary and regular constructions
work over every finite field, so in particular satisfy the source's >=3
restriction. None of the exact menu equalities here is inferred merely from
an upper-bound menu theorem.

Important distinction: `ActualComponentCapacities.charge_for_family` uses
smaller sufficient integer reservations for T1. It is not the definition of
the stronger literal margin vector in this source table. The exact full-profile
theorems above supply that vector. `ActualComponentCapacities.margin_reindex`
proves the same unordered-pair transport as the menu permutations.

## Table tab:residues: all nine rows

`RootClassification.TableRow` lists these rows in the same order, with
translated dimensions (f+3n; u+2n; a+n):

| Source type | f | u | a | chi | n_min |
|---|---:|---|---|---:|---:|
| O | 0 | (0,0,0) | (0,0,1) | 1 | 1 |
| H | 0 | (0,0,1) | (0,0,1) | 1 | 1 |
| R0 | 1 | (0,1,1) | (0,1,1) | 1 | 0 |
| R1 | 1 | (1,1,1) | (0,1,1) | 1 | 0 |
| R2 | 1 | (1,1,1) | (1,1,1) | 2 | 0 |
| T0 | 2 | (1,1,1) | (1,1,1) | 1 | 0 |
| T1 | 2 | (1,1,2) | (1,1,1) | 1 | 0 |
| T2 | 2 | (1,2,2) | (1,1,1) | 1 | 0 |
| T3 | 2 | (2,2,2) | (1,1,1) | 1 | 0 |

`Structural.excess` evaluates to the displayed chi in every row, unchanged
by the translate. `RootClassification.table_legal_thresholds` proves all
nine exact lower boundaries even for integer n, so negative translates are
not silently ignored. `legal_translate` proves the displayed max formula.
`tableRow_sound` verifies legality, Tits value one, and positive excess;
`classification_iff` gives the exhaustive converse through
`UpToArmPermutation`, which lists all six simultaneous (u,a) permutations.
These are dimension-vector statements; they do not falsely claim that every
legal endpoint survives the active and omniscience reductions.

The later profile convention deliberately reverses the T1/T2 enlarged-arm
placement: `NonzeroDefectProfile.fullSignal` uses T1=(2n+2,2n+1,2n+1),
T2=(2n+2,2n+2,2n+1). This is exactly the arm order specified at source lines
2454–2460, not a discrepancy with the residue table. Other families retain
the residue-table arm order.

## Table tab:binary-extra-menus: all five rows

The following are literal `BinaryMenuAllocation.menu`, `charge`, and
`minimumParameter` values; duplicate padding is omitted:

| Source family | Range | Increment upper-bound menu | Charge |
|---|---|---|---|
| R0+n delta | n>=1 | {e4,e6,e1+e3,e2+e5} | (1,1,1) |
| T2+n delta | n>=1 | {e1,e6} | (1,0,0) |
| R1+n delta | n>=1 | {e3,e5} | (0,0,1) |
| T3+n delta, H+n delta | n>=2 | {e2,e4} | (0,1,0) |
| R2+n delta | n>=2 | {e4+e5}, with user permutations | (1,1,1) |

`NonzeroBinaryMenus.family`, `menu`, and `extraFamily` map the first four
rows to these definitions, with T3 and H both using `T3H`.
`BinaryMenuOptimality.additional_optimal_menu` and `r2_optimal_menu` give
every selected increment upper bound, unchanged second entries, actual
original-field relays, and equality of relay dimension with operational U*.
The theorems are valid over any finite field and therefore cover F2 without
extension-field or characteristic assumptions.

`BinaryMenuAllocation.menu_fits` (and `menu_fits_int`) proves selection under
nonnegative integer opposite-pair capacities. `BinaryMenuOptimality`'s
`additional_optimal_fits_capacity`, `r2_optimal_fits_capacity`,
`charge_le_actual_margin`, and `r2_charge_le_actual_margin` connect these
literal charges to actual tasks. The charge bounds require exactly n>=1
for R0/T2/R1 and n>=2 for T3/H/R2. Their full actual margins are respectively
(n,n,n), (n,n-1,n), (n-1,n-1,n), and (n-1,n-1,n-1) for both final rows.
The weaker n>=1 hypothesis on some relay-only existence statements does not
replace the n>=2 charge condition.

For R2, `R2PermutedMenus.inverseFirst_bound` proves that all six generators
are the actual user-permutation orbit of e4+e5; `BinaryMenuAllocation` also
proves `r2_menu_is_path` and `path_is_r2_menu` in both directions.
`BinaryAdditionalMenuPermutations.additional_optimal_permuted`,
`additional_fits_permuted`, `r2_optimal_permuted`, and `r2_fits_permuted`
transport the component, first/second profiles, and capacity coordinates
together. `exceptions_permuted` proves the source's separate n=1 cases
T3+delta, H+delta, R2+delta have optimal relays with no increased profile
entry; they are not incorrectly charged as n>=2 cases.

## Existing verification evidence used

- `logs/nonzero-same-chart-endpoint-axioms.log`: all 44 same-chart endpoint
  theorems pass the standard axiom whitelist, including literal indexed arms.
- `verification/residual-profiles-axioms.log` and
  `verification/boundary-component-menus-axioms.log`: source profile endpoint,
  actual boundary geometry, exact profiles, and all permutations.
- `verification/local-binary-source-axioms.log`: optimal original and additional
  binary menus, actual charge bounds, permutations, and exceptions.
- `verification/actual-component-capacities-axioms.log`: actual margin formulas
  and their permutation transport.
- `verification/FinalAllCoverageReview20261008.lean` and its saved
  `verification/final-all-coverage-review-20261008.log`: independent endpoint
  checks include `RootClassification.classification_iff` and
  `table_legal_thresholds` and the relevant source-facing menu endpoints.

The consulted axiom evidence reports only `propext`, `Classical.choice`, and
`Quot.sound`. Release-build reproducibility remains the separate release
verification obligation; this document makes no claim to have rerun it.
