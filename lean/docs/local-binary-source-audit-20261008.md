# Independent semantic audit: original and additional binary relay choices

Frozen source: `../source/TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.
Claims: `lem:binary-menu` at line 3163 and
`lem:binary-additional-menus` at lines 3201ff, including both referenced tables.

## Original choices: complete

The claim is about every menu member in the ten rows of `tab:menus`, with
exact first increments and all nine second entries unchanged. Merely proving
an upper bound for an increment would not suffice.

- `BinaryMenuPermutations.original_exact_optimal_permuted` supplies each T1
  and O choice on the original coefficient space, for every user permutation.
  It uses the exact hyperplane calculation in `BinaryExactMenus` and the
  actual indecomposable relation and intersection ranks in
  `BinaryExactFamilyMenus`. No generic-rank or extension-field specialization
  assumption is made. The output rank equals the original operational U*.
- In canonical arm order the T1 menu is `{e5,e3}` and O is
  `{e6,e5,e1+e3}`. These are the source's T1^(1) and O^(3). The exact
  permutation identities in `NonzeroSameChartPermutations.indexed_menu_table`
  give the other four rows. The repeated generators used to pad a finite
  menu do not introduce an additional requirement or omit a choice.
- `BoundaryComponentMenus.T1_all_permuted_choices` realizes all three Z
  rows with exact increments, unchanged second entries, rank one, and actual
  operational optimality. The index-zero T1 dimension vector has exactly
  one full signal and the three distinct side lines in the source definition.
- `RegularExactMenus.from_actual_regular` constructs the genuine Jordan
  chart from indecomposability, zero defect, positive excess and intrinsic
  activity, then realizes all three exact R choices on the original task.
  `from_actual_chart` and `jordan_exact_profile` verify the entire 15-entry
  transport. The regular increments are exactly
  `{e1+e3,e2+e5,e4+e6}`. Lean's index n here means source R_(n+1), so every
  positive source size is covered.

These theorems work over every original finite field. In particular they
apply to F2 without assuming its cardinality is at least three. The use of a
stronger all-field statement does not weaken the binary assertion.

## Additional choices: complete

`BinaryMenuOptimality.additional_optimal_menu` and `r2_optimal_menu` provide
an actual locally generated feasible relay, equality of its rank to the
nonlinear regularized U*, the coordinatewise first bound, and equality of
all nine second entries. Every selected generator, not just some generator,
is covered. The menus in `BinaryMenuAllocation.menu` are literally:

- R0, n >= 1: e4, e6, e1+e3, e2+e5; charge (1,1,1).
- T2, n >= 1: e1, e6; charge (1,0,0).
- R1, n >= 1: e3, e5; charge (0,0,1).
- T3 and H, n >= 2: e2, e4; charge (0,1,0).
- R2, n >= 2: the six user-permuted images of e4+e5; charge (1,1,1).

`r2_menu_is_path` and `path_is_r2_menu` verify that the six R2 vectors are
exactly that orbit. The coordinate order is source (123,132,213,231,312,321),
with Lean indices 0 through 5. `pairLeft` and `pairRight` therefore give
source pairs (16,24,35), in that order.

The charge is not an assumed margin. `charge_le_actual_margin` and
`r2_charge_le_actual_margin` prove the inequality against
`2*Q_(i,l) - F_left - F_right` for every actual second entry and every opposite
pair, using the source parameter ranges. The underlying full profile ranks
are obtained from actual indecomposability and the seven family dimensions.
`menu_fits`, `additional_optimal_fits_capacity`, and `r2_optimal_fits_capacity`
prove selection from every nonnegative integer capacity vector paying the
three charges. No divisible, fractional, or asymptotic allocation is substituted.

`BinaryAdditionalMenuPermutations` makes the source caption's simultaneous
user/profile/charge relabeling explicit. `additional_optimal_permuted`,
`r2_optimal_permuted`, `additional_fits_permuted`, and `r2_fits_permuted`
return actual original-space relays optimal for original T, while measuring
profile and capacities in the same selected arm order. Thus this is not an
assumed task symmetry. Actual margin bounds apply to that same reindexed
original task.

`small_exceptions_optimal` covers H+delta and R2+delta, and
`tripod_exception_optimal` covers T3+delta. Each gives no increase in any
of the fifteen entries and equality to actual U*. `exceptions_permuted`
transports all three conclusions to every arm order. Scalar local uploads
follow from the actual locally generated relay construction, with a genuine
length-one original-field linear code available through
`RelayLinearComposition.full_relay_linear_code`.

## Hypotheses and trust boundary

The inputs are an actual finite-dimensional operational task, the original
field, simultaneous indecomposability, and the source's seven family
dimensions. Activity is required only in the regular residual chart theorem
and is derived for actual residual factors. No requested profile, relay
existence, nonlinear converse, optimality, or field-extension descent is
supplied as an input.

`verification/LocalBinarySourceAudit.lean` checks the endpoint roots and
collects dependencies of all imported project theorems. The accepted axiom
set is exactly the standard whitelist `propext`, `Classical.choice`, and
`Quot.sound`. See `verification/local-binary-source-axioms.log`.

Verdict: both claims can be marked `reviewed_complete`. This does not close
an unrelated global allocation or joint-region endpoint.
