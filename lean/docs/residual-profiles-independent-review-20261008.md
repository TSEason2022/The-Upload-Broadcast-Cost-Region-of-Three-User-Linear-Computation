# Independent review of the complete local relay proposition

Source: frozen `TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.
Claim `thm:profiles`, line 1376; associated table at 1353ff.

I independently compared the proposition and its table against
`ResidualProfiles.profiles`, `ResidualProfileCompleteness`, the exact regular
and boundary constructions, and the actual component classification.

The proposition's field restriction is preserved: an original finite field
with at least three elements. Its active residual indecomposable is an actual
six-subspace operational task. `ActiveResidual` contains coefficient-space
geometry only, and `source_residual_active` plus `component_active` derive it
for source components; it does not assume any profile, relay, or optimum.

The four conclusion clauses jointly cover the entire statement:

1. Every component outside the table has a locally generated feasible relay,
   actual nonlinear operational optimality and exact equality of all fifteen
   entries. The proof performs the exhaustive residual classification; zero
   excess uses the full relay. The surviving T2 index-zero boundary is covered
   explicitly and is not silently discarded.
2. Every T1 row and its index-zero Z boundary has every exact listed choice,
   in all six arm permutations. Repeated choices merely pad a two-member set.
3. Every O row at n >= 1 has all three exact choices, again in every arm order.
4. Every regular R_n actual chart has all three exact choices. The chart-free
   `RegularExactMenus.from_actual_regular` independently constructs the chart
   for every genuine positive-excess regular residual. This rules out an
   unproved regular-family membership assumption hiding behind the chart input.

`ListedExceptional` agrees with table membership: labeled positive-index T1,
O, positive-size Jordan regular tasks, and zero-index T1 = Z. The nonlisted
branch starts from actual exhaustive classification, not an externally
provided family enumeration. Its surviving nonzero-defect rows are exactly
the six profile-preserving families. Parameter bounds are retained.

`OptimalExactMenu` asserts exact equalities, not upper bounds. Its increment
functions are definitionally zero on the nine second-family entries. The
source profile order and arm mapping are identified by the proved indexed
menu table. Operational optimality is equality to `T.uploadOptimum`, defined
from arbitrary finite nonlinear codes, positive blocklengths and closure.

Focused builds and the independent combined
`verification/LocalBinarySourceAudit.lean` accept only the three standard
Lean axioms. The semantic review does not replace the kernel audit.

Verdict: `thm:profiles` is semantically complete and can be marked
`reviewed_complete`. The proposition's local scope does not imply the final
global allocation, cycle repair, or finite-block joint-region construction.
