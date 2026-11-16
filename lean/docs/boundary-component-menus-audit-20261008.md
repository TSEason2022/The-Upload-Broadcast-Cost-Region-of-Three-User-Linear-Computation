# Actual low-index residual menus

Source: the `n=0` paragraph, lines 2786–2801 of `TIT_LCBC_optimized.tex`, and the three Z rows of Table `tab:menus`.

## Genuine boundary geometry

`BoundaryComponentMenus.geometry` takes only an actual indecomposable task and `Dimensions T g 0` for T1 or T2. The positive-defect probe theorem derives zero intersection of every two side lines. The dimension formula then proves that each pair of distinct side lines spans the ambient plane. The signal spaces are determined from their dimensions and the task's actual inclusions.

In the profile library's canonical arm order:

- T1 has U0 = F, U1 = A1, U2 = A2. It admits relays A1 and A2. The exact first increments are e5 and e3, respectively. All nine second-family entries equal 1/2 and remain unchanged. This is the Z35 source row.
- T2 has U0 = U1 = F, U2 = A2. Relay A2 preserves all fifteen profile entries exactly. In particular it is not justified to discard T2 at n=0 as passive or omniscience.

`T1_all_permuted_choices` transports both actual T1 choices through every concrete `pathPerm k`, with the increment in original six-entry order through `inverseFirst k`. `T2_permuted_preserving` similarly transports the preserving T2 choice. They give actual relay subspaces of the original coefficient space, not just an isomorphic canonical task.

## Operational optimality

Each constructed relay is a side-information line, hence locally generated, and the actual pair-spanning geometry proves feasibility. The relay has dimension one. `boundary_code_lower` and `boundary_code_lower_permuted` invoke the geometric nonlinear converse on the original task to prove an upload lower bound of one for every positive blocklength and every nonlinear finite-alphabet code. The constructed scalar code and `uploadOptimum_eq_of_code` then identify the actual closure/regularized U* with that one-dimensional relay.

There is no field-extension hypothesis and no cardinality-at-least-three restriction. These boundary constructions work over every finite field, including the binary field.

## Scope

These are the low-index inputs for the source residual profile proposition. Nonzero positive indices are handled by `NonzeroSameChartPermutations`; zero-excess by `ResidualComponentAdditivity.zero_excess_full_relay`; regular resonant components require the actual chart from `ActiveComponentClassification.regular_assignment` and transport of the existing resonant relay menus.

Validation is recorded separately in the focused build and axiom-audit logs; this document does not by itself promote the complete source proposition.
