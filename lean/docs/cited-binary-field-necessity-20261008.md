# Binary field-size necessity: actual operational counterexample

This closes the standalone assertion at frozen-manuscript lines 1804–1806. It is distinct from the five-bit half-integral example: the rounded fully informed optimum itself is unattainable scalarly here.

## Literal source instance

Over `ZMod 2`, let the source coordinates be `(A,B)`. The three side columns are `(1,0)`, `(0,1)`, and `(1,1)`. Their demands are `(0,1)`, `(1,1)`, and `(1,0)`, respectively. `signal_from_demands` proves that each side-plus-demand space is the entire two-dimensional coefficient space. Thus the operational task is the cited instance, not an assumed substitute.

This is the binary instance identified in Example 4 and Appendix A of Yao–Jafar's cited three-user LCBC paper: [arXiv version](https://arxiv.org/pdf/2206.10049v3), [journal-layout author copy](https://escholarship.org/content/qt44b1c5hm/qt44b1c5hm.pdf).

## Verified conclusions

- `broadcastOptimum_eq_one`: the actual nonlinear, all-blocklength fully informed optimum is 1. Every one of the fifteen profile entries is 1.
- `broadcast_source_injective`: any scalar fully informed zero-error encoder is injective on the four actual binary source values. The proof checks all binary side-confusability directions by ordinary kernel reduction.
- `scalar_broadcast_card`: every finite scalar broadcast has at least four attainable messages.
- `scalar_cost_ge_two`: its binary alphabet cost is at least 2.
- `scalar_cost_gt_ceiling`: this is strictly greater than `ceil(D*) = 1`, even for nonlinear codes, and hence in particular for scalar linear codes.

No cardinality or rank conclusion is assumed. No native-evaluation axiom is used.

## Reproduction

`source scripts/env.sh && lake build UploadBroadcast.CitedBinaryFieldNecessity`

`lake env lean scripts/AuditCitedBinaryFieldNecessity.lean`

The build is warning-free. All six audited roots use only `propext`, `Classical.choice`, and `Quot.sound`; see `logs/cited-binary-field-necessity-axioms.log`.
