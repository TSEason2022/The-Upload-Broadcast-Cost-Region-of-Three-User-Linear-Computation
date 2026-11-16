# Opposite one-symbol demands: source mapping

Frozen source: `../source/TIT_LCBC_optimized.tex`, lines 1182–1189, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.

## Actual tasks and direct sum

`UploadBroadcast.OppositeDemandExample.first` is the one-dimensional task
with side spaces `(K,0,0)` and signal spaces `(K,K,0)`: User 1 knows x,
User 2 demands x, and User 3 has no information or demand.
`second` has side spaces `(0,K,0)` and the same signal spaces: User 2 knows y
and User 1 demands y. The actual task `combined` is
`Profile.directSum (first K) (second K)` on the coefficient space `K × K`.
No numerical optimum or abstract task profile is an input assumption.

## Source-facing endpoint

`strict_subadditivity_example` proves, for every finite field K, that the
operational broadcast optima of the two individual tasks and their literal
direct sum are all 1, and hence the joint optimum is strictly below their
sum. It also constructs a scalar linear code for the combined task whose
encoder is exactly `x ↦ x (1,0) + x (0,1)` and whose attained-alphabet
blocklength-one cost is exactly 1.

`singleton_encoders` similarly constructs actual length-one scalar codes
that transmit the original source symbol for each individual task.
`coefficient_code` constructs genuine linear decoders through a proved
kernel-containment condition; it does not assume decodability from a
numerical cost. `combined_span` verifies the actual side-information
recovery geometry, and `sum_encoder` states the literal x+y encoder.
These encoder and decoder results hold over every field, including binary
fields; finiteness is needed only for the operational cost statements.

## Optimality and profiles

`first_entry_two`, `first_entry_zero`, and `second_entry_zero` calculate
specific entries of the actual fifteen-entry conditional-rank profile.
Entrywise direct-sum additivity gives a unit lower bound for the combined
task. Each explicit scalar code supplies the matching upper bound through
the proved nonlinear converse and its attained alphabet bound. Thus
`first_rankBound`, `second_rankBound`, and `combined_rankBound` all equal 1.
`optima` uses the already-proved identification of the operational optimum
with that actual rank maximum.

`all_block_lower` records the universal converse: for any of these tasks,
every finite-alphabet, possibly nonlinear zero-error code at every positive
blocklength has cost at least 1. `scalar_cost` proves that any valid
length-one scalar code for each task attains cost exactly 1, so nominal
coordinate count is not silently equated with attained-alphabet cost.

The source's concluding lesson about coordinating component relay choices
is an interpretation of the strict inequality. This endpoint closes the
explicit broadcast-subadditivity example; it does not substitute for the
separate relay-allocation or joint-region assembly theorems.

## Verification

Focused build: `logs/opposite-demand-target.log`.
Strict imported-project axiom audit: `verification/OppositeDemandExampleAudit.lean`.
Audit output: `verification/opposite-demand-axioms.log`.
The audit accepts only `propext`, `Classical.choice`, and `Quot.sound` and
checks the full imported project theorem closure, not only printed roots.

The focused module compilation and audit both exited 0 with no warnings.
The audit checked 835 imported project theorems and found exactly the three
allowed axioms above. Commands (after sourcing `scripts/env.sh`):

```sh
lake env lean -o .lake/build/lib/lean/UploadBroadcast/OppositeDemandExample.olean UploadBroadcast/OppositeDemandExample.lean
lake env lean verification/OppositeDemandExampleAudit.lean
```
