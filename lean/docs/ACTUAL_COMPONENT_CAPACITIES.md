# Actual component capacities

`UploadBroadcast/ActualPairCapacities.lean` derives the three opposite-pair
margins from the literal coefficient submodules. Conditional-rank submodularity
proves all margins nonnegative, without classification or a relay assumption.
Margins add over actual finite task products and binary direct sums. Every
omniscience task has zero matching pair margins. A Jordan resonant copy of
parameter `n` has margin `n + 1` in each pair.

The six first entries have signed-integer representatives. For an integer
scalar target `D`, `capacity T D r` is exactly `D - entry T (.inl r)`.
`rankBound T ≤ D` proves these six integers nonnegative. A charge bounded by
the actual matching margin is then paid by the corresponding opposite pair.
No opposite-pair budget is assumed by this conversion.

`UploadBroadcast/ActualComponentCapacities.lean` computes the actual charges
from indecomposability and the seven dimension equalities supplied by
`NonzeroFamilyRanks.Dimensions`. All positive-index nonzero-defect families
are covered. The low-index T3, H and R2 exceptions at parameter one have
zero charge. At parameter zero, the active T1 boundary has its literal T1
charge and the T2 boundary has zero charge. The boundary proof uses the
actual distinct-line geometry of `BoundaryComponentMenus`, not a supplied
profile equality. User relabelings transport margins using the identical
unordered-pair permutation as the menus.

The endpoint `actual_integer_capacities` covers the actual task

    resonant finite product × (classified finite product × remainder).

Its inputs are component indecomposability, family dimensions in the selected
user order, the permitted parameter ranges, and the original full task's
`rankBound ≤ D`. The remainder is arbitrary: its nonnegative actual margins
follow from submodularity. Thus zero-excess and omniscience remainders need no
assumed pair-margin inequalities. Its conclusions are six nonnegative integer
capacities, the exact first-entry slack identity, the strengthened pair
reservations including every original resonant copy, and all nine second-entry
bounds. `repaired_actual_capacities` further derives both repaired orientation
inequalities and the remaining strengthened reservations.

These modules prove the numerical capacity stage, not component decomposition,
relay geometry, or upload-optimality. Those stages remain separate. Integer
`D` is essential to exact integer slack; a nonintegral scalar target cannot in
general have exact integral slacks. Half-integral operational targets must use
the separate two-copy scaling construction.

Audit: `verification/ActualComponentCapacitiesAxioms.lean` checks every theorem
in both namespaces and rejects all dependencies except `propext`,
`Classical.choice`, and `Quot.sound`.

Source correspondence: the universal margins are `eq:margins-component` and
`eq:pair-margin-general`; actual additivity and charge domination implement
`eq:reduced-margins` and `eq:pair-cap` from the relay-allocation section. The
charges recorded here are the sufficient integer menu reservations used by
`NonzeroFiniteAssembly`; they may be smaller than the displayed ordinary
margin lower bounds (for example, the T1 menu needs only its distinguished
opposite pair). Every bound is derived from the full actual profile, and the
uncharged positive remainder is retained when proving the global inequality.

Verification completed on 2026-10-08: both modules compile with the repository
Lean toolchain. The strict audit passed for all 44 theorem declarations in the
two namespaces; every dependency is one of the three standard axioms listed
above. The saved output is `verification/actual-component-capacities-axioms.log`.
