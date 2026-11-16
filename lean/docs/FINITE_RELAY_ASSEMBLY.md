# Actual finite component relay assembly

These modules bridge integer numerical menu allocation to concrete subspaces
of the original-field coefficient task. They do not assert that every task
has already been classified into the listed component types.

## Compiled interfaces

- `FiniteRelayAssembly`: dependent finite-product tasks and subspaces; local
  generation and feasibility; exact relay rank sums; all fifteen entry sums;
  intrinsic relay-task profiles; binary-product relay profile addition.
- `GlobalMenuAssembly`: `RealizesMenu` records every local geometric menu
  choice. `assemble_choices`, `assemble_nat_weights`, `assemble_int_weights`
  and `assemble_charged_menus` construct actual product relay subspaces.
  Integer multiplicities are explicitly assigned to component copies before
  local relays are selected. Output profile bounds are proved by additivity.
- `NonzeroFiniteAssembly`: all eight canonical nonzero-defect families,
  from actual task indecomposability and the seven `Dimensions` equalities.
  `binary_relay` constructs an actual finite relay with exact summed rank and
  all fifteen budget inequalities. `stable_relay` does the same for the q≥3
  same-chart construction. T1/O are supplied conservative sufficient integer
  pair charges; the five additional hyperplane kinds and R2 use the proved
  manuscript extra-menu charges. User-permuted classification is a separate
  transport step and is not silently inferred.
- `ResonantFiniteAssembly.exists_of_weights`: nonnegative integer weights
  choose actual Jordan-family relays for all component copies, with exact
  total rank and all fifteen increment bounds.
- `AugmentedRelayAssembly.resonant_charged_relay`: resonant-first integer
  packing followed by actual relay construction for arbitrary locally proved
  charged menus. Inputs are the repaired orientation constraints, strengthened
  opposite-pair constraints, and original-task budget inequalities.
  `resonant_nonzero_relay` specializes this to the actual eight nonzero-defect
  family constructions and an integer D.
- `CycleFiniteAssembly`: both canonical positive and reverse cycle repair
  constructions supply the same concrete geometric menu interface.
- `OmniscienceRelayProfile`: every feasible omniscience relay preserves all
  fifteen profile entries. `assemble_binary` combines actual residual and Ω
  relays, exact numerical ranks, the proven operational optimality identities,
  and the compression theorem to derive binary separation.
- `RelayCoordinateTransport.transport_exists`: a genuine ambient linear
  equivalence transports the constructed relay, exact rank, and all fifteen
  entries back to the original coordinate task.

## Unconditional residual selection

`ResidualBackgroundSelectionTheorem.exists_optimal_relay` starts with an
arbitrary intrinsic active residual S, an arbitrary omniscience task O, and an
integer D bounding the actual fifteen-entry profile of S ⊕ O. It constructs a
locally generated feasible P in S with rank exactly S.uploadOptimum and all
fifteen inequalities entry(S_P)+entry(O)≤D. No decomposition, family assignment,
capacity, cycle availability, selected relay or final-profile conclusion is an
assumption. `residual_background_selection` proves the named universal input
consumed by the canonical/source endpoint wrappers.

The construction now includes:

- Actual finite indecomposable decomposition and classified product charts
- Actual family menus at every legal index, including user permutations,
  zero-index T1/T2 boundaries and binary low-index exceptions
- Universal nonnegative pair margins and capacities derived from the original
  actual D bound, including the full omniscience profile
- Exact integer orientation deficits and charged-coordinate repair bookkeeping
- Physical cycle extraction solely from the zero-excess residual complement;
  positive-excess indecomposables have zero edge multiplicity, so no
  Krull–Schmidt uniqueness assumption is needed
- Injective physical cycle charts, exact positive/reverse canonical coordinate
  identities, distinct resonant/cycle pairing, and actual repaired relays
- Actual finite integer menu choices, finite relay assembly and exact rank sums
- Dimension-derived equality with the operational active-residual upload
  minimum, and exact profile/rank transport back to the original coefficients

`OmniscienceRelayConstruction.exists_scalar` constructs the canonical Ω relay
from the actual scalar optimal linear code, with exact rank, all-fifteen profile
preservation, and binary separation. Its rank lower bound is proved directly
from the actual induced side dimensions and spanning.

The separate `CanonicalSelectionAssembly` and `OriginalJointReduction` modules
combine this residual theorem with integral Ω selection and the constructed
original-task passive reductions. Their source-facing endpoint statements are
maintained separately.

The dedicated standard-axiom audit is
`verification/FiniteRelayAssemblyAxioms.lean`. No custom axiom or `sorry` is used.

The final universal residual endpoints have a dedicated audit in
`verification/ResidualBackgroundSelectionAxioms.lean` with output in
`verification/residual-background-selection-axioms.log`.
