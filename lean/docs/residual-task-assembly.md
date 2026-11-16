# Constructed residual task assembly

## Arbitrary-task pair factorization

`FullResidualAssembly` begins with an arbitrary feasible `Task K F`. Its construction:

1. Restricts to the actual side-information span, with a concrete `normalizationRetraction`.
2. Applies the existing common quotient, simultaneous active-pair shear, and passive-pair deletion.
3. Proves that every surviving pair coefficient belongs to the missing user's signal (`pairReduction_pairKnown_le`). Consequently their sum belongs to every signal.
4. Constructs one idempotent projection onto the intrinsic pair-known sum that preserves every side space and, for pair-active tasks, every signal.
5. Gives an actual ambient product equivalence and exact task equality (`pairResidual_mapTask`) with a pair omniscience task and a pair-free residual task.
6. Constructs the private/tripod chart of the actual residual from its pairwise-disjoint spanning side spaces.

The resulting theorem `Task.pair_canonical_factorization_achievableAt_eq` identifies every original nonlinear fixed-block region with the region of `Profile.directSum T.pairOmniscienceFactor T.canonicalPairFreeResidual`. Its inputs contain no normal-form certificate, chosen reduction, or rate-preservation assumption. The first factor's signals are all top; the second has the exact `ResidualUpload.Ambient` side spaces.

## Actual canonical residual reductions

`ResidualTaskAssembly` starts with a task in the canonical side chart; its demands are arbitrary feasible subspaces. It constructs:

- The exact private coordinates used by remote signals.
- Simultaneous deletion of their unused complements, with a `PassiveRetraction` and exact canonical side identities.
- Full remote-use of all retained private coordinates as a proved conclusion.
- The actual quotient demand subspaces, their private projections and pure tripod intersections.
- Lifted graph maps with exact signal membership. Pure rows are never replaced by projections of mixed demands.
- The signed private-incidence map B and the actual relation-row map G.
- The retained row space `(D1 + D2 + D3) + G(ker B)`.
- A simultaneous side-preserving private-to-tripod gauge, obtained by factoring the passive component of G through B.
- Concrete deletion of the resulting passive tripod rows.

`canonicalReduction_achievableAt_eq` and `canonicalReduction_costRegion_eq` package both private and row deletion with no preselected graph/gauge/reduction input. `canonicalReduction_sides` and `canonicalReduction_fully_used` give the resulting canonical geometry.

`DemandData.signalBridge` constructs the complete `SignalBridge.Data` for the actual row-reduced task. Its active condition follows from `activeRows_generated`, and membership of every private, pure, and mixed demand is verified in the actual signal spaces. `canonicalReductionBridge` is the ready-to-use version for the fully selected reduction. The signal-intersection bridge needed by the nonlinear converse is therefore a theorem of the constructed task, rather than an assumed residual property.

## Rank identification

`ResidualTaskRanks.activeRows_finrank` proves

`dim(activeRows) = dim(D1 + D2 + D3) + dim(image((G mod pureRows)|ker B))`.

`mixedRows_stacked_rank` also identifies the mixed image rank with the actual stacked-rank difference `[B;G]-B`.

`noncommon_activeRows_finrank` subtracts `dim(D1 ∩ D2 ∩ D3)` and gives precisely the pure-noncommon-plus-mixed expression for the retained noncommon tripod dimension.

## Pure-row transport

`ResidualPureTransport` proves that unused-private deletion and the private gauge preserve the pure demand spaces exactly. Passive-row deletion restricts them by the retained-row inclusion. Consequently `canonicalReduction_common_pure_eq_bot` preserves a zero common pure intersection, as required after separating the common-tripod omniscience factor.

## Scope and remaining assembly

The pair factorization and the private/passive-tripod reductions above are actual task constructions and operational equivalences. They do not by themselves assert the full manuscript minimum-upload formula. Separating the common pure tripod rows into the omniscience factor, putting the remaining pure-row triple into the exact grouped `ResidualRowCompletion.Rows` chart, and composing the resulting coding/rank formulas remain additional assembly obligations. Those should be tracked separately rather than inferred from these primitives.

The retractions store linear coefficient maps. `PassiveLinearCode` supplies actual linear-code deletion/restoration and the corresponding cost bounds; the region equivalences in these modules also apply to arbitrary nonlinear codes.

## Verification targets

- `logs/residual-task-assembly-build.log`
- `logs/pair-residual-assembly-build.log`
- `logs/full-residual-assembly-build.log`
- `logs/residual-task-ranks-build.log`
- `logs/residual-pure-transport-build.log`
- `verification/ResidualAssemblyAxioms.lean`
- `logs/residual-assembly-axioms.log`

No project axioms, `sorry`, or proof placeholders are used.

## Verified result

All five new proof modules compile without errors or warnings. The combined
umbrella-plus-residual dependency audit checked 3,515 loaded project theorems;
its complete reachable axiom set was exactly `propext`, `Quot.sound`, and
`Classical.choice`. The lexical source audit passed across 153 Lean files.
See `logs/residual-assembly-all-axioms.log` and
`logs/residual-assembly-source-audit.log`. The checked public signatures are
recorded in `logs/residual-assembly-signatures.log`.

For downstream composition, lift the concrete passive retractions to a product
with the omniscience factor. Equality of an isolated residual region alone is
not a justification for replacing that component inside a jointly coded direct
sum. The pair factorization instead proves exact task equality under an actual
ambient equivalence, and the later private/row reductions expose the needed
concrete retractions.
