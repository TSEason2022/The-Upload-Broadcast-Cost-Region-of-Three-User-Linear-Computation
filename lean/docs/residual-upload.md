# Residual upload: verified coordinate and operational core

Manuscript anchors: `lem:bridges`, `eq:tripod-intersection-bridge`,
`eq:bridge-cancellation`, `eq:bridge-two-recoveries`,
`eq:bridge-third-recovery`, `eq:slice-inverse`, `eq:gamma-rank`, and
`lem:zero-common-row-relay`.

## Signal intersections and nonlinear local inversion

`SignalBridge.Data` specifies actual coefficient embeddings of the three
private spaces and the two tripod coordinates, actual side/pure/mixed-demand
memberships in the signal spaces, and the active retained-row spanning
condition. Its signed private-incidence kernel condition is

    a21 x + a31 x = 0,
    a12 x + a32 x = 0,
    a13 x - a23 x = 0.

Every retained row is required to be a sum of the three pure-demand rows and
`φ1 x + φ2 x + φ3 x` for such a kernel vector. This is the explicit output
condition of the passive-row reduction, not an assumed signal intersection.

- `annihilator_v` derives the manuscript's cancellation directly from these
  actual demand vectors.
- `tripod_le_signal_sup_inter` proves the coefficient-space inclusion by
  annihilator separation.
- `rotate` and `rotate_tripod_range` implement the cyclic coordinate change
  `(v,r) ↦ (r-v,-v)`, including its incidence signs.
- `all_tripod_bridges` proves all three cyclic inclusions from one data record.
- `common_observation` and `exists_bridge_decoder` construct deterministic
  common-function and bridge decoders, for any vector-valued source and any
  possibly nonlinear upload tuple.
- `private_slice_inverse` derives local slice inversion from an actual
  `Task.Code.zero_error`, an isolated private projection, and the span of
  remote projected signal spaces. It does not assume local recovery.
- `signalRecovery_from_slice` feeds that inversion into the actual code's
  decoder. All these operational statements permit every blocklength and
  nonlinear encoders and broadcasts.

The pure spaces in these statements are actual pure coefficient subspaces.
They are not silently replaced by projections of mixed demands.

## Rank and genuine Shannon calculations

`ResidualUpload.Ambient P1 P2 P3 T` is
`((P1 × P2) × P3) × (T × T)`.
The three side maps are the actual embeddings

    (p,t) ↦ (((p,0),0),(t,0)),
    (p,t) ↦ (((0,p),0),(0,t)),
    (p,t) ↦ (((0,0),p),(-t,t)).

`sides_span` and `sides_disjoint₁₂/₁₃/₂₃` prove their span and pairwise
trivial intersections. `gamma_rank` derives the integer rank identity.
`gamma_entropy` proves the corresponding identity for genuine Shannon
entropy of the actual uniform block source in base-|K| units.
`side_observations_pairwise_independent` derives actual independence from
the uniform law and the proved rank intersections.

These entropy statements concern the uniform residual component. The actual
residual-code converse is assembled below; conditioning on the omniscience
component is a separate direct-sum step.

## Simultaneous row completion

`ResidualRowCompletion.Rows H1 H2 H3 D` is
`H1 × H2 × H3 × D × D`. `Hi` is a row block with no pure demand at user i.
The final two coordinates are the diamond row directions a and b. Retained
empty-demand/mixed rows may be included in H1.

`rowUpload` sends one vector along each required local side line:

    v-coordinate: (h1,0,-h3,0,b),
    r-coordinate: (0,h2,h3,a,0).

Its injectivity, exact rank, local generation, and all three recovery
conditions are proved. `simultaneous_corrections` extends the mixed-demand
coordinate maps and combines corrections on independent target coordinates.
`privateCorrection_square_zero` and `privateShear_preserves` prove that the
actual simultaneous shear is invertible and preserves all three sides.

`generated_signals_row_completion` accepts separate pure spaces B1/B2/B3,
remote-private domains Li, and mixed graph maps φi. It constructs the actual
signal spaces as side + pure representatives + mixed graph representatives.
The pure-row coordinate requirements are:

- B1 has zero H1 and b coordinates
- B2 has zero H2 and a coordinates
- B3 has zero H3 coordinate

It proves existence of a relay in the original mixed-demand coordinates,
with all three feasibility inclusions, exact local generation, and rank
`dim P1 + dim P2 + dim P3 + dim Rows`.

`exists_local_linear_upload_code` converts any such finite-dimensional,
locally generated feasible relay into actual local linear encoders, a
linear relay assembler, and linear signal decoders. The message coordinates
are partitioned by their uploading user, and their total fixed scalar length
is proved equal to the relay dimension. This is a scalar dual-source code
interface; it is not merely a dimension estimate or a feasibility axiom.
`ResidualOperational.finiteCode_of_local_relay` converts it into an actual
`Task.FiniteCode 1` and proves the attained-alphabet upload-cost bound
`uploadCost ≤ dim P`, closing the singleton-block operational interface.

## Actual nonlinear residual converse

`ResidualConverse.PrivateSplit` records an actual isolated private projection,
its side/tripod splitting, and the remote projected-signal span. It does not
postulate local inversion; inversion is derived from `Code.zero_error`.

- `common_retained_bound_finite` proves the common-function inequality for
  genuine heterogeneous finite observations from pointwise recoveries and
  actual independence.
- `code_retained_entropy_bound` builds all functional hypotheses from an
  arbitrary nonlinear `Task.Code` and its coefficient/projection geometry.
- `code_retained_rank_bound` substitutes the actual uniform-source entropy
  ranks, retaining both actual conditional mutual informations.
- The `_ordered` variants apply to any permutation of the three users, so
  cyclic bounds do not require changing message-alphabet types.
- `explicit_residual_upload_lower_bound` proves
  `dim P1 + dim P2 + dim P3 + dim T ≤ code.uploadCost` for every actual
  `Task.FiniteCode` in the explicit residual product model. It derives the
  signal bridge from `SignalBridge.Data`, side independence and Γ from the
  actual product embeddings, and the cost bound from attained encoder
  alphabets. The theorem includes every nonlinear fixed-length code and
  every positive blocklength.
- `explicit_residual_retained_bound` keeps both conditional-MI terms,
  conditioned on the actual original side observations, in q-ary units.

The explicit endpoint requires the task's side spaces to equal the stated
product-model spaces and its signal spaces to equal the active data record's
signals. Those are structural transport obligations, not information-theoretic
axioms. Conditioning on an additional independent omniscience source Ω is
not asserted by these unconditioned residual theorems.

## Independent omniscience component and actual global converse

`GlobalUploadConverse` conditions the common-function argument on the actual
independent omniscience observation. All three residual inequalities, their
conditional recoveries and their Shannon rank values are derived from an
arbitrary finite nonlinear task code. Its `code_upload_lower_bound` applies
the verified omniscience-lift inequality; it does not assume a residual
entropy bound.

`GlobalUploadGeometry` constructs the required geometry for an actual direct
sum of an omniscience task and the canonical active residual. The product
rank calculation gives residual private-plus-tripod dimension plus the
maximum of the three omniscience deficits and half their sum.
`GlobalUploadAssembly.fully_used_active_directSum_lower_bound` constructs
private slice certificates from full use of the actual remote private
projections. `fully_used_active_costRegion_lower_bound` extends the result
to every blocklength and the closed operational region.

`CommonTripodAssembly` splits the actual intersection of all three pure row
spaces from a canonical task. It proves an exact coefficient-task direct
sum with a common-tripod omniscience task, equality of nonlinear achievable
sets and closed regions, zero common pure rows in the residual, and exact
preservation of every used private projection. Pure rows are defined by
actual intersections and are never replaced by mixed-demand projections.

`CommonTripodRanks.activeRows_mem_iff` characterizes retained rows using
actual signal representatives whose signed private sum vanishes. This proves
independence from every selected graph lift. Under the common split, the
post-split active space equals the comap of the original active space along
the complement inclusion. `residual_activeRows_finrank` therefore subtracts
exactly the common pure dimension, connecting the operational residual to
the manuscript's noncommon-plus-mixed row-rank formula.

## Constructed zero-common relay and exact canonical optimum

`ZeroCommonRowNormalForm.exists_chart` derives the required three missing
pure coordinates from a zero triple intersection. A zero-dimensional
diamond block suffices; no spanning hypothesis is needed.
`ResidualRelayAssembly.signal_graphs` identifies each actual signal with
its side, pure rows and selected mixed graph. The chart, simultaneous shear,
and pullback yield `exists_relay_of_zero_common`, with exact relay rank and
all local-generation and feasibility properties. Its scalar linear code
endpoint is `exists_scalar_linear_upload`.

`GlobalUploadOptimal.canonical_uploadOptimum` combines the genuine nonlinear
converse with the constructed residual scalar code and original-field
two-instance omniscience code. It proves equality of the actual operational
upload infimum to residual private-plus-tripod dimension plus the canonical
omniscience optimum. It assumes actual canonical active coordinates and
full private use, rather than an entropy, recovery, or row-completion axiom.

## Scope of the remaining final assembly

The explicit residual and direct-sum modules prove their stated operational
converses from actual task geometry. The separate original-task assembly
must compose the normalized active/passive reductions, the pair and common
omniscience splits, and actual code transports before claiming the full
unrestricted manuscript theorem. See the repository's top-level theorem
index for the current status of that final assembly.

`verification/ResidualUploadAudit.lean` and
`verification/CommonTripodAudit.lean` print dependencies of the main results.
The permitted foundations are Lean's standard classical axioms:
`propext`, `Classical.choice`, and `Quot.sound`.
