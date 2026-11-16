# Independent source audit: demand-cycle repair

Frozen source: `../source/TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.
Target: `thm:endpoint`, beginning at line 1609, including the positive and
reverse cycles and the original-field scalar-upload clause.

## Source-facing statements

`CycleSourceEndpoint.positive_directSum` and `negative_directSum` assert all
clauses on the literal direct sum of the canonical original Jordan task and
the directed scalar cycle. They have no activity, chart, converse, optimality,
profile, or relay-existence input. Their only parameters are the original
finite field and the natural component index. The library index n denotes
source component size n+1; consequently all source sizes at least one are
covered, including size one.

The `Repair` conclusion retains an actual coefficient subspace P, local
generation, relay feasibility, dimension `3*(n+1)+4`, equality of that dimension
to the actual `T.uploadOptimum`, exact first-family increment, and all nine
second-family equalities. It additionally gives an original-field linear code
of blocklength one, exactly that many scalar upload symbols, and upload cost
equal to that dimension.

The positive target is Lean first-coordinate 1, source e2; the reverse target
is Lean coordinate 3, source e4. The profile order is the source order
(123,132,213,231,312,321).

## Genuine relation to the source coordinates

`CycleDirectSumCoordinates.map_directSum` and `map_reverseDirectSum` are
literal equalities of all side and signal subspaces under an explicitly
constructed linear equivalence. They identify the original resonant task
plus the three directed edges with the cycle repair coordinate model, not
merely a task having the same dimension vector or profile.

`CycleRepair.relayMap` is the positive uploaded coefficient map, and
`reverseRelayMap` is the reverse map. Their injectivity proves exactly 3n+4
independent uploaded coefficients for source size n. `relay_decomposition`
and its reverse version prove local availability. The explicit encoders and
decoders in `CycleRepair` implement the displayed source uploads and demands.
`CycleRepair.canonical_positive_repair` and the corresponding reverse
statement already supplied the exact rank, local feasibility and every
profile entry; this audit adds the previously missing operational optimality.

The source's nilpotent block is in source-vector coordinates. The library
uses its transpose on coefficient rows. `JordanResonance.transpose_pairing`
checks the transpose convention, and `sourceColumn_not_mem_range` verifies
the required h outside the image. There is no hidden characteristic exception.

## New nonlinear optimality proof

`CycleUploadOptimality` establishes all intrinsic activity conditions from
the original cycle geometry. Side spaces are pairwise disjoint, span the
ambient space, and each has rank n+2 in the generic size-n coordinate model.
Each signal has rank 2n+3 and each pair intersection rank n+1, so every signal
pair spans the full ambient space of dimension 3n+5.

The common triple signal intersection is zero by the proved fixed-head
Jordan condition. For the active tripod row, an explicit fixed vector w with
A*w=w and H*w=1 gives a signed zero-private witness. If p is in
A0 intersect (A1+A2), its only possible surviving coordinate is V. Let
v=p_V*w and q=(v,v,v;0,0,0,0,0). Then q lies in U0 intersect U1 and p+q lies
in U2, so p lies in U2+(U0 intersect U1). This proves precisely the intrinsic
tripod bridge used by `ResidualComponentAdditivity.code_lower`.

It would be incorrect to assume the stronger full identity
U2+(U0 intersect U1)=F here: that join has dimension 3n+4 in ambient dimension
3n+5. The new proof does not make that assumption. For the reverse orientation,
the exact `cycleFlip_task` equality and a proved first-two-users swap preserve
the needed intrinsic conditions; the inverse automorphism retains the fixed
head witness and the joint-zero condition.

The genuine residual nonlinear converse applies to every finite-alphabet
zero-error code and every positive blocklength. `minimum_upload` includes the
closed regularized region. The rank expression is calculated as
`2*(3n+5)-3*(n+2)=3n+4`. Thus `canonical_positive_optimal` and
`canonical_reverse_optimal` equate the actual constructed relay rank to
operational U*, not only to a symbolic additive formula or a linear minimum.

`CycleSourceEndpoint.repair_of_equiv` transports exact profiles and the
physical relay through the explicit direct-sum coordinates. Operational U*
transport follows from the proved coordinate retraction, and the actual
length-one code is constructed from that relay. The converse forces its
upload cost to equal its nominal scalar upload count.

## Verification and scope

Focused compilation is recorded in `logs/cycle-source-endpoint-build.log`.
`verification/CycleSourceEndpointAudit.lean` checks the main geometry,
operational and source-facing roots and the entire imported project theorem
closure against the whitelist `propext`, `Classical.choice`, `Quot.sound`.
Its log is `verification/cycle-source-endpoint-axioms.log`. The audit passed
for all 4,632 imported project theorem roots, and each endpoint printed only
those three standard axioms. All three new modules compiled without warnings.

This closes exactly the local demand-cycle claim. It does not assert that a
global algorithm has extracted enough cycles, allocated them, or constructed
the final joint-region endpoint; those remain separate assembly claims.

## Independent conclusion

The independent final semantic reviewer checked the compiled `Repair`
definition and eight actual geometry, optimality and direct-sum signatures in
`verification/FinalCycleReview20261008.lean`. That independent audit also
passed with exactly the three standard axioms. It confirmed the coordinate
chart, transpose convention, both orientations, exact rank-to-U* equality,
all fifteen entries, and the original-field scalar count.

Verdict: `thm:endpoint` is `reviewed_complete`.
