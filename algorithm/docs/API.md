# Public API — three-user-codes 1.5.0

## Field, Matrix and Task

`Field(q, modulus=None)` represents GF(q), for prime-power q < 2**64.
Extension-field elements encode polynomial coefficients in base p; multiplication
uses an irreducible polynomial, not integer arithmetic modulo q. A supplied
modulus must be monic and irreducible. Elements must be Python integers in
`[0,q)`, excluding bool. Preserve the field representation across processes.

`Matrix(field, rows, ncols=None)` is immutable. Explicit `ncols` preserves the
ambient width of an empty matrix. Matrix rows are linear functions; source
samples are columns. Public operations include `@`, `+`, `-`, `.T`, `.shape`,
`.to_list()` and dictionary conversion. Incorrect fields/shapes and non-integer
coefficients are rejected. Private trusted constructors are not public API.

`three_user_codes.linalg` provides exact `rref`, `rank`, `nullspace`, `solve`,
`inverse`, `determinant`, `coordinates`, `row_basis`, `row_sum`, `intersection`,
`contains`, `quotient_rank`, `extend_basis`, `eye`, `zeros`, `lift` and stack
helpers. No floating-point rank tolerance is involved.

`Task(field, side, demand)` accepts exactly three observation and three demand
matrices of equal source width. All requested functions must lie in the joint
observation span. `Task.from_rows(field, side, demand, *, n=None)` accepts row
collections; all-empty input requires explicit `n`. Canonical rowspaces are in
`.side` and `.demand`; `.original_side` and `.original_demand` retain the exact
input row order and redundant rows. `.augmented` contains the three side-plus-
demand spaces. `task.lift(L)` uses instance-major coordinates.

## Exact target values

`upload_cost(task)` returns the exact `Fraction` upload optimum.
`upload_parameters(task)` exposes the normal-form integers `rho`, `r0`, `b`,
`c`, `tau` and their `.omega` and `.cost` properties.

`broadcast_profile(side, augmented)` returns a `BroadcastProfile` with `.first`
(six F branches), `.second` (nine Q branches), `.cost`, `.branches` and `.doubled`.
The first order is 123, 132, 213, 231, 312, 321; the second order is Q11 to Q33
in row-major order. See manual page 3 for the formulas.

## Compilation

```python
result = compile_task(
    task,
    max_states=100_000,
    max_seconds=60.0,
    fast_paths=True,
    force_blocklength=None,
    max_cache_entries=2048,
    cancel_event=None,
    progress=None,
    progress_interval=0.25,
)
```

The default chooses original-field L=1 if both exact optimal costs are integral,
and L=2 otherwise. This minimum-blocklength contract follows the supplied
manuscript, Theorem 1, equation (18), and also applies with `fast_paths=False`.
`force_blocklength` accepts only 1 or 2. Explicit 2 returns exactly two original-
field instances; forcing 1 when a denominator requires 2 raises
`BlocklengthError`. No global GF(4) promotion is performed.

Structural construction can fail without making the task infeasible. Complete
search continues at the chosen L. Resource exhaustion raises
`SearchBudgetExceeded`. Exhausting a complete unbudgeted search where the
existence theorem guarantees a code raises `ConstructionError`, indicating an
implementation/theorem consistency issue.

`max_states=None` and `max_seconds=None` remove their limits. Generic search
remains exponential. Time is cooperative, including algebra checkpoints, and
includes bounds, construction and verification. It is not a preemptive process
timeout. `max_cache_entries=0` disables search memoization, not matrix-local
arithmetic reuse. Entry/cell cache limits are not process RSS limits.

`cancel_event` implements `is_set()`; a `threading.Event` works. `progress`
receives immutable `ProgressEvent(stage, search_states, elapsed_seconds)`.
Callbacks run synchronously; exceptions propagate. Stage changes force a
notification; intermediate notifications are throttled by `progress_interval`.
Nested compilation restores its surrounding context on success or failure.

`CompileResult` exposes `.certificate`, `.upload_optimum`, `.broadcast_optimum`,
`.strategy`, `.stats` and `.input_fingerprint`.
`result.verify(task)` verifies original input binding, all-source identities and
both recomputed target costs. `result.operating_code(task)` verifies before
creating an executable adapter. Strategy strings and counters are diagnostic,
not an integration dispatch API. Search-state counts include visited prefixes
and should not be treated as comparable units of work across implementations.

## Active reduction

```python
from three_user_codes import active_reduce

reduction = active_reduce(task)
assert reduction.verify(task)
residual = reduction.residual.task
embedding = reduction.residual.embedding
# A component row E maps to source coordinates as E @ embedding.
```

`ActiveReduction` also exposes `.omniscience`, `.passive`, `.parameters`,
`.components` and `.removed_dimension`. Each `ReducedComponent` has `.task`
and `.embedding`, with shape `(component.task.n, task.n)`. Verification checks
side/augmented reconstruction and roles. It does not itself construct a final
operating code. Multi-component recognition is an internal optimization; use
`compile_task` as its stable public entry point.

## Execution

```python
code = result.operating_code(task)
uploads = code.encode_uploads(observations)
signal = code.broadcast(uploads)
outputs = code.decode_all(observations, signal)
execution = code.execute(observations)  # same protocol
for execution in code.iter_execute(observation_batches):
    consume(execution.decoded)
```

Each Matrix column is one independent complete L-instance block. Each user
encoder receives only that user's observations. The relay receives uploads;
a decoder receives its local observations plus the broadcast. No encoder
requires the full source. Original redundant measurements and output order
are restored. `code.original_side` and `code.original_demand` expose the lifted
original matrices, useful for simulation and integration checks.

`OperatingCode(certificate, task)` permits adapting a semantically equivalent
row representation. `result.operating_code(task)` additionally checks the
result's original-representation fingerprint. Use the latter for normal
application integration.

## Certificates and JSON

`CodeCertificate` contains `.task`, `.uploads`, `.broadcast`, `.local_maps`,
`.decoders`, `.side_decoders`, `.blocklength` and `.base_field`. Its `.B` aliases
`.broadcast`; `.stacked_upload` and `.signal` expose the combined maps.
`.verify(expected_upload_count=None, expected_broadcast_count=None)` checks exact
local-generation and decoder identities. Expected counts additionally require
both the transmitted row count and rank to equal the target. Feasibility alone
does not establish global optimality.

`save_task(task, path)` / `load_task(path)` round-trip task input.
`save_code(result, task, path)` verifies and atomically writes a v2 result.
`load_code(path, expected_fingerprint=None, allow_legacy=True, limits=ReadLimits())`
returns `(result, original_task)` after re-verification. Use
`allow_legacy=False` to require the current result wrapper.

Fingerprints bind field encoding, source width and exact original side/demand
rows. They are not digital signatures. Pin an independently trusted digest
through `expected_fingerprint` when required. `ReadLimits` defaults to 32 MiB,
four million matrix cells, 100,000 rows/columns and imported blocklength 4,096.
These guard allocation, not total algebraic runtime. The import limit does not
change the new-compilation L<=2 guarantee. See SECURITY.md.

## Standalone broadcast API

`build_lcbc(A, W, *, round_up=False)` requires integer optimum by default.
`round_up=True` opts into a scalar ceiling budget; the returned `LCBCCode.cost`
is the realized integer length. `lcbc_parameters(A, W).cost` retains the exact
rational optimum. For q>=3 the manuscript's general construction applies;
for q=2 the separated-side spanning construction has additional hypotheses.

`BinaryScalarRealizationUnavailable` means this sufficient construction did
not succeed, not that a scalar code is impossible. Use `compile_task` for the
end-to-end task and its minimum-blocklength contract. The compiler does not
round its final upload or broadcast target.

## Errors and CLI

| Error / status | Meaning | Exit |
|---|---|---:|
| Success | Requested operation completed and verified where applicable | 0 |
| `ConstructionError`, internal algebra consistency errors | Implementation invariant failed | 1 |
| `BlocklengthError` | Requested original-field length is insufficient | 2 |
| `InputFormatError`, invalid values/types, `VerificationError` | Invalid input or failed verification | 2 |
| `SearchBudgetExceeded` | Resource stop, not infeasibility | 3 |
| `CompilationCancelled`, Ctrl-C | Caller interruption | 130 |

CLI subcommands are `demo`, `compile`, `inspect`, `verify`, `simulate`.
`--progress` writes JSON lines to stderr; final results are JSON on stdout.
`--debug` before the subcommand preserves internal consistency tracebacks.
Unexpected callback exceptions retain their original Python type.
`--blocklength` is preferred; `--force-working-blocklength` remains a compatible
alias with original-field semantics. CLI `inspect` reports
`minimum_linear_blocklength`; compile summaries also report
`blocklength_is_minimal`.
