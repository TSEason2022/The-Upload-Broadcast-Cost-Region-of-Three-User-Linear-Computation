# Security and resource boundaries

This package implements exact algebra and coding, not constant-time
cryptography. Pivoting, table access, search and timing depend on input data.

Task and code loaders use strict JSON, reject duplicate keys/nonfinite values,
and verify fields, shapes and coefficients. `ReadLimits` defaults to 32 MiB,
four million matrix cells, 100,000 rows/columns and imported blocklength 4,096.
The task and certificate share the matrix budget. Expanded execution conventions
are checked before allocation. These are input/allocation guards, not a security
sandbox, CPU limit or resident-memory cap.

Imported codes are reverified using exact local-generation and decoding
identities. Claimed costs are recomputed. Stored verification summaries are not
trusted. Mathematical optimality still depends on the project theorem.

Compiled-code v2 fingerprints bind the field representation, source width and
original side/demand rows in their original order. A hash stored beside its data
is not a digital signature. Pin a separately trusted digest with
`load_code(path, expected_fingerprint=...)` when required. Use
`allow_legacy=False` to require the current result wrapper.

Generic search can be exponential. `max_seconds` is cooperative, including
algebra checkpoints. Synchronous callbacks can block and cannot be preempted by
the library. Use a supervised process with OS resource limits for hard deadlines
or untrusted workloads. Search cache caps do not cap total process memory.

The runtime needs no network access, shell execution, pickle or eval. Keep
public validation enabled; private trusted constructors are internal only.
See the manual and API reference for operational error handling.
