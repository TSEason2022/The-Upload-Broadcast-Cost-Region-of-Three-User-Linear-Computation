# Technical overview

## Model

Let x be a column vector over a finite field. User i observes A_i x and requests W_i x. There are exactly three users. Upload encoders use only their respective users' observations; the relay computes its common broadcast from those uploads. User i decodes using its observation and the common broadcast. Tasks must satisfy the feasibility conditions of the model.

For a linear code across L source instances, the normalized total upload cost is the total number of uploaded field symbols divided by L. The normalized broadcast cost is the number of broadcast field symbols divided by L. Redundant original observation rows and the order of requested outputs are handled by the implementation.

## Why joint design matters

The minimum total upload with unrestricted broadcasting and the minimum broadcast with a fully informed server give two separate lower bounds. Matching each bound separately does not show that one scheme can match both. An upload-optimal relay observation can lose the structure needed for an optimal broadcast.

The research resolves this issue by using the design freedom within upload-optimal constructions. Components are coordinated through their broadcast profiles, with demand-cycle adjustments when required. The resulting joint construction attains both bounds. The analytical cost-region statement also includes nonlinear fixed-length zero-error codes; testing finitely many linear examples does not prove that converse.

## Executable construction

The Python package operates on exact finite-field matrices. It analyzes a task, selects a supported structural construction or an exact-search fallback, constructs encoders and decoders, and verifies the resulting certificate against the original task. Finite extension fields are supported.

A successful concrete certificate checks exact linear identities, ranks and costs over the requested field and blocklength. The independent benchmark verifier additionally evaluates original source basis vectors using separate polynomial field arithmetic. This is a computational check on returned codes, not a proof that the executable implements every mathematical theorem.

The original-field blocklength contract is L = 1 when both optimal normalized costs are integers, and L = 2 otherwise. A resource-budget failure does not change that blocklength or establish infeasibility. Generic unrestricted fallback search can take exponential time.

## Formalization

The Lean development separates finite-dimensional linear algebra, entropy, allocation, code construction and operational region results. The [module guide](../lean/docs/MODULE_GUIDE.md) explains the library; [UploadBroadcast.lean](../lean/UploadBroadcast.lean) is its umbrella import.

The trust boundary permits only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. The verification scripts audit theorem dependencies and safe project declarations. Kernel checking establishes the compiled declarations with their actual hypotheses. A separate statement review records how those declarations correspond to a particular manuscript snapshot.

The Python and Lean implementations have separate source identities and validation evidence. No executable-to-formal-library refinement certificate is supplied.
