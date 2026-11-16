# Technical overview

## Model and costs

The source is $x\in\mathbb F_q^n$. The three users have prescribed observation matrices $A_i$ and demand matrices $W_i$ with the same source width. User $i$ observes $A_i x$ and requests $W_i x$. Observations may overlap, contain redundant rows, or already determine part or all of a user's demand.

The necessary and sufficient task-feasibility condition is

```math
\mathrm{row}(W_i)\subseteq
\mathrm{row}(A_1)+\mathrm{row}(A_2)+\mathrm{row}(A_3),
\qquad i=1,2,3.
```

A block contains $L$ computation instances. Each user sends one deterministic, noninteractive upload depending only on its own observation block. The relay starts without source information, receives the three uploads individually over noiseless links, and forms one common broadcast. Each user decodes from its observation block and that broadcast. Correctness is required for every source block; no source distribution is imposed. The mathematical model permits nonlinear maps coupling the $L$ instances.

Let $\mathcal M_i^{\mathrm{att}}$ and $\mathcal S^{\mathrm{att}}$ denote the upload and broadcast alphabets attainable as the source block varies. A code's costs are

```math
U_{\mathrm{code}}=\frac1L\sum_{i=1}^3\log_q|\mathcal M_i^{\mathrm{att}}|,
\qquad
D_{\mathrm{code}}=\frac1L\log_q|\mathcal S^{\mathrm{att}}|.
```

Both are measured in $q$-ary units per computation instance. Upload cost is the sum across users. For linear messages the alphabet logarithms equal the ranks of their source-to-message matrices; transmitted symbol counts agree when the transmitted coordinates are independent. A scalar code has $L=1$ and may transmit multiple symbols.

## Region and minimum blocklength

Define $\mathcal R_L$ as the set of budgets $(U,D)$ for which some length-$L$ code satisfies $U_{\mathrm{code}}\le U$ and $D_{\mathrm{code}}\le D$. Let $U^{\star}$ be the infimum total upload with unrestricted broadcast, and let $D^{\star}$ be the infimum broadcast cost when the server has the entire source, optimizing over all allowed blocklengths and codes.

**Proven in the accompanying research:** for every feasible three-user task over every finite field,

```math
\mathcal R_2=\overline{\bigcup_{L\ge1}\mathcal R_L}
=[U^{\star},\infty)\times[D^{\star},\infty).
```

The corner $(U^{\star},D^{\star})$ is attained by a linear code over the original field. Its least positive linear blocklength is one if both costs are integers and two otherwise. This integrality criterion concerns linear codes. The region converse allows nonlinear fixed-length zero-error coding, and an explicit binary example establishes that the uniform two-instance bound is also necessary when nonlinear codes are allowed. The rectangle describes cost budgets, not every pair of exact attained costs or a region of individual user upload rates.

## Why the construction is joint

An upload-optimal relay observation can require a broadcast cost strictly larger than $D^{\star}$. The joint construction chooses among upload-optimal observations to retain the fully informed broadcast optimum.

For three-user LCBC, the broadcast optimum is the maximum of 15 rank expressions: six indexed by user permutations and nine indexed by ordered pairs. Under task direct sums, corresponding profile entries add. Taking the maximum after adding entries can give a different result from adding the separate component maxima. Accordingly, the construction coordinates component choices through their full profiles and handles directed demand cycles jointly.

The [exact-cost section of the algorithm manual](../algorithm/docs/ALGORITHM_MANUAL.md#3-exact-costs-and-blocklength) gives the 15 broadcast expressions and the upload formula. Their executable definitions are [profile.py](../algorithm/three_user_codes/profile.py) and [upload_bound.py](../algorithm/three_user_codes/upload_bound.py).

## Executable construction and certificates

The Python package accepts exactly three observation and three demand matrices. It checks feasibility, computes rational target costs from the analytical formulas, attempts explicit constructions for recognized structures, and falls back to exhaustive finite-field subspace search when necessary. Original observation-row redundancy and requested output order are preserved by the execution adapter.

For the certificate equations below, $A_i$ and $W_i$ denote row-space bases of the supplied matrices; the execution adapter restores the original observation rows and requested output order. For $L$ instances, let $A_i^{[L]}=I_L\otimes A_i$ and $W_i^{[L]}=I_L\otimes W_i$, with instance-major source coordinates. A returned code supplies local upload maps $T_i$, a relay map $B$, and decoder maps $C_i,H_i$. Write $E_i$ for the upload matrix acting on the full source block and $E$ for their vertical concatenation. The certificate checks

```math
E_i=T_iA_i^{[L]},
\qquad
W_i^{[L]}=C_iBE+H_iA_i^{[L]},
\qquad i=1,2,3.
```

These exact identities establish that each upload uses only local observations and that each decoder recovers its requested output for every source block. `CompileResult.verify(task)` also checks source/field consistency, binding to the original input, recomputed target costs, and the required transmitted row counts and ranks:

```math
\sum_{i=1}^3\mathrm{rank}(E_i)=LU^{\star},
\qquad \mathrm{rank}(BE)=LD^{\star}.
```

The optimality interpretation of those target costs comes from the mathematical results; checking a concrete certificate does not itself prove the universal optimum formulas.

The benchmark's separate verifier uses its own polynomial field arithmetic to evaluate the returned maps on every original source basis vector. Linearity extends these checks to all source vectors. This verifies returned codes independently of the package's arithmetic; it does not independently prove or derive the optimum formulas.

### Supported fields and resource limits

- The field API accepts prime-power orders $2\le q<2^{64}$. Extension-field elements use polynomial-basis representations. Automatic modulus selection has a bounded search; an explicit monic irreducible polynomial may be required. See the [field API](../algorithm/docs/API.md#field-matrix-and-task).
- By default, compilation uses the input field and chooses $L=1$ when both target costs are integers, and $L=2$ otherwise. `force_blocklength=2` explicitly requests two instances even when one would suffice.
- Default limits are 100,000 visited search states and 60 seconds of cooperative elapsed-time checking, including bounds, construction and verification. A separate supervising process is needed for a hard deadline.
- `SearchBudgetExceeded` reports resource exhaustion and preserves the selected field and blocklength. It does not establish infeasibility. Unrestricted fallback search can take exponential time.

See the [public API](../algorithm/docs/API.md) for execution, cancellation, validation and exception contracts.

## Lean formalization and its scope

The Lean development formalizes finite-dimensional linear algebra, finite-alphabet entropy, allocation, code existence and the operational region. The main original-field theorems are in [SourceMainTheorem.lean](../lean/UploadBroadcast/SourceMainTheorem.lean):

| Declaration in `UploadBroadcast.Task` | Conclusion |
| --- | --- |
| `main_region` | Both the two-instance budget region and the closed arbitrary-blocklength region equal the rectangle |
| `joint_two` | A two-instance linear code attains both optimal costs |
| `minimum_linear_blocklength` | The stated blocklength is least among all positive linear blocklengths attaining both optima |
| `scalar_joint_iff_integral` | A scalar linear code attains both optima exactly when both are integers |

`UploadBroadcast.nonlinear_uniform_bound_tight` supplies the binary obstruction to a universal one-instance guarantee, including nonlinear codes. [Reuse examples](../lean/docs/REUSING_THE_PROOFS.md) explain how to instantiate these statements; the [module guide](../lean/docs/MODULE_GUIDE.md) describes their dependencies.

The recorded Lean 4.19.0 run compiled 314 library modules. The coverage map associates 28 named manuscript results with 103 distinct theorem declarations checked for their types and transitive axiom dependencies. Both full-library axiom audits passed. The audits permit only `propext`, `Classical.choice` and `Quot.sound`; the Lean compiler and imported dependency objects remain part of the trusted environment. The run rebuilt project modules while reusing pinned upstream dependency objects.

Lean establishes the formal declarations under their stated hypotheses. Correspondence with the informal manuscript is a separate review recorded in the [current-source mapping](../lean/current-source-coverage.json). Some formal constructions use noncomputable classical choices, so this library is a proof development rather than an executable matrix synthesizer. The Python implementation and Lean formalization have separate source identities; no refinement theorem connects them.
