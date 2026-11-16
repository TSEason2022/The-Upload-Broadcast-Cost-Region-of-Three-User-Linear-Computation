# Kernel trust boundary audit, 2026-10-08

## Result and scope

No source-level proof placeholder, custom logical axiom, native-computation
proof escape, unchecked declaration injection, or disabled kernel check was
found in the reviewed project sources and build configuration. The project
uses ordinary kernel-checked proof terms, including computational `decide`
proofs. Resource limits and linter options do not disable kernel checking.

This review strengthened two checks without editing mathematical proofs:

- `scripts/audit_source.py` now scans root, library, script, and verification
  Lean sources. It rejects explicit placeholders, user-authored axioms/unsafe
  declarations, known native-reduction and unchecked-environment APIs, and the
  kernel-skip option. Custom command metaprograms in the mathematical library
  require review. The audit metaprograms outside that library were inspected:
  they read declarations, collect dependencies, print results, and report errors.
- `scripts/AuditAllDeclarations.lean` inventories declarations by their defining
  **module**, then audits every safe logical declaration. This includes private
  names, declarations outside the `UploadBroadcast` namespace, proof-bearing
  definitions, structures, and otherwise unused logical declarations. The
  existing namespaced theorem audit remains as a separate check.

The focused test of the new collector passed on the existing imported umbrella:
7,772 safe declarations, including 5,790 theorem declarations and 401 private or
out-of-namespace declarations, from 243 imported project modules. Its complete
reachable axiom set was `propext`, `Quot.sound`, and `Classical.choice`.
This was a **development-cache test of the collector**, not a fresh verification
of all subsequently edited sources. Its log is
`verification/kernel-trust-axiom-audit-20261008.log` in the development tree.
The release's fresh all-module check and content-bound report supersede these
provisional counts. No entire-library rebuild was performed by this review.

Twelve lexical-gate regression tests and seven release-selection tests passed.
The lexical tests use temporary text fixtures only; they do not compile or add
unproved declarations to the project.

## Why the new root selection matters

A declaration namespace is not a module inventory. Lean private names are
internally prefixed, and a source file can define names in another namespace.
Also, a proof or proof-bearing structure can be stored in a `def` rather than a
`theorem`. Those are coverage blind spots of a namespace-and-theorem-only root
filter. They are not evidence that a public theorem's dependency closure was
incorrectly computed: private helper proofs reached by a public theorem were
already traversed by the previous collector.

The new collector obtains the defining module with
`Environment.getModuleIdxFor?`, accepts all safe declaration kinds from imported
`UploadBroadcast` modules, rejects empty root sets and missing checked roots,
and shares Lean's visited set across all roots. Lean's collector inspects both
types and values, including definitions and opaque proof values. Sharing the
visited set changes runtime, not which axioms are found. See the pinned
[collector implementation](https://github.com/leanprover/lean4/blob/v4.19.0/src/Lean/Util/CollectAxioms.lean).

The library source inventory is separately enumerated from disk by
`scripts/check_all_modules.py`. The generated audit imports every library
module, including modules omitted from the convenience umbrella. Each source is
built before the audits run. Merely invoking the collector against an old
umbrella `.olean` does not establish that coverage.

## Unsafe compiler implementation declarations

Lean's compiler creates unsafe implementation specializations and unsafe axiom
stubs for executable code. The focused imported environment contained 12,492
unsafe implementation declarations. These are counted separately and are not
logical roots. Safe kernel proofs cannot use unsafe declarations. A whitelist
applied blindly to all implementation stubs would therefore reject legitimate
compiled programs without identifying a logical proof assumption.

The distinction does not permit user-authored unsafe code: the source gate
rejects it. A safe declaration's complete logical dependency closure is still
audited, with exactly the same three-axiom whitelist. No additional logical
axiom is accepted because an implementation-only declaration was counted
separately. The relevant flags are defined in the pinned
[declaration implementation](https://github.com/leanprover/lean4/blob/v4.19.0/src/Lean/Declaration.lean).

## Exactly which axioms are allowed

- `propext`: logically equivalent propositions are equal.
- `Classical.choice`: from `Nonempty α`, obtain an element of `α`.
- `Quot.sound`: related representatives have equal quotient constructors.

These are standard explicit axioms of Lean's classical foundation. They are
not manuscript-specific claims and are not a claim of axiom-free mathematics.
They supplement Lean's underlying type theory and kernel rules, including
inductive types, universes, proof irrelevance, and quotient support.

Their pinned declarations are in
[Init/Core.lean](https://github.com/leanprover/lean4/blob/v4.19.0/src/Init/Core.lean)
and [Init/Prelude.lean](https://github.com/leanprover/lean4/blob/v4.19.0/src/Init/Prelude.lean).
`sorryAx`, project-specific axioms, `Lean.ofReduceBool`, `Lean.ofReduceNat`, and
`Lean.trustCompiler` are not allowed. A tactic or imported proof introducing
such a dependency fails the whitelist even if the tactic's spelling is absent
from the project. Native reduction is distinct from ordinary `decide`, whose
generated proof is checked by the kernel.

## Pinned upstream and executable identity

The observed Lean executable reports version 4.19.0 and full compiler commit
`6caaee842e9495688c1567e78c0e68dbb96942aa`. This agrees with the official
[Lean v4.19.0 release](https://github.com/leanprover/lean4/releases/tag/v4.19.0).
The direct dependency pins are the official
[mathlib revision c44e0c8](https://github.com/leanprover-community/mathlib4/commit/c44e0c8ee63ca166450922a373c7409c5d26b00b)
and [PFR revision 859f6b2](https://github.com/teorth/pfr/commit/859f6b23d5532de385cff18fc25381e715dba199),
both corresponding to their Lean 4.19.0 updates. All eleven dependency HEADs
and their tracked-source cleanliness matched the lockfile during this review.

`scripts/verify_toolchain.py` additionally checks actual executable version and
commit output against `toolchain-lock.json`, records executable hashes, and
rejects inherited import-path overrides. Executable self-identification and
hash recording identify the tested installation; they do not prove the entire
compiler/runtime supply chain correct.

## Compiled objects, source correspondence, and release gates

Normal Lean imports trust previously compiled object declarations. The focused
audit reported imported-object trust level 1025. An axiom collector reads the
loaded logical terms; it does not independently re-type-check every imported
object, authenticate a cache, or prove that an object was generated from the
source beside it. The pinned
[environment implementation](https://github.com/leanprover/lean4/blob/v4.19.0/src/Lean/Environment.lean)
documents this trust distinction.

The release process addresses stale **project** artifacts by creating a fresh
source-only snapshot, excluding project `.olean`, `.ilean`, object files,
traces, and other build artifacts, then compiling all library modules. Existing
loose `.olean` files in the development source tree must not be used as release
evidence. Source manifests are compared before and after verification and
again before packaging. Coverage declaration existence/type checks, both axiom
audits, source scanning, and warning/error rejection must all succeed.

Dependency caches are explicitly separate: the workflow may reuse official
mathlib compiled caches and existing dependency build artifacts. Matching
dependency Git revisions and clean tracked sources does **not** establish the
correctness or source correspondence of cached `.olean` bytes. Their provenance
and integrity remain in the operational trust boundary. No compiler rebuild,
full dependency rebuild, or independent external-kernel recheck is claimed.

The release scripts fail closed on their documented consistency checks, reject
optimized Python execution where assertions would disappear, require fresh
destinations and successful recorded gate outcomes, and bind evidence to exact
source hashes. These are reproducibility controls, not a tamper-proof security
system: an adversary able to replace scripts, binaries, manifests, and logs can
forge mutually consistent local evidence. Independently rerunning the published
checks is stronger than trusting a supplied success report. Checksums provide
content identity, not authorship authentication.

## What this audit cannot establish

A valid proof establishes its exact Lean proposition from its explicit
hypotheses. A theorem may legitimately be conditional, and an inappropriate or
impossible hypothesis can make a statement irrelevant to the manuscript while
remaining kernel-valid. Structures and definitions can also package assumptions.
The axiom audit does not decide whether those hypotheses were discharged in
the intended operational model. This is why manuscript-to-statement review,
coverage declaration inspection, and the separate semantic audit are required.
Human-reviewed coverage statuses are not themselves proofs.

The lexical gate is deliberately conservative and is not a sandbox for hostile
metaprogramming or a formal security proof. The ordinary trusted boundary
includes Lean's kernel implementation and its compiled executable, runtime and
platform behavior, imported object provenance, the declared standard axioms,
and correct interpretation of the stated hypotheses. This report claims no
absolute hardware infallibility and is not external academic peer review.

An accurate summary is: **the recorded project snapshot is verified relative
to the pinned Lean toolchain, the disclosed dependency-object trust boundary,
and the three standard axioms, with manuscript fidelity assessed separately.**
Use that statement only after the snapshot's final clean release gates pass.
