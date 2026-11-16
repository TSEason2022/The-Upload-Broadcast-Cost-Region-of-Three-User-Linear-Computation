# Reusable module map

This is an orientation guide, not a replacement for inspecting theorem types or
`coverage.json`. Import a concrete module to minimize dependencies; the root
`UploadBroadcast` import is a convenience entry point, not the release inventory.
The generated `verification-results/module-inventory.json` is authoritative for
which library modules the clean release check actually compiled.

- **Operational model:** `Model`, `LinearCode`, and operational/region modules define
  tasks, admissible communication codes, costs, and their transport. Read the
  precise field, blocklength, finiteness, and feasibility hypotheses before reuse.
- **Entropy and converses:** `LinearEntropy`, `BroadcastShannon`, and the upload
  converse modules connect concrete finite random variables, rank, and entropy.
  Shannon inequalities are proved through the pinned PFR dependency.
- **Linear algebra and decomposition:** task decomposition, active reduction,
  common-tripod, quiver, regular, resonant, and finite-coordinate modules implement
  the manuscript's structural reductions and source rank identities.
- **Concrete coding:** relay, cycle, omniscience, binary-menu, and finite-assembly
  modules construct actual codes and prove their local recoverability and costs.
- **Paper interfaces:** `OriginalUploadTheorem` and other endpoint wrappers expose
  source-facing statements. Use `source-ledger/named-claims.json` in a final
  artifact to locate each original named claim and its exact Lean declarations.
- **Audits:** `scripts/AuditAxioms.lean` collects transitive theorem axioms;
  `check_all_modules.py` extends its roots to every library module.
  `verification/CoverageDeclarations.lean` checks mapped declarations, while
  semantic audit documents explain why those declarations match the source.

The groups above describe roles, not independent semantic certifications. The
same theorem may depend on several groups. A claim remains conditional if its
Lean type assumes a structural certificate or a code whose existence has not
been established for the original class of inputs.

For a small installation test use `Smoke.lean`; it proves a real polynomial
identity and prints its axioms. It is deliberately not counted as a paper result.

For twelve compiled public-API examples and the existence-versus-execution distinctions, see [Reusing the proofs](REUSING_THE_PROOFS.md) and `../examples/ReusableAPI.lean`. The clean integrated gate recompiles that file and rejects any unapproved axiom in its explicitly listed declarations.
