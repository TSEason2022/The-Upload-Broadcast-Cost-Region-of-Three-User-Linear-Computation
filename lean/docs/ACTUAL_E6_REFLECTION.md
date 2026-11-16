# Actual E6 reflection and nonzero-defect consequences

This development bridges the earlier dimension-only calculations to actual
representations. It uses no Kac theorem, no assumed Tits bound, no presumed
normal form, and no assumption of the desired uniqueness conclusion.

## Module interfaces

* `QuiverRepresentation.lean`: arbitrary orientations, vertex module families,
  arrow maps, commuting Hom/Iso, actual direct sums, kernel/image splitting of
  idempotents, and equivalence of direct-sum indecomposability with nonzero
  and trivial idempotents.
* `ReflectionEquivalence.lean`: explicit local kernels and cokernels, inverse
  recovery isomorphisms and naturality, Hom equivalences, zero and composition
  preservation, direct sums, indecomposability preservation, supported-simple
  exceptions, and actual rank-nullity dimension formulas. The attached star
  may have an arbitrary unchanged peripheral quiver.
* `QuiverReindex.lean`: graph relabelling with fully faithful Hom transport;
  explicit sink/source charts at any vertex; actual reflections back in the
  original vertex labels; finite-dimensionality, indecomposability and exact
  dimension formulas; reverse isomorphism transport under epi/mono conditions.
* `ReflectionIteration.lean`: admissible words carry each successive sink or
  source proof. Word execution acts on actual representations. Every word
  either reaches an actual vertex-simple through valid epi/mono steps or
  follows its verified dimension action. A negative dimension endpoint forces
  a simple. Simultaneous reflection and reverse isomorphism transport prove
  original-field uniqueness for such a word.
* `E6Reflection.lean`: explicit seven-step source and sink words, verified
  orientation return, equality with the previous Coxeter arithmetic, 42-step
  blocks, and their arbitrary repetitions. The resulting theorems are
  `negative_defect_reaches_simple`, `positive_defect_reaches_simple`,
  `nonzero_defect_reaches_simple`, and `nonzero_defect_unique`.
* `QuiverTits.lean`: proves the actual dimension transformations preserve the
  graph quadratic form, proves the form is one at vertex-simples, transports
  this along actual reachability, and identifies the inward E6 form with the
  manuscript's polynomial. `E6Reflection.nonzero_defect_tits_one` concludes
  q = 1 for any finite-dimensional nonzero-defect indecomposable inward E6
  representation.
* `SourceHomVanishing.lean`: a numerical no-selected-simple-prefix certificate
  is turned into actual local injectivity along a source word; the resulting
  Hom equivalence preserves zero. A supported source has no nonzero maps into
  an object with injective aggregate outgoing map, and this vanishing can be
  transported backwards along the whole certified word.
* `TaskQuiverBridge.lean`: constructs the paper's actual six-subspace task
  representation, proves exact Hom and isomorphism bridges, proves both
  directions of indecomposability equivalence, and applies the q=1 and
  uniqueness conclusions directly to the original task.
* `ScalarEndReflection.lean`: proves all endomorphisms are scalar at a
  vertex-simple and transports this property backwards through the actual
  Hom equivalences; every nonzero-defect indecomposable task therefore has
  scalar stable endomorphisms over its original field.
* `ScalarEndBaseChange.lean`: arbitrary-basis tensor coefficients of every
  extended stable map are original-field stable maps. Scalarity of all these
  coefficients forces the extended map itself to be scalar. This proves
  `Task.nonzero_defect_extend_indec` for arbitrary field extensions, without
  finite-extension, algebraic-closure, or absolute-splitting hypotheses.
* `QuiverHomLinear.lean`: puts the actual commuting Hom spaces in vector
  spaces and upgrades reflection and word Hom bijections to linear
  equivalences, including checked Hom-finrank transport.
* `TaskComponentBridge.lean`: restricts an actual indecomposable ambient
  component to its own module and proves its spaces are the actual
  intersections. The q=1 and arbitrary-extension conclusions therefore apply
  directly to components of the original task decomposition.
* `QuiverEuler.lean`: proves simultaneous source-reflection invariance of the
  directed Euler pairing. Stopping when either indecomposable reaches a
  selected simple gives the exact formula
  `finrank Hom(R,S) = max(0, Euler(R,S))` whenever the target has positive
  defect. No genericity, Ext-vanishing, or probe-survival hypothesis is used.

## Mathematical scope

The E6 theorems quantify over fields `K : Type` and finite-dimensional vertex
modules, with actual direct-sum indecomposability. They impose no inward-arrow
injectivity restriction, so they apply in particular to subspace flags once
the flag-to-representation bridge is supplied.

These results close the nonzero-defect real-root, base-field uniqueness, and
absolute-indecomposability steps for the original six-subspace tasks. They do
not by themselves prove the zero-defect regular classification, the complete
canonical model table, or any communication/relay theorem. In particular,
the individual intersection-probe identifications, their assembly into the
required rank conditions, and operational coding statements remain separate
obligations.

## Verification

Run `lake build UploadBroadcast.QuiverTits UploadBroadcast.SourceHomVanishing`,
`lake env lean scripts/AuditActualReflection.lean`, and
`python3 scripts/audit_source.py`.
The targeted audit scans QuiverRepresentation, ReflectionEquivalence, and
E6Reflection namespaces and permits only standard classical axioms
`propext`, `Classical.choice`, and `Quot.sound`.

## Checked completed stack (2026-10-08)

The targeted build of `TaskComponentBridge`, `QuiverEuler`,
`ScalarEndBaseChange`, and `QuiverHomLinear` passed without warnings. These
imports transitively check the reflection, actual E6 iteration, task bridge,
absolute-indecomposability, and Hom-rank modules described above.

`AuditActualReflection.lean` passed for 734 namespaced theorems, allowing only
`propext`, `Classical.choice`, and `Quot.sound`. The source audit passed across
160 Lean files at this checkpoint. Logs are
`logs/actual-reflection-build.log`, `logs/actual-reflection-axioms.log`, and
`logs/actual-reflection-source-audit.log`. This is a targeted stack check;
whole-project integration remains a separate check.
