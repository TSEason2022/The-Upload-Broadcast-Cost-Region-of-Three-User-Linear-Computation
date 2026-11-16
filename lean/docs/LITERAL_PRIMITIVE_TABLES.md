# Exact primitive-coordinate verification

Source: frozen `../source/TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`,
lines 2540–2629, tables `tab:primitive-flags` and `tab:primitive-relays`.
The parameterized blocks immediately following the tables are covered separately
in `LITERAL_THETA_BLOCKS.md`.

## Scope

This supplements the independent proof of the same-chart lemma. It verifies the
literal coordinate constructions themselves. The seven base flag rows and all ten
relay choices are transcribed exactly, including minus signs and the empty demand
list for O. The definitions interpret the listed vectors as columns; transposing
that storage convention does not change the actual displayed coefficient vectors.
No indecomposability assumption is made about these explicit examples.

The separate modules imported by `UploadBroadcast/LiteralPrimitiveTables.lean`
use namespaces `UploadBroadcast.LiteralPrimitiveTables.T1_2`, `T1_3`, `T2_3`,
`T3_2`, `R1_1`, `R2`, `O_1`, `O_2`, `O_3`, and `H_1`.

In each namespace:

- `side{i}Columns`, `demand{i}Columns`, and `signal{i}Columns` give the literal
  vectors. `signal{i}_from_demands` checks the source's A_i plus B_i convention.
- `side{i}_literal` and `signal{i}_literal` identify those actual column spans
  with the constraint-kernel descriptions used for efficient rank computation.
- `task` is an actual feasible `Task`; `side_spanning` and
  `side_pairwise_disjoint` establish its full side geometry.
- `relayForms` is exactly the displayed common-kernel matrix. `dim_relay`,
  `relay_columns`, `locally_generated`, and `relay_feasible` establish its
  dimension, an explicit basis, actual local generation, and actual feasibility.
- `inducedTask` uses the literal intersections P∩A_i and P∩U_i in the same
  ambient coordinate vector space. Its six dimensions are proved, not assumed.
- `full_rankConditions` and `induced_rankConditions` establish the actual
  pair-sum, pair-intersection spanning, pair-conditional, and triple-conditional
  ranks. Separate exact finrank theorems provide every pair/triple intersection
  used in deriving these facts.
- `full_first_profile`, `induced_first_profile`, `full_second_profile`, and
  `induced_second_profile` give the actual six first entries and nine doubled
  second entries in the paper's established order.
- `relation_slices_partition` and `relationComponent{i}_from_side` bind the
  three components to the respective side-column slices of the actual relation
  basis; `relationComponent{i}_in_side` proves membership in each actual side.
  `relation_space` certifies a basis of the kernel of the actual side-sum
  matrix. The three `relation_value{i}` identities give the displayed form's
  values on its three side components; `relation_sum` proves they are relations.
  For the hyperplane cases these values are (0,1,−1), up to the stated sign and
  arm order, and `relay_form_vanishes` proves vanishing on the suffixed signal.
  For R2, `wedge_from_relation_components` binds the displayed wedge matrix
  to those actual form evaluations; `actual_wedge_determinant` proves its
  determinant is exactly one. `first_form_vanishes` and
  `second_form_vanishes` prove that each individual R2 form annihilates its
  designated actual signal space.

These endpoints quantify over an arbitrary field, without a characteristic or
cardinality assumption. In particular the literal table claims hold in
characteristic two. The separate theta blocks require theta≠0,1 as in the source.
This scope does not claim to reproduce the algebraic-geometric open-orbit
transfer argument. The required same-chart conclusion, rather than that
geometric transfer theorem, has a separate independent formal proof.

## Certificate trust boundary

`LiteralMatrixCertificates.rank_int_certificate` transports exact integer matrix
identities into an arbitrary field. For a claimed rank r, the certificate supplies
X,Y,L,R with XY=M and LMR=I_r. Factorization bounds rank above by r; the split
identity bounds it below by r. The kernel/range, column-span, and rank-nullity
lemmas then prove actual submodule dimensions. This is not rational arithmetic
being reinterpreted as a proof in other characteristics.

There are 550 generated rank certificates. Every integer equality is proved by
ordinary Lean `decide`, with kernel checking enabled. Neither an external CAS
result, finite-prime testing, native evaluation, a new axiom, nor the desired rank
is accepted as an assumption. SymPy is used only to find witnesses for generation.
The all-declaration axiom audit includes proof-bearing definitions and the helper
module, not only the advertised endpoint theorem names.

## Reproduction

From the repository root, source `scripts/env.sh` and compile the literal modules
one at a time, followed by `LiteralPrimitiveTables.lean` and the audit script.
The release clean-build driver includes every module and checks them sequentially.
A focused independent check can use:

```sh
source scripts/env.sh
for m in LiteralMatrixCertificates LiteralPrimitiveT1_2 LiteralPrimitiveT1_3 \
         LiteralPrimitiveT2_3 LiteralPrimitiveT3_2 LiteralPrimitiveR1_1 \
         LiteralPrimitiveR2 LiteralPrimitiveO_1 LiteralPrimitiveO_2 \
         LiteralPrimitiveO_3 LiteralPrimitiveH_1 LiteralPrimitiveTables; do
  lake build "UploadBroadcast.$m" || exit 1
done
lake env lean scripts/AuditLiteralPrimitiveTables.lean
```

Checking one target at a time avoids concurrently loading the substantial
shared library into ten Lean processes.

Optional supplementary source/generator checks, tested with SymPy 1.14.0:

- `python scripts/audit_literal_primitive_tables.py`
- `python scripts/generate_literal_primitive_certificates.py --check`

The former authenticates the frozen source hash, parses all table cells, checks
that every transcribed matrix agrees, and computes the exact rational diagnostic
ranks. The latter regenerates the exact integer certificates and compares the
files without changing them. Neither check substitutes for the Lean build.

## Validation on 2026-10-08

- All ten concrete modules, the general bridge, and the umbrella compiled cleanly.
- `AuditLiteralPrimitiveTables.lean` checked every one of the 1,807 safe
  declarations originating in these modules, including proof-bearing definitions.
  The complete reachable axiom set is `propext`, `Quot.sound`, `Classical.choice`.
- The source lexical gate passed across the repository's 413 current Lean files.
- Source transcription/hash checks and deterministic regeneration checks passed.
- No literal-coordinate counterexample was found, and the frozen TeX hash was
  unchanged. Lean establishes the claimed characteristic-uniform results;
  supplementary rational diagnostics alone are not the proof.

Evidence is in `logs/literal-primitive-tables-build.log`,
`logs/literal-primitive-axioms.log`, `logs/literal-primitive-regeneration.log`,
`logs/literal-primitive-symbolic.log`, and
`logs/literal-construction-source-hashes.log`. The repository's final clean
integrated rebuild and its independent semantic review remain separate release
checks; this focused validation does not impersonate them.
