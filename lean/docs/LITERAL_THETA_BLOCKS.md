# Literal θ-dependent primitive blocks

`UploadBroadcast/LiteralThetaBlocks.lean` independently checks the actual
coefficient vectors in lines 2631–2667 of the frozen source
`../source/TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.
The source file is not edited.

## Scope

All Lean results hold over an arbitrary field `K : Type`; the nondegenerate
rank and profile results require only `θ ≠ 0` and `θ ≠ 1`. There is no
finite-field, characteristic-zero, algebraic-closure, indecomposability,
custom-axiom, or requested-profile hypothesis. The literal vector lists are
interpreted as `Submodule.span K (Set.range vectors)` by `vspan`.

The source phrase “every conditional rank for a pair intersection is one”
is read in its preceding rank-condition context: `crk(U_i ∩ U_j | A_j)`
for distinct `i,j`, so the conditioning arm participates in the pair. It does
not assert the same value for an arbitrary third-arm conditioning space.
For example, the full R₀ task has `crk(U₂ ∩ U₃ | A₁) = 2`. This is a scope
clarification, not a counterexample to the contextual source condition.

The full R₀ configuration is on `Fin 4 → K`, with coordinates `(x,y,z,w)`.
The D configuration is on `Fin 3 → K`. The relay is literally the span of
`x,y,z`, and `embed` is the fixed coordinate inclusion `(x,y,z) ↦ (x,y,z,0)`.

## Kernel-checked results

Namespace prefix: `UploadBroadcast.LiteralThetaBlocks`.

- `R0.mem_A0`, `mem_A1`, `mem_A2`, `mem_U0`, `mem_U1`, `mem_U2`, `mem_P`:
  exact membership equations of every displayed generator span.
- `R0.pair01`, `pair02`, `pair12`: the full pair intersections are respectively
  the spans of `(1,1,1,0)`, `(1,θ,θ,0)`, and
  `(1,θ,1,0),(0,−θ,0,1)`. Their dimensions are `(1,1,2)`.
- `D.pair01`, `pair02`, `pair12`: the three pair lines are the spans of
  `(1,1,1)`, `(1,θ,θ)`, and `(1,θ,1)`.
- `R0.triple_zero`, `D.triple_zero`: the actual triple intersections are zero,
  using only `θ ≠ 1`.
- `R0.side_signal01` through `side_signal21`, `D.side_signal_zero`:
  exact remote side/signal intersections, with `θ ≠ 0` only where necessary.
- `R0.rank_conditions`, `D.rank_conditions`: side/signal dimensions, all
  pair spanning identities, pair-intersection spanning identities, and all
  conditional-rank inputs, derived from those literal subspaces.
- `R0.relation_certificate`: the actual side relation
  `x + w − (x+w) = 0` and the form values `(0,1,−1)`.
- `R0.relay`: literal relay feasibility and local generation.
- `map_D_side`, `map_D_signal`, `induced_eq_image_D`: exact identification of
  each relay-restricted side/signal space, and of the entire induced task,
  with the embedded D configuration. This is not merely a matching profile.
- `R0.full_profile`, `D.profile`, `R0_same_chart_profile`: all six first
  entries are 1; all nine doubled second entries are 3; the full and induced
  R₀ profiles coincide entry by entry.
- `R0.relay_side_dimension`, `relay_signal_dimension`, `relay_pair_dimension`,
  `relay_pair_conditional_rank`, `relay_local_upload_dimension`: the actual
  relay side ranks are all 1, signal ranks all 2, pair ranks and pair
  conditional ranks all 1, and the sum of local upload dimensions is 3.
- `D.append_dimensions`, `append_conditional_ranks`, `append_profile`:
  appending one actual D block to any existing task adds `(3,1,2,1,0,1)` to
  `(d,a_i,u_i,p_ij,t,m_i)`, adds 1 to each pair conditional rank, leaves each
  triple conditional rank unchanged, and adds 1 to the six first profile
  entries and 3 to the nine doubled second entries. Iterating this verified
  one-copy operation is the source's `n−1`-copy append construction.

## Reproduction

From the repository directory:

```sh
source scripts/env.sh
lake build UploadBroadcast.LiteralThetaBlocks
lake env lean scripts/AuditLiteralThetaBlocks.lean
```

The audit examines every safe declaration originating in the module,
including proof-bearing definitions, verifies presence in the kernel-checked
environment, and restricts all reachable axioms to `propext`,
`Classical.choice`, and `Quot.sound`.

Optional symbolic companion (tested with SymPy 1.14.0):

```sh
python3 scripts/check_literal_theta_blocks.py
```

Lean build and axiom checking do not require SymPy. The Python companion is
an exact symbolic check over `Q(θ)`, including the
fifteen actual profile expressions and relay feasibility/local generation.
It checks the source hash before proceeding. It is diagnostic evidence only;
all-characteristic validity comes from Lean, not from sampling or symbolic
rational-function rank calculations. No `native_decide` is used.

## Boundaries

These results verify the two literal constructions and the one-copy append
operation. They do not assert that a displayed task is indecomposable, or use
the independent classified same-chart theorem to transfer anything to these
literal generators. The current module deliberately does not edit root
imports, the main endpoint, or the repository's source-coverage accounting.
