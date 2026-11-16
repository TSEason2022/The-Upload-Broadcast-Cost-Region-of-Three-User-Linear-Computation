# The Upload–Broadcast Cost Region of Three-User Linear Computation

**Exact Finite-Field Algorithms and Lean Formalization**

This project accompanies the research by Shuo Tan and Syed A. Jafar on three users computing linear functions through an initially uninformed relay.

## Available now: verified algorithm implementation

The [algorithm source](algorithm/) includes finite-field task analysis, executable local upload encoders, a relay encoder, three decoders, exact code certificates, examples and tests.

The current recheck passed **256 regression tests**, **171 benchmark trials** (57 frozen tasks, three repetitions), eight CLI/API checks and an isolated installation check. See the [validation record](algorithm/validation/CURRENT_RECHECK.md) for commands, source digests, fields, dimensions, seeds and resource limits.

For every feasible task in the three-user model, the research establishes simultaneous minimum total upload and minimum fully informed broadcast. A linear code over the original field attains the corner with blocklength one when both optimal costs are integers, and two otherwise, including GF(2). Implementation tests check concrete constructions; they do not replace the mathematical proof.

## Lean verification in progress

The formalization has been aligned with the current supplied manuscript. A clean build of all **314 library modules**, followed by complete axiom and declaration audits, is running. The updated [Lean source](lean/) will be added after these checks pass. Historical proof reports will not be presented as current certification.

## Run the algorithm

```sh
git clone https://github.com/TSEason2022/The-Upload-Broadcast-Cost-Region-of-Three-User-Linear-Computation.git
cd The-Upload-Broadcast-Cost-Region-of-Three-User-Linear-Computation/algorithm
python3.12 -m venv .venv
. .venv/bin/activate
python -m pip install .
python -m three_user_codes demo --q 2 --n 1 --output code.json
python -m three_user_codes verify code.json
python -m three_user_codes simulate code.json
```

The manuscript is maintained separately. Existing [algorithm rights information](algorithm/LICENSING.md) is preserved; no new reuse license is granted.
