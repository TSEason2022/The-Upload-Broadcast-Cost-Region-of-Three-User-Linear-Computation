# three-user-codes 1.5.0

Three-user upload/broadcast coding over finite fields, with exact code-certificate checks.
The compiler produces executable local upload encoders, one relay encoder and
three decoders, together with all-source matrix certificates.

**Original-field blocklength:** the default is **L=1 when both exact optimal
rates are integers, and L=2 otherwise**, including GF(2). A budget stop never
silently increases L. Generic fallback search is complete without resource
limits and can take exponential time.

## Start here

Requires Python 3.10 or newer. The runtime has no third-party dependencies.
From the repository root, enter this source package and use a local environment:

```bash
cd algorithm
python3.12 -m venv .venv
source .venv/bin/activate
python -m pip install .
python -m three_user_codes demo --q 2 --n 1 --output code.json
python -m three_user_codes verify code.json
python -m three_user_codes simulate code.json
python examples/quickstart.py
```

The binary demo uses 8 upload and 3 broadcast symbols across L=2 instances,
attaining U*=4 and D*=3/2. For an integral-rate example:

```bash
python -m three_user_codes inspect examples/integer_cycle_mix.json
python -m three_user_codes compile examples/integer_cycle_mix.json --output code.json
```

This repository contains source, tests, fixtures and documentation. To generate
a standalone zipapp locally, run `python build_release.py --output ../build/algorithm`.
Generated archives and PDFs are not checked into this repository.

## Handover documents

- [Algorithm and engineering manual](docs/ALGORITHM_MANUAL.md): notation,
  formulas, construction/search, certificate checks, operational examples and
  Mermaid flowcharts. Editable vector artwork is in `docs/diagrams/`.
- [Public API](docs/API.md): exact interfaces, data conventions and exceptions.
- [Original validation evidence](validation/RELEASE_VALIDATION.md): retained
  evidence from the supplied 1.5.0 handover; its environment and timings belong
  to that original run. See [the current recheck](validation/CURRENT_RECHECK.md) for the reproduced checks.
- [Security and resource boundaries](SECURITY.md).

## Refine the manual

Edit `tools/build_manual.py`, the authoritative manual authoring source, then:

```bash
python -m pip install ".[docs]"
python tools/build_manual.py
```

The script regenerates the PDF, Markdown and SVG diagrams together. Direct
edits to generated exports are overwritten. It uses DejaVu fonts when present,
or ReportLab's bundled Vera fonts; `--bundled-fonts` forces the portable option.
The PDF is an optional generated manual, not a manuscript; keep generated
outputs out of version control.

## Python entry point

```python
from three_user_codes import Field, compile_task, resonant_task

task = resonant_task(Field(2), 1)
result = compile_task(task, max_states=100_000, max_seconds=60)
result.verify(task)
code = result.operating_code(task)
# observations contains exactly three matrices of local measurements.
# execution = code.execute(observations)
```

Use `Task.from_rows(field, side, demand, n=...)` for custom tasks. Rows are linear
functions; source samples are columns. L-instance blocks use instance-major
order. Original redundant measurement rows and requested output order survive
execution. See the manual for a complete simulation.

## Engineering contract

- Every returned code is checked using exact finite-field identities and the
  target upload/broadcast counts and ranks.
- Automatic structural routes accelerate supported families; unsuccessful
  recognition continues to exact primal/dual search at the same L.
- `SearchBudgetExceeded` means resource exhaustion, not infeasibility.
  `max_seconds` is cooperative; use a supervising process for hard deadlines.
- An integer standalone binary LCBC profile is not by itself a scalar-code
  guarantee. Actual realization is checked before acceptance.
- The mathematical optimality interpretation follows the supplied manuscript;
  this package is not a formal proof assistant.

Run the regression suite with `python -m unittest discover -s tests -v`.
`build_release.py` creates a clean source delivery. The retained original
validation reports are historical evidence; the current reproduction is recorded
separately in [CURRENT_RECHECK.md](validation/CURRENT_RECHECK.md). Ownership and
license information is recorded in [LICENSING.md](LICENSING.md).
