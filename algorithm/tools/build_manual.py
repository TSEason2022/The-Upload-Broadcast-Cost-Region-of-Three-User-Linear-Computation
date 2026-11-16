"""Authoritative manual source; rebuild with: python tools/build_manual.py.

Install dependencies with: python -m pip install ".[docs]".
This rebuilds docs/ALGORITHM_MANUAL.pdf, docs/ALGORITHM_MANUAL.md and SVG figures.
No workspace-specific path or external status file is used.
"""
from pathlib import Path
import html, re
from reportlab.pdfgen import canvas
from reportlab.lib import colors
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.styles import ParagraphStyle
from reportlab.platypus import Paragraph, Table, TableStyle, Preformatted
from reportlab.lib.enums import TA_LEFT

ROOT=Path(__file__).resolve().parents[1]
DOC=ROOT/'docs'; DOC.mkdir(exist_ok=True)
import argparse
import reportlab
parser = argparse.ArgumentParser(description='Regenerate the algorithm manual PDF, Markdown and SVG assets.')
parser.add_argument('--bundled-fonts', action='store_true', help='Use ReportLab bundled Vera fonts for a portable rendering.')
args = parser.parse_args()
font_roots = [Path('/usr/share/fonts/truetype/dejavu'), Path('/usr/local/share/fonts/dejavu'),
              Path.home() / 'Library/Fonts', Path('C:/Windows/Fonts')]
font_root = next((p for p in font_roots if all((p / f).is_file() for f in
    ('DejaVuSans.ttf', 'DejaVuSans-Bold.ttf', 'DejaVuSansMono.ttf'))), None)
if font_root is not None and not args.bundled_fonts:
    font_files = [('Body', 'DejaVuSans.ttf'), ('BodyBold', 'DejaVuSans-Bold.ttf'), ('Mono', 'DejaVuSansMono.ttf')]
else:
    font_root = Path(reportlab.__file__).resolve().parent / 'fonts'
    font_files = [('Body', 'Vera.ttf'), ('BodyBold', 'VeraBd.ttf'), ('Mono', None)]
for name, filename in font_files:
    if filename is None:
        pdfmetrics.registerFont(pdfmetrics.Font(name, 'Courier', 'WinAnsiEncoding'))
        continue
    font_path = font_root / filename
    if not font_path.is_file():
        raise SystemExit(f'Missing bundled font: {font_path}. Reinstall the reportlab docs dependency.')
    pdfmetrics.registerFont(TTFont(name, str(font_path)))
GLYPH_FALLBACK = {'∩': ' intersection ', '−': '-', '…': '...', '≤': '<=', '≥': '>=',
                  '–': '-', '—': '-', '×': 'x', '→': '->', '’': "'", '“': '\"', '”': '\"'}
def safe_glyphs(text, font='Body'):
    supported = getattr(pdfmetrics.getFont(font).face, 'charToGlyph', {i: i for i in range(32, 127)})
    result = []
    for ch in text:
        if ch in '\n\t' or ord(ch) in supported:
            result.append(ch)
        elif ch in GLYPH_FALLBACK:
            result.append(GLYPH_FALLBACK[ch])
        else:
            raise ValueError(f'Font {font} lacks U+{ord(ch):04X}; add an explicit glyph-safe fallback.')
    return ''.join(result)
BLUE=colors.HexColor('#123455'); CYAN=colors.HexColor('#087f8c'); LIGHT=colors.HexColor('#edf5f8'); GREY=colors.HexColor('#546373'); INK=colors.HexColor('#172839'); AMBER=colors.HexColor('#9a6000')
W,H=595.28,841.89; M=44; CW=W-2*M
body=ParagraphStyle('body',fontName='Body',fontSize=9.1,leading=13.4,textColor=INK,spaceAfter=7)
small=ParagraphStyle('small',parent=body,fontSize=8.1,leading=11.5)
heading=ParagraphStyle('heading',fontName='BodyBold',fontSize=11.4,leading=15,textColor=BLUE,spaceBefore=12,spaceAfter=7)
cell=ParagraphStyle('cell',parent=small,fontSize=8,leading=11)
code_style=ParagraphStyle('code',fontName='Mono',fontSize=7.9,leading=11.4,textColor=INK)
PAGES=[]
def page(title,subtitle,*blocks): PAGES.append((title,subtitle,list(blocks)))
def p(t): return ('p',t)
def h(t): return ('h',t)
def code(t): return ('code',t.strip())
def table(headers,rows,widths=None): return ('table',headers,rows,widths)
def note(t): return ('note',t)
def diagram(name): return ('diagram',name)

page('Engineering handover', 'three-user-codes 1.5.0 | Algorithm and integration manual',
p('This package compiles a three-user finite-field observation/demand task into local upload encoders, a relay broadcast encoder, and three zero-error decoders. Every returned code is verified by exact matrix identities for all possible source values.'),
note('Core contract: use the original input field. Select L = 1 when both exact optimal rates are integers; otherwise select L = 2. A resource stop never silently changes that blocklength.'),
h('Read the package in this order'),
table(['Reader / task','Start here'],[
['Recipient running a first task','Pages 2, 9 and 10; README.md'],
['Algorithm reviewer','Pages 3–8; editable ALGORITHM_MANUAL.md'],
['Service / application integrator','Pages 10–12; docs/API.md; SECURITY.md'],
['Researcher refining the implementation','Pages 6–8 and 12–14; tests/; validation/']],[170,CW-170]),
h('Delivery contents'),
p('The source project contains the runtime package, current regression tests, minimal examples, the API reference, this manual, and current validation evidence. Historical releases and old benchmark reports are intentionally excluded. The PDF is intended for review and onboarding. tools/build_manual.py is the editable authoring source; it regenerates the Markdown export and vector artwork together.'),
h('What is and is not certified'),
p('Feasibility is checked by exact local-generation and decoding identities. Equality to the target costs is checked against separately recomputed rank formulas. The global optimality and minimum-blocklength interpretation depend on the supplied manuscript theorem, rather than a formal proof assistant.'),
h('Document map'),
table(['Pages','Subject'],[['2–3','Model, notation, exact rates and blocklength'],['4–6','Compiler flow and structural construction'],['7–8','Exact search, broadcast realization and certificates'],['9–11','CLI, Python execution and integration contracts'],['12–14','Engineering design, validation and refinement']],[70,CW-70]),
p('All matrices, code examples and public interfaces use a row-function convention: source samples are columns. Do not transpose an input merely because another coding library uses a column-generator convention.'))

page('Model and finite-field representation','Inputs, coordinate order and symbols',
p('Let x be an n-dimensional column over F_q. User i observes A_i x and requests W_i x. Define the augmented space V_i = row(A_i) + row(W_i). In this manual V_i denotes the augmented space to avoid confusing it with the scalar upload rate U*. The source is arbitrary; the guarantee is zero-error linear recovery.'),
table(['Symbol','Meaning'],[['q','Prime-power field order; q = p^m'],['A_i, W_i','Observation and requested-function matrices, for i = 1,2,3'],['V_i','Augmented rowspace A_i + W_i'],['L','Number of source instances in one coding block'],['E_i = T_i A_i','Upload matrix and local observation encoder'],['E; P','Stacked uploads; their rowspace'],['B','Relay encoder acting on stacked uploads'],['C_i, H_i','Broadcast and side-information decoder matrices'],['U*, D*','Optimal symbols per original source instance']],[100,CW-100]),
h('Original rows are an operational contract'),
p('Task canonicalizes rowspaces for algebra but retains original_side and original_demand. Redundant observation rows and their order survive execution. The runtime adapter maps the certificate back to the exact input measurement and output convention. All six input matrices must share the field and source width. A demand outside the joint observation span is rejected.'),
h('Extension fields are polynomial fields'),
p('Field(q, modulus=None) requires a prime power q < 2**64. Elements are Python integers in [0,q), excluding bool. For q = p^m an integer encodes base-p polynomial coefficients; multiplication is reduced by an irreducible modulus. GF(4) is not arithmetic modulo 4. A supplied modulus must be monic and irreducible. Preserve the serialized field representation across services.'),
h('Block and sample layout'),
p('For L instances, source coordinates are instance-major: x^(0), x^(1), …, x^(L-1). Observation and demand rows follow the same instance order. A runtime Matrix column represents one complete L-instance block. Multiple columns are independent blocks processed in a single call. Empty matrices require an explicit ncols to retain their width.'),
note('Use exact integers and the Field API. Floating-point rank tolerances, ordinary modular arithmetic for extension fields, and unchecked fixed-width integer accumulation do not preserve these semantics.'))

page('Exact costs and blocklength','The mathematical target precedes construction',
h('Broadcast profile'),
p('For spaces X and A define r(X | A) = dim(X + A) − dim(A). Put m_i = dim(V_i) − dim(A_i), M = m_1 + m_2 + m_3, V_ij = V_i ∩ V_j, and V_123 = V_1 ∩ V_2 ∩ V_3. Let t_i = r(V_i ∩ (V_j + V_k) | A_i), where {i,j,k} = {1,2,3}.'),
code('F_ijk = M - r(V_ij | A_j) - t_k\nQ_i,l = [2M - r(V_123 | A_l)\n         - r(V_ij + V_ik | A_i) - t_j - t_k] / 2\nD* = max(all six F_ijk, all nine Q_i,l)'),
p('The six F branches follow permutations 123, 132, 213, 231, 312, 321. The nine Q branches follow (i,l) in row-major order. broadcast_profile returns the exact Fraction cost and all fifteen branches. Branches add under direct sums; their maximum generally does not.'),
h('Upload formula'),
code('omega = max(c + tau_1, c + tau_2, c + tau_3,\n            (3c + tau_1 + tau_2 + tau_3) / 2)\nU* = rho + r0 + b + omega'),
p('upload_parameters computes these integers from a simultaneous three-side-space normal form: rho measures required private projections; c is the common pure-tripod demand dimension; r0 is the remaining pure-tripod demand dimension; b is the graph-relation rank modulo pure-tripod demands; tau_i measures demand in the other two users’ common observation space modulo the common three-user space. upload_bound.py is the executable definition, including graph-lift conventions.'),
h('Minimum original-field blocklength'),
code('L_min = 1  if U* and D* are both integers\n        2  otherwise\nupload_count = L * U*; broadcast_count = L * D*'),
p('This contract follows the supplied manuscript, Theorem 1, equation (18), including the binary field. The default and fast_paths=False both use L_min. Explicit force_blocklength=2 returns exactly two original-field instances. Forcing 1 when a rate is half-integral raises BlocklengthError.'),
note('A theorem bounding L does not bound search time. Integral rates remove fractional symbol counts; they do not guarantee that the current structural recognizer finds a scalar code cheaply.'))

page('Compiler control flow','A verified result or an explicit operational stop',
diagram('pipeline'),
p('Candidates require local generation, the target profile and actual broadcast realization. Dispatch uses direct constructors, targeted structural recognition and lazy scalar candidates, with a bounded 32-state scalar probe and active reduction before full search. Recognition failure continues at the same L. Binary realization can require the joint exact pass.'),
p('All routes share the compile budget and cancellation token. Time checks are cooperative, including algebra checkpoints. No-success after a complete unbudgeted search at the theorem-guaranteed length is ConstructionError: an implementation/theorem consistency issue, not a nonexistence certificate.'),
note('Strategy labels and counters are diagnostic. Integrations should branch on result success or exception type, not on an exact private route name.'))

page('Active reduction and joint construction','Remove irrelevant work while retaining exact embeddings',
diagram('active'),
p('The side normal form separates common, pairwise, private and tripod coordinates. Active reduction extracts an omniscience component, an active residual and passive directions, with exact coefficient embeddings back to the source task.'),
code('component_row_in_source = component_row @ embedding\nembedding.shape = (component_dimension, source_dimension)'),
p('active_reduce(task).verify(task) checks the side/augmented reconstruction and component roles. This is a decomposition check, not yet a final operating-code certificate. Omniscience uploads can be fixed while residual relays are searched.'),
h('Why broadcast construction remains joint'),
p('Optimizing each component’s maximum broadcast branch separately can overpay. The compiler evaluates the sum of all fifteen branch profiles and realizes one broadcast for the combined relay. At L=2, small scalar menus are a warm start; the complete lifted search retains arbitrary cross-instance mixing.'),
note('Direct-sum decomposition is an optimization opportunity, not a license to add separately minimized broadcast costs. Keep the branch vectors and source embeddings until joint acceptance.'))

page('Structured multi-component construction','Supported composition and its exact acceptance boundary',
h('Goal of the structural route'),
p('A collection of recognizable resonant R_n components and private-demand edges should be handled through verified source-space embeddings, local relay menus, and a joint broadcast. Dense source-basis changes must not alter the algebraic acceptance criteria.'),
h('Implementation status'),
p('STRUCTURAL_RELEASE_TEXT'),
h('Capacity reasoning used during candidate selection'),
p('A resonant component can offer several relay choices. Their effects must be combined at the level of the full fifteen-entry profile. The six F branches carry orientation-sensitive capacity; the nine Q branches remain constraints that must be checked, even where a family theorem says they are invariant. A private-demand cycle may require a mixed upload across a component boundary.'),
p('A candidate that passes a profile test is still subject to actual finite-field broadcast construction. Over GF(2), equal branch vectors do not generally imply equal scalar realizability. A deduplication or pruning rule therefore requires its own proof and field-specific preconditions.'),
h('Refinement rules'),
table(['Change','Required evidence'],[['New component recognizer','Exact embeddings; reconstruction of all six flags; dense-basis tests'],['New relay menu','Local generation, upload count/rank and complete branch profile'],['Cycle assignment','Exact repaired upload rows and an actual joint broadcast'],['Multiplicity shortcut','Equivalence to explicit small compositions over several fields'],['Binary special case','Actual scalar realization and the required separation conditions']],[135,CW-135]),
p('The final certificate is the common acceptance gate. An unsupported or unsuccessful structural path falls through to exact search at the selected blocklength. The package does not claim a complete polynomial-time quiver decomposition algorithm.'))

page('Exact primal and dual fallback','Complete search with sound finite-field pruning',
h('Primal: allocate local upload dimensions'),
p('The primal engine allocates upload counts to users and enumerates local quotient extensions in canonical reduced-row-echelon form. It rejects a partial relay when the remaining users cannot satisfy necessary demand or rank cuts. Canonical relay rowspaces support compile-local memoization; cache limits affect reuse, not mathematical coverage.'),
h('All-subset capacity checks'),
code('For every nonempty subset S of remaining users:\ndim(P + sum(C_i for i in S)) - dim(P)\n    >= sum(remaining_quota_i for i in S)'),
p('There are at most seven subsets. A failed condition prunes the branch. Tight demand cuts restrict allowed local spaces. When a multi-user capacity group is tight, the implementation constructs a quota-respecting independent basis with Hall lookahead and collapses the forced combined span. This preserves every final relay rowspace while avoiding internal enumeration.'),
h('Dual: enumerate a relay annihilator'),
p('The dual engine represents a relay by the kernel of a normal matrix and visits canonical prefixes. A prefix must preserve the equality of images of A_i and V_i, a necessary condition for demand recovery modulo the relay.'),
code('K_i = A_i intersect ker(N_prefix)\nJ_i = V_i intersect ker(N_prefix)\nFor a new normal column v, require for every i:\n    K_i v is nonzero  OR  J_i v is zero'),
p('The incremental implementation updates these residual kernel spaces by one-pivot elimination instead of rebuilding every prefix nullspace. The completed relay still passes local-generation, profile and broadcast checks. The dispatcher estimates primal and dual enumeration sizes; this is a search-order heuristic, not a complexity guarantee.'),
h('Completeness and binary fallback'),
p('A sufficient binary LCBC construction can fail for a particular relay even when another broadcast works. When needed, the joint exact pass enumerates target-dimensional broadcast spaces as well as relay choices. Only exhaustive failures may be used as exhaustive rejection evidence; a failed fast constructor alone is insufficient.'),
note('Worst-case enumeration remains exponential. max_states counts visited search work, including prefixes; it is not a version-independent performance unit. SearchBudgetExceeded is a resource result, never infeasibility.'))

page('Broadcast construction and certificate','Recover the requested functions for every source',
h('Induced broadcast problem'),
p('For a candidate relay P, choose a canonical relay basis E. Restrict each observation and augmented space to P, then express these intersections in relay coordinates. The broadcast problem operates on this induced task. The resulting broadcast is mapped back to the actual order of local upload rows.'),
p('The constructive LCBC route allocates common, pairwise, aligned and private broadcast groups. Decoder coordination works in the smaller quotient V_i/A_i. Its quotient map is constructed directly from side-space pivots, avoiding a full ambient annihilator. Empty demand quotients skip factorization.'),
h('The binary distinction'),
p('For q >= 3 the manuscript provides a general three-user scalar LCBC construction at the integer ceiling. For GF(2), the separated-side spanning construction has additional hypotheses. build_lcbc(..., round_up=True) can realize a ceiling cost for the standalone problem; compile_task never rounds its final optimal upload/broadcast targets.'),
h('All-source verification identities'),
code('E_i = T_i A_i                          (local uploads)\nW_i = C_i B E + H_i A_i               (zero-error decode)\nsum rows(E_i) = rank(E) = L * U*\nrows(B) = rank(B E) = L * D*'),
p('Here A_i and W_i refer to the lifted, canonical task used by the certificate. The operating adapter restores original row order and redundant rows. Since each equality is an exact matrix identity, it holds for every source column, not just the samples used in simulation.'),
h('Result binding'),
p('CompileResult stores exact Fraction optima, the certificate, a task representation fingerprint, and diagnostic statistics. result.verify(task) checks the binding, recomputes the costs and verifies the identities. Loading a saved code repeats verification rather than trusting a stored “verified” label.'),
note('A feasibility certificate and an optimality theorem have different roles. The certificate proves the supplied encoder/decoder equations. The implemented formulas and the mathematical theorem justify the target optimum.'))

page('Installation and command-line workflow','Run from the directory containing pyproject.toml',
h('Quick start'),
code('python -m pip install .\npython -m three_user_codes --version\npython -m three_user_codes demo --q 2 --n 1 \\\n  --output code.json --task-output task.json\npython -m three_user_codes verify code.json\npython -m three_user_codes simulate code.json'),
p('Requires Python 3.10 or newer. The runtime uses only the standard library. In demo, --n is the resonant chain length; the source dimension is 3n + 2. The binary n=1 task has U*=4, D*=3/2 and therefore L=2, with 8 upload and 3 broadcast symbols.'),
h('Inspect and compile your task'),
code('python -m three_user_codes inspect task.json\npython -m three_user_codes compile task.json \\\n  --max-states 100000 --max-seconds 60 \\\n  --progress --output code.json'),
p('inspect computes rates and minimum blocklength without synthesis. --blocklength 1 or 2 requests a specific original-field length; omit it for the minimum. --no-fast-paths selects the complete search route. --unlimited removes search limits and can lead to very long runtimes.'),
h('Minimal task JSON'),
code('{"schema":"three-user-task-v1", "q":2, "n":3,\n "side":[[[1,0,0]], [[0,1,0]], [[0,0,1]]],\n "demand":[[[0,1,0]], [[0,0,1]], [[1,0,0]]]}'),
p('For custom extension-field representation use save_task to emit the full field object; do not provide both q and field. Exactly three side and three demand arrays are required. Empty row arrays are valid when n is explicit.'),
h('Process status'),
table(['Exit','Meaning'],[['0','Verified result / successful requested operation'],['1','Construction or internal algebra consistency error'],['2','Invalid input, invalid length or failed verification'],['3','Search budget exhausted; no infeasibility conclusion'],['130','Cancellation or keyboard interruption']],[55,CW-55]),
p('Successful machine-readable output is JSON on stdout. --progress emits JSON lines on stderr. --debug before the subcommand preserves internal consistency tracebacks.'))

page('Python integration and execution','Compile once; execute many source blocks',
code('from three_user_codes import (\n    Field, Matrix, compile_task, resonant_task, save_code,\n    load_code, SearchBudgetExceeded,\n)\n\ntask = resonant_task(Field(2), 1)\ntry:\n    result = compile_task(task, max_states=100_000,\n                          max_seconds=60.0)\nexcept SearchBudgetExceeded as exc:\n    print(exc.stats)\n    raise\n\nresult.verify(task)\nsave_code(result, task, "code.json")\nresult, task = load_code("code.json", allow_legacy=False)\ncode = result.operating_code(task)\n\n# Only this simulation has full source access.\nx = Matrix(task.field, [[i % 2]\n           for i in range(result.certificate.task.n)])\nobservations = tuple(A @ x for A in code.original_side)\nexecution = code.execute(observations)\nassert execution.decoded == tuple(\n    W @ x for W in code.original_demand\n)'),
diagram('execution'),
p('In deployment, each user supplies only its own observation matrix. Use encode_uploads(observations), broadcast(uploads), and decode_all(observations, signal) to separate the protocol stages. code.execute performs the same sequence conveniently. iter_execute consumes observation batches lazily; the caller chooses batch size.'),
note('Do not send full source x to encoders in a production protocol. It appears above only to generate observations and check a reproducible simulation.'))

page('Integration contracts and resources','Stable interfaces and explicit trust boundaries',
h('Compile API'),
code('compile_task(task, *, max_states=100_000,\n    max_seconds=60.0, fast_paths=True,\n    force_blocklength=None, max_cache_entries=2048,\n    cancel_event=None, progress=None,\n    progress_interval=0.25)'),
p('cancel_event must provide is_set(), as threading.Event does. progress receives immutable ProgressEvent(stage, search_states, elapsed_seconds). Callbacks are synchronous, contribute to elapsed time and may propagate exceptions. Nested compile calls restore the surrounding context.'),
h('Strict JSON and fingerprints'),
p('The loader rejects duplicate keys, explicit nonfinite values and invalid field/shape data. Default ReadLimits are 32 MiB input, four million coefficient cells, 100,000 rows, 100,000 columns and a maximum imported blocklength of 4,096. The input task and certificate share the matrix allocation budget. These controls are not CPU or resident-memory limits.'),
p('New writers produce three-user-compiled-code-v2. Its SHA-256 fingerprint binds the field representation, source width and original side/demand rows in order. JSON formatting is irrelevant. A hash stored beside data is not authentication: pin a separately trusted expected_fingerprint when provenance requires it. Saves use atomic replacement.'),
h('Task versus certificate compatibility'),
p('load_code(path, allow_legacy=False) enforces the current result wrapper. The default loader also supports older verified certificates for import compatibility; no old release is included in this delivery. Imported blocklength allowance does not change the L<=2 contract for new compilation.'),
h('Service deployment'),
p('Keep state/time limits for unfamiliar tasks. max_seconds is cooperative and cannot interrupt a blocked callback or preempt every arithmetic operation. Put compilation in a supervised process when a hard deadline or memory limit is required. Cache entry and coefficient-cell limits bound cache growth, not total process RSS.'),
p('Arithmetic, pivoting and search are data dependent. This is exact coding software, not a constant-time cryptographic primitive. The runtime needs no network, shell execution, eval or pickle. Public constructors remain the input-validation boundary; private trusted matrix constructors are not public API.'),
note('Use exception classes and verification results as your integration contract. Statistics, internal module names and route labels are diagnostic and may evolve.'))

page('Engineering architecture','Where the optimization lives and where to extend it',
table(['Layer / module','Responsibility and invariant'],[['field.py; linalg.py','Exact field arithmetic, immutable matrices, canonical rowspaces'],['task.py; upload_bound.py; profile.py','Input semantics and exact upload/broadcast formulas'],['structure.py; mixing.py; structural_compiler.py; active_reduction.py','Verified structural candidates and source embeddings'],['compiler.py; active_relay.py','Route dispatch, exact primal/dual search and joint acceptance'],['lcbc.py; coordination.py','Original-field broadcast construction in demand quotients'],['certificate.py; provenance.py','All-source identities, counts/ranks and task binding'],['io.py; runtime.py; cli.py','Strict interchange, executable protocol and public tooling']],[190,CW-190]),
h('Implemented efficiency principles'),
p('RUNTIME_RELEASE_TEXT'),
h('Safe extension procedure'),
p('Add a constructor that returns an actual relay or local uploads in a documented coordinate system. Verify local generation and target count before invoking joint broadcast acceptance. Retain the complete fallback. Keep budget checks inside expensive loops and let cancellation propagate. Preserve the original-field blocklength and task fingerprint contracts.'),
h('Changes that need a separate project'),
p('A native finite-field backend, persistent packed-matrix storage, resumable search checkpoints and a universal indecomposable decomposition engine are not implied by the present package. Each needs an explicit compatibility contract and measurements. GF(2) already uses bitwise integer elimination; describing this as a new backend would be inaccurate.'),
p('When adding a backend, match extension-field basis and modulus exactly. Differentially compare ranks, solves, kernels and emitted certificates against the reference arithmetic. Fixed-width multiply-accumulate overflow must be prevented before modular reduction.'),
note('Optimize time to a verified code, peak memory and budget completion coverage. Reducing an internal call count alone is not an end-to-end performance claim.'))

page('Validation and repeatable refinement','Evidence belongs to the delivered source revision',
h('Release validation'),
p('VALIDATION_RELEASE_TEXT'),
code('python -m unittest discover -s tests -v\npython -m compileall -q three_user_codes\npython -m three_user_codes demo --q 2 --n 1 \\\n  --output /tmp/three_user_code.json\npython -m three_user_codes verify /tmp/three_user_code.json'),
h('What each test layer establishes'),
table(['Layer','Purpose'],[['Exact algebra','Field laws, shape/empty cases, rowspaces, kernels and solves'],['Small independent oracles','Compare selected rates and search results with separate small enumerations'],['Structural families','Recognized components, demand-cycle repair and dense basis changes'],['Compiler contracts','Minimum L, forced L, budgets, cancellation and fallback'],['Certificates / I/O','Tamper rejection, original-row binding, strict JSON and atomic save'],['Runtime execution','Local-only encoders, sample columns, redundant rows and output order']],[145,CW-145]),
h('Adding a reproducible regression'),
p('Save the smallest task JSON that reproduces the problem, including field modulus. Record source version, Python version, budget, fast-path setting, returned strategy, rates, L, verification result and elapsed time. Reduce dimensions only while preserving the failure. For basis invariance, apply an invertible source transform and verify the transformed result independently.'),
h('Performance comparison rules'),
p('Use the same tasks, seeds, budgets and machine. Report successes, budget stops and errors separately. Repeat timings and report medians or quantiles; compare speed only on paired successful tasks. Include preprocessing, broadcast construction and verification. Record peak memory for large inputs. Synthetic family coverage does not estimate performance on all possible tasks.'),
note('Do not turn a budget stop into a negative mathematical example. Do not report known-decomposition timings as automatic-discovery performance. Keep feasibility checks and optimum checks visible in the evidence.'))

page('Handover limits and maintenance guide','A precise boundary makes the next iteration reviewable',
h('Known limits'),
p('Generic exact search remains exponential in the worst case. Structural routes cover specified families and may miss a useful decomposition or cycle assignment. The current package is not a proof of fixed-parameter tractability or a universal polynomial-time synthesizer. Large prime-power fields may require expensive field setup and arithmetic.'),
p('Binary scalar broadcast requires special care: an integral LCBC profile alone is not a general scalar realizability theorem for arbitrary standalone binary broadcast inputs. The end-to-end task compiler retains actual realization checks and complete fallback at the chosen length.'),
h('Troubleshooting'),
table(['Observation','Action'],[['Budget exhausted','Keep the task and stats; inspect rates; increase a justified budget or improve its structural route'],['Forced L=1 rejected','Inspect exact denominators; use default policy or request L=2'],['Certificate binding fails','Use the original task rows/order and field representation; investigate tampering'],['Extension-field mismatch','Compare modulus and polynomial-basis encoding, not just q'],['Unexpected source/observation shape','Use L*n source rows and instance-major observation order'],['ConstructionError','Preserve input and traceback; treat as a defect needing diagnosis']],[155,CW-155]),
h('Refinement priorities'),
p('First improve structural coverage on verified multi-component cases. Then measure candidate generation, coordinate factorization and broadcast work before changing linear-algebra storage or adding native dependencies. Preserve inexpensive complete-search exits for small tasks. Every new pruning rule needs a soundness argument and adversarial small-case comparison.'),
h('Theoretical correspondence'),
p('The theoretical reference is Shuo Tan and Syed A. Jafar, “The Upload–Broadcast Cost Region of Three-User Linear Computation”, supplied manuscript. Publication status and date are not asserted. The implementation uses Theorem 1, equation (18); the upload rank formula; fifteen broadcast branches; and Appendix D demand-cycle and broadcast constructions. The manuscript PDF is not duplicated.'),
h('Ownership and public distribution'),
p('The algorithm code and its accompanying software documentation are available under the MIT License, copyright (c) 2026 Shuo Tan. See LICENSE and LICENSING.md. This license does not apply to research papers, the sibling Lean formalization, or other repository materials; their existing rights and licenses are unchanged. Existing attribution is preserved. No third-party runtime dependency is introduced.'),
note('The manual authoring source, API reference, current tests and validation evidence form the maintenance handover. A new change is ready when its contract is stated, its acceptance invariant is checked and its evidence can be reproduced.'))

MERMAID={
'pipeline':'''flowchart TD\n  A["Validate task and field"] --> B["Compute exact U*, D*; fix L"]\n  B --> C["Reduce coordinates; direct and structural candidates"]\n  C --> D{"Verified candidate?"}\n  D -->|Yes| H["Embed, certify and return"]\n  D -->|No| E["Probe, structural and active routes"]\n  E --> F{"Verified candidate?"}\n  F -->|Yes| H\n  F -->|No| G["Exact primal or dual relay search"]\n  G --> I{"Broadcast realized?"}\n  I -->|Yes| H\n  I -->|No| J["Joint exact broadcast fallback when needed"]\n  J --> H\n  G -.-> K["Budget stop or cancellation"]\n  J -.-> K''',
'active':'''flowchart TD\n  A["Task in joint observation coordinates"] --> B["Certified active reduction"]\n  B --> C["Omniscience uploads"]\n  B --> D["Residual candidates / exact search"]\n  B --> E["Passive directions"]\n  C --> F["Combine relay and all fifteen branches"]\n  D --> F\n  E --> G["Retain source embedding only"]\n  F --> H{"Joint broadcast succeeds?"}\n  H -->|Yes| I["Embed and verify final code"]\n  H -->|No| D''',
'execution':'''flowchart LR\n  A["Local observations"] --> B["Local upload encoders"]\n  B --> C["Relay broadcast"]\n  C --> D["User decoders"]\n  A --> D\n  D --> E["Requested functions"]'''
}

def draw_box(c,x,y,w,h,text,fill=LIGHT,stroke=BLUE,decision=False):
    c.setFillColor(fill); c.setStrokeColor(stroke); c.setLineWidth(.85)
    if decision:
        path=c.beginPath(); path.moveTo(x+w/2,y+h);path.lineTo(x+w,y+h/2);path.lineTo(x+w/2,y);path.lineTo(x,y+h/2);path.close();c.drawPath(path,stroke=1,fill=1)
    else: c.roundRect(x,y,w,h,6,stroke=1,fill=1)
    lines=text.split('\n');c.setFont('BodyBold' if decision else 'Body',8.2);c.setFillColor(INK)
    for i,t in enumerate(lines): c.drawCentredString(x+w/2,y+h/2+(len(lines)-1)*5.4-i*10.8-3,t)

def arrow(c,points,label=None):
    c.setStrokeColor(GREY);c.setLineWidth(.9)
    path=c.beginPath();path.moveTo(*points[0])
    for xy in points[1:]:path.lineTo(*xy)
    c.drawPath(path)
    (x0,y0),(x1,y1)=points[-2:];import math
    a=math.atan2(y1-y0,x1-x0);c.setFillColor(GREY)
    p=c.beginPath();p.moveTo(x1,y1);p.lineTo(x1-5*math.cos(a-.45),y1-5*math.sin(a-.45));p.lineTo(x1-5*math.cos(a+.45),y1-5*math.sin(a+.45));p.close();c.drawPath(p,fill=1,stroke=0)
    if label:
        tx,ty,t=label;c.setFont('Body',7.2);c.setFillColor(GREY);c.drawString(tx,ty,t)

def draw_diagram(c,name,x,top):
    if name=='pipeline':
        hh=430; y=top-hh; cx=x+145; w=216
        boxes=[(cx,y+383,w,38,'Validate task and field'),(cx,y+326,w,38,'Compute exact U*, D*\nFix original-field L'),(cx,y+269,w,38,'Direct / structural candidates\nLazy dispatch'),(cx,y+201,w,49,'Candidate accepted?',True),(cx,y+139,w,42,'Probe, structural and\nactive construction'),(cx,y+79,w,42,'Exact primal or dual\nrelay search'),(cx,y+15,w,43,'Joint broadcast fallback\nwhen required')]
        for item in boxes:
            xx,yy,ww,hh2,txt,*d=item;draw_box(c,xx,yy,ww,hh2,txt,decision=bool(d))
        for a,b in [(383,364),(326,307),(269,250),(201,181),(139,121),(79,58)]:arrow(c,[(cx+w/2,y+a),(cx+w/2,y+b)])
        draw_box(c,x,y+168,108,63,'Embed in source\nVerify identities\nReturn code',fill=colors.HexColor('#e0f2ec'))
        arrow(c,[(cx,y+225.5),(x+120,y+225.5),(x+120,y+199.5),(x+108,y+199.5)],(x+112,y+236,'Yes'))
        arrow(c,[(cx,y+160),(x+54,y+160),(x+54,y+168)],(x+76,y+149,'On success'))
        arrow(c,[(cx,y+100),(x+35,y+100),(x+35,y+168)])
        arrow(c,[(cx,y+36),(x+16,y+36),(x+16,y+168)])
        c.setFont('Body',7.5);c.setFillColor(GREY);c.drawString(cx+w/2+9,y+191,'No')
        draw_box(c,x+390,y+67,114,78,'Budget stop /\ncancellation\nNo infeasibility\nclaim',fill=colors.HexColor('#fff5e2'),stroke=AMBER)
        arrow(c,[(cx+w,y+100),(x+390,y+100)])
        return 440
    if name=='active':
        hh=315;y=top-hh
        draw_box(c,x+130,y+268,245,40,'Task in joint observation coordinates')
        draw_box(c,x+130,y+204,245,42,'Certified active reduction')
        arrow(c,[(x+252,y+268),(x+252,y+246)])
        draw_box(c,x,y+126,148,49,'Omniscience\nFixed local uploads')
        draw_box(c,x+177,y+126,148,49,'Active residual\nCandidates / search')
        draw_box(c,x+354,y+126,148,49,'Passive directions\nRetain embedding')
        for xx in [74,251,428]:arrow(c,[(x+252,y+204),(x+252,y+190),(x+xx,y+190),(x+xx,y+175)])
        draw_box(c,x+54,y+57,287,44,'Combine relay profiles\nConstruct one joint broadcast')
        arrow(c,[(x+74,y+126),(x+74,y+101)])
        arrow(c,[(x+251,y+126),(x+251,y+101)])
        draw_box(c,x+54,y,287,37,'Embed and verify final code',fill=colors.HexColor('#e0f2ec'))
        arrow(c,[(x+197,y+57),(x+197,y+37)])
        arrow(c,[(x+428,y+126),(x+428,y+18),(x+341,y+18)])
        return 330
    if name=='execution':
        y=top-88
        for xx,txt in [(0,'Local\nobservations'),(131,'Local upload\nencoders'),(262,'Relay\nbroadcast'),(393,'User\ndecoders')]:draw_box(c,x+xx,y+28,112,44,txt)
        for xx in [112,243,374]:arrow(c,[(x+xx,y+50),(x+xx+19,y+50)])
        arrow(c,[(x+56,y+28),(x+56,y+7),(x+449,y+7),(x+449,y+28)],(x+194,y-6,'Local side information'))
        return 112

def markup(t):
    return html.escape(safe_glyphs(t)).replace('**','')

# Release text is embedded: no external status file or workspace is needed.
status = {'structural': 'The structural_compiler.py route automatically discovers repeated or mixed '
               'R_n summands, extracted private-demand edges/cycles and a zero-excess '
               'remainder after active reduction. No generator labels are supplied. It '
               'solves a restricted endomorphism system, probes fixed-seed operators, and '
               'certifies stable image/kernel splits with complementary idempotent '
               'projectors preserving all six flags. Recognized embeddings feed six-slack '
               'integer allocation and multiplicity-based cycle repair. For L=2 it '
               'decomposes once and duplicates component multiplicities, permitting '
               'cross-instance pairing. The resulting relay must pass the existing joint '
               'broadcast and certificate gates. Recognition is bounded: at most 512 local '
               'probes, source dimension 80 and 384 variables for endomorphism and '
               'reference-isomorphism systems; unsuccessful or unsupported tasks retain '
               'the complete fallback. This is not a full classification or all binary '
               'Table V constructions.',
 'runtime': 'Scalar candidates are generated lazily and tested immediately; L=2 streams '
            'combinations while retaining complete fallback. Coordinate solves reuse '
            'immutable-matrix pivot factorizations, and shared-basis right-hand sides are '
            'batched. Normal forms, upload parameters and verified active reductions reuse '
            'immutable Task-local results. Internal proven-valid slices avoid repeated '
            'element validation while public constructors remain strict. Tight '
            'Hall-capacity groups collapse to a quota-respecting basis; dual prefix '
            'kernels update by one-pivot elimination. Certificate construction performs '
            'one complete pre-return verification. These are implemented changes; release '
            'evidence, rather than call-count reductions alone, determines measured '
            'performance.',
 'validation': 'The delivered revision passed all 256 regression tests. A 57-scenario '
               'suite run three times completed 171/171 trials under 3-second and '
               '100,000-state per-compilation budgets, with native certificate checks and '
               'independent source-basis decoding checks. These results measure the '
               'supplied task families, not a universal runtime guarantee. See '
               'validation/RELEASE_VALIDATION.md and its machine-readable evidence for the '
               'source hash, environment, timings and exact cases. The commands below '
               'reproduce the core suite.'}
replacements = {
    'STRUCTURAL_RELEASE_TEXT': status['structural'],
    'RUNTIME_RELEASE_TEXT': status['runtime'],
    'VALIDATION_RELEASE_TEXT': status['validation'],
}
for _,_,blocks in PAGES:
    for j,b in enumerate(blocks):
        if b[0] in ('p','note') and b[1] in replacements:blocks[j]=(b[0],replacements[b[1]])

out=DOC/'ALGORITHM_MANUAL.pdf'; c=canvas.Canvas(str(out),pagesize=(W,H));c.setTitle('three-user-codes 1.5.0 — Algorithm and Engineering Manual');c.setAuthor('Project engineering handover')
bounds=[]
for idx,(title,subtitle,blocks) in enumerate(PAGES,1):
    c.setFillColor(BLUE);c.rect(0,H-22,W,22,fill=1,stroke=0)
    c.setFont('BodyBold',8);c.setFillColor(colors.white);c.drawString(M,H-15,'THREE-USER CODES  /  ENGINEERING MANUAL')
    c.setFillColor(CYAN);c.setFont('BodyBold',9);c.drawString(M,H-49,f'{idx:02d}  /  {len(PAGES):02d}')
    c.setFillColor(BLUE);c.setFont('BodyBold',20);c.drawString(M,H-79,title)
    c.setFillColor(GREY);c.setFont('Body',9.4);c.drawString(M,H-99,subtitle)
    c.bookmarkPage(f'page{idx}');c.addOutlineEntry(title,f'page{idx}',level=0,closed=False)
    y=H-120
    for b in blocks:
        kind=b[0]
        if kind in ('p','h','note'):
            style=heading if kind=='h' else body
            if kind=='h':y-=5
            para=Paragraph(markup(b[1]),style);ww,hh=para.wrap(CW-18 if kind=='note' else CW,700)
            if kind=='note':
                c.setFillColor(LIGHT);c.roundRect(M,y-hh-15,CW,hh+12,5,stroke=0,fill=1);para.drawOn(c,M+9,y-hh-8);y-=hh+23
            else:para.drawOn(c,M,y-hh);y-=hh+7
        elif kind=='code':
            pre=Preformatted(safe_glyphs(b[1], 'Mono'),code_style,maxLineLength=79);ww,hh=pre.wrap(CW-18,700)
            c.setFillColor(colors.HexColor('#f1f3f6'));c.roundRect(M,y-hh-12,CW,hh+13,4,fill=1,stroke=0);pre.drawOn(c,M+9,y-hh-5);y-=hh+24
        elif kind=='table':
            rows=[[Paragraph(markup(str(x)),cell) for x in b[1]]]+[[Paragraph(markup(str(x)),cell) for x in row] for row in b[2]]
            tt=Table(rows,colWidths=b[3] or [CW/len(b[1])]*len(b[1]),hAlign='LEFT');tt.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),LIGHT),('VALIGN',(0,0),(-1,-1),'TOP'),('LINEBELOW',(0,0),(-1,0),.7,CYAN),('LINEBELOW',(0,1),(-1,-1),.35,colors.HexColor('#d8e1e8')),('LEFTPADDING',(0,0),(-1,-1),7),('RIGHTPADDING',(0,0),(-1,-1),7),('TOPPADDING',(0,0),(-1,-1),6),('BOTTOMPADDING',(0,0),(-1,-1),6)]));ww,hh=tt.wrap(CW,700);tt.drawOn(c,M,y-hh);y-=hh+12
        elif kind=='diagram': y-=draw_diagram(c,b[1],M,y)
    bounds.append((idx,round(y,1)))
    c.setStrokeColor(colors.HexColor('#d4dfe7'));c.line(M,39,W-M,39);c.setFont('Body',7.4);c.setFillColor(GREY);c.drawString(M,26,'Version 1.5.0  •  Exact arithmetic  •  Original-field coding');c.drawRightString(W-M,26,str(idx));c.showPage()
c.save()
md=['# three-user-codes 1.5.0 — Algorithm and Engineering Manual','', 'This readable and editable Markdown export accompanies ALGORITHM_MANUAL.pdf. For synchronized regeneration, edit tools/build_manual.py (the authoritative authoring source), then run python tools/build_manual.py after installing the docs extra. Direct edits to this export are overwritten by regeneration. Editable vector artwork is in diagrams/pipeline.svg, diagrams/active.svg and diagrams/execution.svg; Mermaid sources appear below.','']
for idx,(title,subtitle,blocks) in enumerate(PAGES,1):
    md += [f'## {idx}. {title}','',subtitle,'']
    for b in blocks:
        if b[0]=='p':md +=[b[1],'']
        elif b[0]=='h':md +=['### '+b[1],'']
        elif b[0]=='note':md +=['> '+b[1],'']
        elif b[0]=='code':md +=['```text',b[1],'```','']
        elif b[0]=='table':
            md += ['| '+' | '.join(b[1])+' |','| '+' | '.join(['---']*len(b[1]))+' |']
            md += ['| '+' | '.join(row)+' |' for row in b[2]];md+=['']
        elif b[0]=='diagram':md +=['```mermaid',MERMAID[b[1]],'```','']
(DOC/'ALGORITHM_MANUAL.md').write_text('\n'.join(md))
print({'pdf':str(out),'pages':len(PAGES),'bottom_positions':bounds})
if any(y<51 for _,y in bounds):raise SystemExit('PAGE OVERFLOW: adjust content or styles')

# Editable vector companions, using precisely the PDF diagram geometry.
class SvgPath:
    def __init__(self): self.ops=[]
    def moveTo(self,x,y): self.ops.append(f'M {x:.3f} {y:.3f}')
    def lineTo(self,x,y): self.ops.append(f'L {x:.3f} {y:.3f}')
    def close(self): self.ops.append('Z')
class SvgCanvas:
    def __init__(self,w,h): self.w=w;self.h=h;self.parts=[];self.fill='#000000';self.stroke='#000000';self.linewidth=1;self.font='Body';self.fs=8
    def setFillColor(self,c): self.fill=c.hexval().replace('0x','#')
    def setStrokeColor(self,c): self.stroke=c.hexval().replace('0x','#')
    def setLineWidth(self,w): self.linewidth=w
    def roundRect(self,x,y,w,h,r,stroke=1,fill=1): self.parts.append(f'<rect x="{x:.3f}" y="{y:.3f}" width="{w:.3f}" height="{h:.3f}" rx="{r}" fill="{self.fill if fill else "none"}" stroke="{self.stroke if stroke else "none"}" stroke-width="{self.linewidth}"/>')
    def beginPath(self): return SvgPath()
    def drawPath(self,p,stroke=1,fill=0): self.parts.append(f'<path d="{" ".join(p.ops)}" fill="{self.fill if fill else "none"}" stroke="{self.stroke if stroke else "none"}" stroke-width="{self.linewidth}"/>')
    def setFont(self,f,s):self.font=f;self.fs=s
    def _text(self,x,y,t,anchor): self.parts.append(f'<text transform="translate({x:.3f},{y:.3f}) scale(1,-1)" text-anchor="{anchor}" font-family="DejaVu Sans, sans-serif" font-size="{self.fs}" font-weight="{"bold" if self.font=="BodyBold" else "normal"}" fill="{self.fill}">{html.escape(t)}</text>')
    def drawCentredString(self,x,y,t): self._text(x,y,t,'middle')
    def drawString(self,x,y,t): self._text(x,y,t,'start')
    def save(self,path): path.write_text(f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.w}" height="{self.h}" viewBox="0 0 {self.w} {self.h}"><rect width="100%" height="100%" fill="white"/><g transform="translate(0,{self.h}) scale(1,-1)">'+''.join(self.parts)+'</g></svg>')
svg_dir=DOC/'diagrams';svg_dir.mkdir(exist_ok=True)
for name,height in [('pipeline',440),('active',330),('execution',112)]:
    sc=SvgCanvas(519,height+10);draw_diagram(sc,name,7,height+3);sc.save(svg_dir/(name+'.svg'))
