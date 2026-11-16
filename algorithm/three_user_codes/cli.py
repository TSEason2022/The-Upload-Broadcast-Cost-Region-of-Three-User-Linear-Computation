"""Command-line entry points. All code generation is deterministic."""
from __future__ import annotations

import argparse
import json
import sys

from ._version import __version__
from .errors import CompilationCancelled, ConstructionError
from .io import loads_json
from .field import Field
from .linalg import Matrix
from .compiler import compile_task, resonant_task, SearchBudgetExceeded
from .upload_bound import upload_cost
from .profile import broadcast_profile
from .io import (read_json, write_json, task_from_dict, task_to_dict,
                 result_to_dict, result_from_dict, verify_result, fraction_dict)


def _summary(result):
    c = result.certificate
    minimum = 1 if (result.upload_optimum.denominator == 1 and
                    result.broadcast_optimum.denominator == 1) else 2
    return {"status": "verified", "q": c.task.field.q, "blocklength": c.blocklength,
            "minimum_linear_blocklength": minimum,
            "blocklength_is_minimal": c.blocklength == minimum,
            "upload_optimum": str(result.upload_optimum),
            "broadcast_optimum": str(result.broadcast_optimum),
            "upload_symbols": c.stacked_upload.nrows, "broadcast_symbols": c.broadcast.nrows,
            "strategy": result.strategy, "stats": result.stats}


def _simulation(result, task, values=None):
    from .runtime import OperatingCode
    code = OperatingCode(result.certificate, task)
    field, n = task.field, result.certificate.task.n
    if values is None:
        # Three deterministic independent source vectors as sample columns.
        x = Matrix(field, [[(3*i+7*j+j*i+1) % field.q for j in range(3)] for i in range(n)], ncols=3)
    else:
        if not isinstance(values, list) or len(values) != n:
            raise ValueError(f"source must be a list of {n} field elements")
        x = Matrix(field, [[value] for value in values], ncols=1)
    side = tuple(A @ x for A in code.original_side)
    messages = code.encode_uploads(side)
    signal = code.broadcast(messages)
    decoded = tuple(code.decode(i, side[i], signal) for i in range(3))
    expected = tuple(W @ x for W in code.original_demand)
    if decoded != expected:
        raise RuntimeError("runtime decoding did not match direct demands")
    return {"source": x.to_list(), "uploads": [m.to_list() for m in messages],
            "broadcast": signal.to_list(), "decoded": [m.to_list() for m in decoded],
            "sample_columns": x.ncols, "decoded_exactly": True}


def main(argv=None):
    parser = argparse.ArgumentParser(prog="three-user-codes", description="Exact finite-field optimal three-user upload/broadcast coding")
    parser.add_argument("--debug", action="store_true", help="show traceback for construction consistency errors")
    parser.add_argument("--version", action="version", version=__version__)
    sub = parser.add_subparsers(dest="command", required=True)
    demo = sub.add_parser("demo", help="compile R_n, verify, and run actual encoders/decoders")
    demo.add_argument("--q", type=int, default=3)
    demo.add_argument("--n", type=int, default=1, help="resonant chain length; source dimension is 3n+2")
    demo.add_argument("--output", default="demo_code.json")
    demo.add_argument("--task-output", help="also write its reusable task input JSON")
    compile_parser = sub.add_parser("compile", help="compile a task JSON to a verified code JSON")
    compile_parser.add_argument("input")
    compile_parser.add_argument("--output", "-o", default="code.json")
    for command in (demo, compile_parser):
        command.add_argument("--max-states", type=int, default=100000)
        command.add_argument("--max-seconds", type=float, default=60.0)
        command.add_argument("--unlimited", action="store_true", help="remove search limits (may take exponential time)")
        command.add_argument("--no-fast-paths", action="store_true")
        command.add_argument("--max-cache-entries", type=int, default=2048)
        command.add_argument("--progress", action="store_true", help="emit progress JSON lines on stderr")
        command.add_argument("--blocklength", "--force-working-blocklength",
                             dest="blocklength", type=int, choices=(1, 2),
                             help="force 1 or 2 instances over the original input field (legacy flag is an alias)")
    inspect = sub.add_parser("inspect", help="calculate exact optimal costs without constructing a code")
    inspect.add_argument("input")
    verify = sub.add_parser("verify", help="recompute bounds and verify all code identities")
    verify.add_argument("input")
    simulate = sub.add_parser("simulate", help="execute local uploads, relay broadcast and decoding")
    simulate.add_argument("input")
    simulate.add_argument("--source", help="JSON list of L*n coefficients in instance-major order")
    args = parser.parse_args(argv)
    def emit_progress(event):
        print(json.dumps({"status": "progress", **event.to_dict()}), file=sys.stderr)
    try:
        if args.command in ("demo", "compile"):
            task = resonant_task(Field(args.q), args.n) if args.command == "demo" else task_from_dict(read_json(args.input))
            result = compile_task(task, max_states=None if args.unlimited else args.max_states,
                                  max_seconds=None if args.unlimited else args.max_seconds,
                                  fast_paths=not args.no_fast_paths,
                                  force_blocklength=args.blocklength,
                                  max_cache_entries=args.max_cache_entries,
                                  progress=emit_progress if args.progress else None)
            write_json(args.output, result_to_dict(result, task))
            output = _summary(result)
            output["output"] = args.output
            if args.command == "demo":
                output["execution"] = _simulation(result, task)
                if args.task_output:
                    write_json(args.task_output, task_to_dict(task))
        elif args.command == "inspect":
            task = task_from_dict(read_json(args.input))
            profile = broadcast_profile(task.side, task.augmented)
            upload = upload_cost(task)
            output = {"q": task.field.q, "source_dimension": task.n,
                      "upload_optimum": fraction_dict(upload),
                      "broadcast_optimum": fraction_dict(profile.cost),
                      "minimum_linear_blocklength": 1 if (
                          upload.denominator == 1 and profile.cost.denominator == 1) else 2,
                      "first_six_branches": [fraction_dict(v) for v in profile.first],
                      "last_nine_branches": [fraction_dict(v) for v in profile.second]}
        else:
            result, task = result_from_dict(read_json(args.input))
            output = _summary(result)
            output["verification"] = verify_result(result, task).to_dict()
            if args.command == "simulate":
                output["execution"] = _simulation(result, task, loads_json(args.source) if args.source else None)
        print(json.dumps(output, ensure_ascii=False, indent=2, allow_nan=False))
        return 0
    except (CompilationCancelled, KeyboardInterrupt) as exc:
        print(json.dumps({"status": "cancelled", "message": str(exc) or "Interrupted by user"}), file=sys.stderr)
        return 130
    except SearchBudgetExceeded as exc:
        print(json.dumps({"status": "budget_exhausted", "message": str(exc), "stats": exc.stats}), file=sys.stderr)
        return 3
    except (ConstructionError, RuntimeError, ArithmeticError) as exc:
        if args.debug:
            raise
        print(json.dumps({"status": "construction_error", "error_type": type(exc).__name__, "message": str(exc)}), file=sys.stderr)
        return 1
    except (ValueError, TypeError, KeyError, OSError) as exc:
        print(json.dumps({"status": "error", "message": str(exc)}, ensure_ascii=False), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
