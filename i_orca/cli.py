"""Command-line interface for i-orca.

Subcommands mirror the MCP tool surface (SPEC §7): the cheap loop
(``parse``/``verify``/``compile``/``metrics``) runs with zero Isabelle; the
expensive loop (``check``/``hammer``) binds to a warm Isabelle session and
degrades gracefully when none is present. ``prove`` drives the autonomous loop.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from i_orca import __version__
from i_orca.ast import Theorem
from i_orca.backend import IsabelleBackend
from i_orca.compiler import compile_isar, compile_lean4, compile_tex
from i_orca.compiler.isar import compile_isar_document
from i_orca.compiler.tex import compile_tex_document
from i_orca.metrics import compute_metrics
from i_orca.parser import ParseError, parse, parse_file
from i_orca.tools import tools_description
from i_orca.verifier import verify

_TARGET_EXT = {"isar": ".thy", "tex": ".tex", "lean4": ".lean"}


def _load(args) -> list[Theorem]:
    if getattr(args, "source", None):
        return parse(args.source).theorems
    return parse_file(args.file).theorems


def _emit(obj, as_json: bool) -> None:
    if as_json:
        print(json.dumps(obj, indent=2, ensure_ascii=False))


# --------------------------------------------------------------------------- #
#  Subcommands
# --------------------------------------------------------------------------- #


def cmd_parse(args) -> int:
    theorems = _load(args)
    out = {"theorems": [_theorem_ast(t) for t in theorems]}
    if args.json:
        _emit(out, True)
    else:
        for t in theorems:
            print(f"theorem {t.name}: {len(t.proof.steps())} steps, "
                  f"goal = {t.goal.statement if t.goal else '—'}")
    return 0


def cmd_verify(args) -> int:
    theorems = _load(args)
    reports = [verify(t, strict=args.strict) for t in theorems]
    if args.json:
        _emit({"reports": [r.to_dict() for r in reports]}, True)
    else:
        for r in reports:
            _print_report(r)
    return 0 if all(r.valid for r in reports) else 1


def cmd_compile(args) -> int:
    theorems = _load(args)
    target = args.target
    if args.document and target == "tex":
        text = compile_tex_document(theorems)
        _write_or_print(text, args.out, theorems[0].name, target)
        return 0
    if args.document and target == "isar":
        text = compile_isar_document(theorems, theory_name=args.theory or "Fieldrun")
        _write_or_print(text, args.out, args.theory or "Fieldrun", target)
        return 0
    compiler = {"isar": compile_isar, "tex": compile_tex, "lean4": compile_lean4}[target]
    for t in theorems:
        text = compiler(t)
        _write_or_print(text, args.out, t.name, target)
    return 0


def cmd_metrics(args) -> int:
    theorems = _load(args)
    out = {t.name: compute_metrics(t).to_dict() for t in theorems}
    if args.json:
        _emit(out, True)
    else:
        for name, m in out.items():
            print(f"{name}: formal_fraction_static={m['formal_fraction_static']} "
                  f"({m['n_method']}/{m['n_steps']} method, {m['n_frontier']} frontier)")
    return 0


def cmd_check(args) -> int:
    theorems = _load(args)
    backend = IsabelleBackend(
        extra_dirs=getattr(args, "dir", None),
        parent_session=getattr(args, "session", None),
    )
    results = [backend.check_proof(t, timeout_s=args.timeout) for t in theorems]
    if args.json:
        _emit({"results": [r.to_dict() for r in results]}, True)
    else:
        for r in results:
            tag = "available" if r.available else "UNAVAILABLE (static fallback)"
            print(f"{r.theorem}: Isabelle {tag}")
            if r.formal_fraction_real is not None:
                print(f"  formal_fraction_real = {r.formal_fraction_real:.3f}")
            if r.error:
                print(f"  note: {r.error}")
            for ob in r.open_obligations:
                print(f"  open: {ob.step}  {ob.goal}  → {ob.suggestion}")
    return 0


def cmd_hammer(args) -> int:
    theorems = _load(args)
    backend = IsabelleBackend()
    res = backend.hammer_step(theorems[0], args.step, timeout_s=args.timeout)
    if args.json:
        _emit(res.to_dict(), True)
    else:
        print(f"hammer {res.step}: success={res.success} method={res.method} "
              f"({res.message})")
    return 0 if res.success else 1


def cmd_prove(args) -> int:
    """Autonomous loop (SPEC §7): verify → compile isar → check → report."""
    theorems = _load(args)
    backend = IsabelleBackend(
        extra_dirs=getattr(args, "dir", None),
        parent_session=getattr(args, "session", None),
    )
    overall = {"theorems": []}
    exit_code = 0
    for t in theorems:
        rep = verify(t)
        m = compute_metrics(t)
        entry = {
            "theorem": t.name,
            "structurally_valid": rep.valid,
            "errors": [e.to_dict() for e in rep.errors],
            "formal_fraction_static": m.formal_fraction_static,
            "frontier": [h.to_dict() for h in rep.frontier],
        }
        if not rep.valid:
            exit_code = 1
        else:
            chk = backend.check_proof(t, timeout_s=args.timeout)
            entry["isabelle_available"] = chk.available
            entry["formal_fraction_real"] = chk.formal_fraction_real
            entry["open_obligations"] = [o.to_dict() for o in chk.open_obligations]
            if args.out:
                outdir = Path(args.out)
                outdir.mkdir(parents=True, exist_ok=True)
                (outdir / f"{t.name}.thy").write_text(compile_isar(t), encoding="utf-8")
        overall["theorems"].append(entry)
    if args.json:
        _emit(overall, True)
    else:
        for e in overall["theorems"]:
            status = "valid" if e["structurally_valid"] else "INVALID"
            print(f"{e['theorem']}: {status}, "
                  f"formal_fraction_static={e['formal_fraction_static']:.3f}, "
                  f"{len(e['frontier'])} holes")
            for err in e["errors"]:
                print(f"  error {err['code']}: {err['message']}")
    return exit_code


def cmd_tools(args) -> int:
    _emit(tools_description(), True)
    return 0


# --------------------------------------------------------------------------- #
#  Rendering helpers
# --------------------------------------------------------------------------- #


def _theorem_ast(t: Theorem) -> dict:
    return {
        "name": t.name,
        "description": t.description,
        "imports": t.imports,
        "context": [{"name": c.name, "statement": c.statement} for c in t.context],
        "goal": t.goal.statement if t.goal else None,
        "outer_method": t.proof.outer_method,
        "steps": [
            {
                "id": s.id, "claim": s.claim, "by": s.by, "using": s.using,
                "method": s.method, "status": s.static_status,
                "witnesses": s.witnesses,
            }
            for s in t.proof.steps()
        ],
    }


def _print_report(r) -> None:
    flag = "VALID" if r.valid else "INVALID"
    print(f"theorem {r.theorem}: {flag}  "
          f"(formal_fraction_static={r.metrics.formal_fraction_static:.3f}, "
          f"{len(r.frontier)} frontier holes)")
    for e in r.errors:
        loc = f" [{e.step}]" if e.step else ""
        print(f"  error  {e.code}{loc}: {e.message}")
        if e.suggestion:
            print(f"         ↳ {e.suggestion}")
    for w in r.warnings:
        loc = f" [{w.step}]" if w.step else ""
        print(f"  warn   {w.code}{loc}: {w.message}")
    for a in r.advisories:
        print(f"  advise {a.code}: {a.message}")


def _write_or_print(text: str, out: str | None, name: str, target: str) -> None:
    if not out:
        print(text)
        return
    outpath = Path(out)
    if outpath.is_dir() or out.endswith("/"):
        outpath.mkdir(parents=True, exist_ok=True)
        outpath = outpath / f"{name}{_TARGET_EXT[target]}"
    outpath.write_text(text, encoding="utf-8")
    print(f"wrote {outpath}")


# --------------------------------------------------------------------------- #
#  Argument parser
# --------------------------------------------------------------------------- #


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="i-orca", description="i-orca proof toolchain")
    p.add_argument("--version", action="version", version=f"i-orca {__version__}")
    p.add_argument("--tools", action="store_true", help="print the tool surface as JSON and exit")
    p.add_argument("--json", action="store_true", help="JSON output (top-level shortcut)")
    sub = p.add_subparsers(dest="command")

    def add_input(sp):
        sp.add_argument("file", nargs="?", help="path to a .i.orca.md file")
        sp.add_argument("--source", help="inline .i.orca.md source (instead of a file)")
        sp.add_argument("--json", action="store_true", help="JSON output")

    sp = sub.add_parser("parse", help="parse to AST")
    add_input(sp)
    sp.set_defaults(func=cmd_parse)

    sp = sub.add_parser("verify", help="structural verification (no Isabelle)")
    add_input(sp)
    sp.add_argument("--strict", action="store_true")
    sp.set_defaults(func=cmd_verify)

    sp = sub.add_parser("compile", help="compile to a backend")
    add_input(sp)
    sp.add_argument("--target", choices=["isar", "tex", "lean4"], default="isar")
    sp.add_argument("--out", help="output dir/file (default: stdout)")
    sp.add_argument("--document", action="store_true",
                    help="(isar/tex) one combined document for all theorems")
    sp.add_argument("--theory", help="(isar --document) theory name")
    sp.set_defaults(func=cmd_compile)

    sp = sub.add_parser("metrics", help="formal-fraction metrics")
    add_input(sp)
    sp.set_defaults(func=cmd_metrics)

    sp = sub.add_parser("check", help="kernel-check via Isabelle (warm session)")
    add_input(sp)
    sp.add_argument("--timeout", type=int, default=300)
    sp.add_argument("-d", "--dir", action="append", metavar="DIR",
                    help="directory holding project-local theories named in ## imports "
                         "(repeatable; resolves a sibling like MinimalDecider)")
    sp.add_argument("--session", help="parent Isabelle session for the check "
                                      "(default: inferred from imports)")
    sp.set_defaults(func=cmd_check)

    sp = sub.add_parser("hammer", help="Sledgehammer one hole")
    add_input(sp)
    sp.add_argument("--step", required=True, help="step id to hammer")
    sp.add_argument("--timeout", type=int, default=60)
    sp.set_defaults(func=cmd_hammer)

    sp = sub.add_parser("prove", help="autonomous loop: verify → isar → check")
    add_input(sp)
    sp.add_argument("--timeout", type=int, default=300)
    sp.add_argument("--out", help="dir to write .thy artifacts")
    sp.add_argument("-d", "--dir", action="append", metavar="DIR",
                    help="directory holding project-local theories named in ## imports "
                         "(repeatable)")
    sp.add_argument("--session", help="parent Isabelle session (default: inferred)")
    sp.set_defaults(func=cmd_prove)

    sp = sub.add_parser("tools", help="print the tool surface as JSON")
    sp.set_defaults(func=cmd_tools)
    return p


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.tools:
        return cmd_tools(args)
    if not getattr(args, "command", None):
        parser.print_help()
        return 0
    try:
        return args.func(args)
    except ParseError as ex:
        print(f"parse error: {ex}", file=sys.stderr)
        return 2
    except FileNotFoundError as ex:
        print(f"error: {ex}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
