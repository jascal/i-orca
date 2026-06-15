"""i-orca MCP server (SPEC §7) — the primary way an LLM touches i-orca.

The product is ``source: str`` in → structured JSON out, with stable codes
designed as a feedback channel for an agent loop. The cheap loop
(``parse``/``verify``/``compile``/``refine``/``metrics``) needs zero Isabelle;
the expensive loop (``check``/``hammer``) hides a slow, stateful prover behind
stateless-looking per-step calls.

Run with ``python -m i_orca.mcp_server`` over stdio, or ``i-orca-mcp``::

    claude mcp add i-orca /path/to/.venv/bin/python -m i_orca.mcp_server

The ``mcp`` SDK is an optional dependency (``pip install i-orca[mcp]``); the rest
of the package imports without it.
"""
from __future__ import annotations

from typing import Any

from i_orca import __version__
from i_orca.backend import IsabelleBackend
from i_orca.compiler import compile_isar, compile_lean4, compile_tex
from i_orca.compiler.isar import compile_isar_document
from i_orca.compiler.tex import compile_tex_document
from i_orca.metrics import compute_metrics
from i_orca.parser import ParseError, parse
from i_orca.tools import tools_description
from i_orca.verifier import verify

try:  # the MCP SDK is optional — only the server entry point needs it.
    from mcp.server.fastmcp import FastMCP
except ImportError:  # pragma: no cover - exercised only when mcp is absent
    FastMCP = None


def _theorems(source: str):
    return parse(source).theorems


def parse_proof(source: str) -> dict[str, Any]:
    """Parse ``.i.orca.md`` source to AST JSON (steps, DAG edges, scopes, goal)."""
    try:
        theorems = _theorems(source)
    except ParseError as ex:
        return {"error": f"parse error: {ex}"}
    from i_orca.cli import _theorem_ast

    return {"version": __version__, "theorems": [_theorem_ast(t) for t in theorems]}


def verify_proof(source: str, strict: bool = False) -> dict[str, Any]:
    """Structural verify → {valid, errors[], frontier[], formal_fraction_static, dag}."""
    try:
        theorems = _theorems(source)
    except ParseError as ex:
        return {"error": f"parse error: {ex}"}
    return {"reports": [verify(t, strict=strict).to_dict() for t in theorems]}


def compile_proof(
    source: str,
    target: str = "isar",
    document: bool = False,
    theory: str | None = None,
) -> dict[str, Any]:
    """Compile to ``isar`` | ``tex`` | ``lean4`` (holes → ``sorry``).

    ``document=True`` emits ONE combined artifact for all theorems (``isar``/``tex``
    only); ``theory`` names the combined isar theory. Mirrors the CLI ``compile
    --document`` / ``--theory``.
    """
    try:
        theorems = _theorems(source)
    except ParseError as ex:
        return {"error": f"parse error: {ex}"}
    if document and target == "isar":
        return {"target": target, "document": True,
                "output": compile_isar_document(theorems, theory_name=theory or "Fieldrun")}
    if document and target == "tex":
        return {"target": target, "document": True, "output": compile_tex_document(theorems)}
    if document:
        return {"error": f"--document not supported for target {target!r} (isar | tex only)"}
    fn = {"isar": compile_isar, "tex": compile_tex, "lean4": compile_lean4}.get(target)
    if fn is None:
        return {"error": f"unknown target {target!r}; expected isar | tex | lean4"}
    return {"target": target, "outputs": {t.name: fn(t) for t in theorems}}


def refine_proof(source: str) -> dict[str, Any]:
    """Return structural errors as prompt fragments for the next generation turn.

    i-orca does not auto-edit: the model owns the fix. This hands it every error
    code, suggestion, and open obligation in one structured object (SPEC §7).
    """
    try:
        theorems = _theorems(source)
    except ParseError as ex:
        return {"error": f"parse error: {ex}", "fixable": "syntax"}
    out = []
    for t in theorems:
        rep = verify(t)
        out.append({
            "theorem": t.name,
            "valid": rep.valid,
            "errors": [e.to_dict() for e in rep.errors],
            "warnings": [w.to_dict() for w in rep.warnings],
            "frontier": [h.to_dict() for h in rep.frontier],
        })
    return {"reports": out}


def proof_metrics(source: str) -> dict[str, Any]:
    """formal_fraction_static / frontier counts / status histogram (no Isabelle)."""
    try:
        theorems = _theorems(source)
    except ParseError as ex:
        return {"error": f"parse error: {ex}"}
    return {t.name: compute_metrics(t).to_dict() for t in theorems}


def check_proof(
    source: str,
    timeout_s: int = 300,
    dirs: list[str] | None = None,
    session: str | None = None,
) -> dict[str, Any]:
    """Kernel-check via the warm Isabelle session → per-step status + obligations.

    ``dirs`` registers directories holding project-local theories named in
    ``## imports`` (e.g. a sibling ``MinimalDecider``), so the import resolves from
    source instead of being looked up as a bare file; ``session`` overrides the parent
    Isabelle session. Mirrors the CLI ``check -d/--dir`` / ``--session``.

    Degrades to the static fallback when Isabelle is absent (``available: False``).
    """
    try:
        theorems = _theorems(source)
    except ParseError as ex:
        return {"error": f"parse error: {ex}"}
    backend = IsabelleBackend(extra_dirs=dirs, parent_session=session)
    return {"results": [backend.check_proof(t, timeout_s=timeout_s).to_dict()
                        for t in theorems]}


def hammer_step(
    source: str,
    step_id: str,
    timeout_s: int = 60,
    dirs: list[str] | None = None,
    session: str | None = None,
) -> dict[str, Any]:
    """Sledgehammer one hole → {success, method: 'by (metis …)'}.

    ``dirs`` / ``session`` resolve project-local imports exactly as ``check_proof``.
    """
    try:
        theorems = _theorems(source)
    except ParseError as ex:
        return {"error": f"parse error: {ex}"}
    backend = IsabelleBackend(extra_dirs=dirs, parent_session=session)
    return backend.hammer_step(theorems[0], step_id, timeout_s=timeout_s).to_dict()


def prove_proof(
    source: str,
    timeout_s: int = 300,
    dirs: list[str] | None = None,
    session: str | None = None,
) -> dict[str, Any]:
    """Autonomous-loop report (SPEC §7): structural verify → kernel check per theorem.

    Mirrors the CLI ``prove``: structurally verifies each theorem and, when valid,
    kernel-checks it (``formal_fraction_real`` + open obligations). ``dirs`` / ``session``
    resolve project-local imports exactly as ``check_proof``.
    """
    try:
        theorems = _theorems(source)
    except ParseError as ex:
        return {"error": f"parse error: {ex}"}
    backend = IsabelleBackend(extra_dirs=dirs, parent_session=session)
    out = []
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
        if rep.valid:
            chk = backend.check_proof(t, timeout_s=timeout_s)
            entry["isabelle_available"] = chk.available
            entry["formal_fraction_real"] = chk.formal_fraction_real
            entry["open_obligations"] = [o.to_dict() for o in chk.open_obligations]
        out.append(entry)
    return {"theorems": out}


def describe_tools() -> dict[str, Any]:
    """Self-description for any agent framework (SPEC §7 ``--tools --json``)."""
    return tools_description()


# Pure functions above are unit-testable without the MCP SDK; the block below
# registers them as MCP tools when the SDK is installed.
def _build_app():
    app = FastMCP("i-orca")
    app.tool()(parse_proof)
    app.tool()(verify_proof)
    app.tool()(compile_proof)
    app.tool()(refine_proof)
    app.tool()(proof_metrics)
    app.tool()(check_proof)
    app.tool()(hammer_step)
    app.tool()(prove_proof)
    app.tool()(describe_tools)
    return app


def main() -> None:
    """Entry point for ``python -m i_orca.mcp_server`` / ``i-orca-mcp``."""
    if FastMCP is None:
        raise SystemExit(
            "the 'mcp' package is required for the MCP server: pip install i-orca[mcp]"
        )
    _build_app().run()


if __name__ == "__main__":
    main()
