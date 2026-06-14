"""Self-describing tool surface (SPEC §7), shared by the CLI and the MCP server.

The top five are the *cheap loop* (zero Isabelle, CI-runnable). The bottom two
are the *expensive loop* bound to a warm Isabelle session.
"""
from __future__ import annotations

TOOL_SPECS = [
    {
        "name": "parse_proof",
        "isabelle": False,
        "latency": "ms",
        "summary": "Parse .i.orca.md → AST JSON (steps, DAG edges, scopes, goal).",
        "params": {"source": "str (the .i.orca.md text)"},
    },
    {
        "name": "verify_proof",
        "isabelle": False,
        "latency": "ms",
        "summary": "Structural verify → {valid, errors[], frontier[], "
                   "formal_fraction_static, dag}.",
        "params": {"source": "str", "strict": "bool (warnings → errors)"},
    },
    {
        "name": "compile_proof",
        "isabelle": False,
        "latency": "ms",
        "summary": "Compile to isar | tex | lean4 (holes → sorry).",
        "params": {"source": "str", "target": "isar | tex | lean4"},
    },
    {
        "name": "refine_proof",
        "isabelle": False,
        "latency": "s (LLM)",
        "summary": "Return the structural errors as prompt fragments for the next "
                   "generation turn (the model does the fix).",
        "params": {"source": "str"},
    },
    {
        "name": "check_proof",
        "isabelle": True,
        "latency": "s–min (warm)",
        "summary": "Kernel-check via the warm Isabelle session → per-step real "
                   "status + open obligations. Degrades to static fallback.",
        "params": {"source": "str", "timeout_s": "int"},
    },
    {
        "name": "hammer_step",
        "isabelle": True,
        "latency": "bounded s (warm)",
        "summary": "Sledgehammer one hole → {success, method: 'by (metis …)'}.",
        "params": {"source": "str", "step_id": "str", "timeout_s": "int"},
    },
    {
        "name": "proof_metrics",
        "isabelle": False,
        "latency": "ms",
        "summary": "formal_fraction_static / frontier counts / status histogram.",
        "params": {"source": "str"},
    },
]


def tools_description() -> dict:
    return {
        "name": "i-orca",
        "cheap_loop": [t["name"] for t in TOOL_SPECS if not t["isabelle"]],
        "expensive_loop": [t["name"] for t in TOOL_SPECS if t["isabelle"]],
        "tools": TOOL_SPECS,
    }
