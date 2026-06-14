# i-orca MCP surface

MCP is the primary way an LLM touches i-orca (SPEC §7): `source: string` in →
structured JSON out, with stable codes designed as a feedback channel for an
agent loop. It matters more here than for any sibling because the backend
(Isabelle) is the slowest and most stateful in the family — and the server hides
that behind stateless-looking per-step calls.

## Running the server

```bash
pip install i-orca[mcp]          # the MCP SDK is an optional dependency
python -m i_orca.mcp_server      # stdio
# or, registered with Claude Code:
claude mcp add i-orca /path/to/.venv/bin/python -m i_orca.mcp_server
```

`parse` / `verify` / `compile` need zero Isabelle; only `check` / `hammer` bind
to a warm Isabelle session, and they degrade gracefully when it is absent.

## Tools

| Tool | Isabelle? | Latency | Returns |
|------|-----------|---------|---------|
| `parse_proof(source)` | no | ms | AST JSON: steps, DAG edges, scopes, goal |
| `verify_proof(source, strict?)` | no | ms | `{valid, errors[], frontier[], formal_fraction_static, dag}` |
| `compile_proof(source, target)` | no | ms | `isar` \| `tex` \| `lean4` source (holes → `sorry`) |
| `refine_proof(source)` | no | ms | structural errors as prompt fragments (the model fixes) |
| `proof_metrics(source)` | no | ms | `formal_fraction_static`, frontier counts, status histogram |
| `check_proof(source, timeout_s?)` | **yes (warm)** | s–min | per-step real status + open obligations |
| `hammer_step(source, step_id, timeout_s?)` | **yes (warm)** | bounded s | `{success, method: "by (metis …)"}` for one hole |
| `describe_tools()` | — | — | self-description (also `i-orca --tools`) |

The top five are the **cheap loop** (CI-runnable, the model's tight cadence).
The bottom two are the **expensive loop**, where the MCP design earns its keep.

## Structured errors are prompt fragments

`check_proof` returns each open obligation shaped to drop straight into the next
generation turn — goal, fixed vars, assumptions in scope, facts cited, the
model's own prior informal reason, and a suggested next call:

```json
{ "available": true, "formal_fraction_real": 0.71,
  "steps": {"s2": "checked", "s3": "checked", "s5": "failed"},
  "open_obligations": [
    { "step": "s5", "goal": "even q",
      "fixed": ["p","q","k"], "assume": ["q ≠ 0","sqrt 2 = p/q","coprime p q"],
      "using": ["s1","s4"], "by": "substitute, even_sq_even",
      "suggestion": "hammer_step(s5) with using=[s1, s4]" } ] }
```

No parsing Isabelle's stderr, no temp `.thy`, no shell — the server absorbs heap
management, ATP orchestration, and result parsing.

## The autonomous loop

```
generate .i.orca.md → verify_proof (cheap) → refine_proof until valid
   → compile_proof isar → check_proof (warm session)
   → for each open obligation: hammer_step → on fail, refine that step
   → repeat until formal_fraction_real → 1.0
   → exports: compile_proof tex (always) | compile_proof lean4 (best-effort)
```

## Graceful degradation

When no Isabelle distribution is found, `check_proof` / `hammer_step` return
`available: False` with the static fallback (every step's `static_status`, the
open obligations, `formal_fraction_real: null`) — never an exception. CI and the
fast refine loop run without the heavy dependency.
