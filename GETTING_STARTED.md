# Getting started with i-orca

i-orca is a Markdown-table DSL for mathematical proofs whose canonical backend is
**Isabelle/Isar** (with TeX and Lean 4 as secondary exports). You write proofs as
`# theorem` blocks with `## imports` / `## context` / `## goal` / `## proof` tables;
a fast, Isabelle-free **structural verifier** lints the skeleton, and the Isabelle
backend **kernel-checks** it. See [`SPEC.md`](SPEC.md) for the full design and
[`examples/`](examples/) for real files.

> **Read the disclaimer (SPEC §2).** A structurally-valid i-orca proof can still be
> mathematically false. `verify` (green skeleton) is **not** `check` (kernel-proved).
> Always distinguish `formal_fraction_static` from `formal_fraction_real`.

---

## 1. Install

The repo ships a `uv`-managed virtualenv at `.venv` (Python 3.12). To (re)create it
and install the package **with the MCP extra** (needed for the MCP server):

```bash
uv pip install -e ".[mcp]"        # installs i-orca + the `mcp` SDK into .venv
# or, if you manage the venv yourself:  uv sync --extra mcp
```

Sanity check:

```bash
.venv/bin/python -m i_orca.cli --help
.venv/bin/pytest -q                # 51 passing, zero Isabelle needed
```

## 2. Isabelle (only for `check` / `hammer`)

`parse` / `verify` / `compile` / `metrics` need **zero Isabelle**. The kernel path
(`check`, `hammer`, `prove`) needs an Isabelle distribution. Point i-orca at it via
`ISABELLE_HOME` (or put `isabelle` on `PATH`, or set `ISABELLE`/`ISABELLE_BIN`):

```bash
export ISABELLE_HOME=/path/to/Isabelle2025-2
```

---

## 3. MCP setup for Claude

The MCP server is the primary way an agent touches i-orca: `source` string in →
structured JSON out, with stable codes for an agent loop (SPEC §7). A project-scoped
server is already declared in [`.mcp.json`](.mcp.json):

```json
{ "mcpServers": { "i-orca": {
  "command": ".venv/bin/python", "args": ["-m", "i_orca.mcp_server"], "env": {} } } }
```

**To use it in Claude Code:**

1. **Install the `mcp` extra first** (step 1) — without the `mcp` SDK the server
   fails to connect with `No module named mcp`.
2. Approve / add the server:
   - Project `.mcp.json` servers need a one-time approval — run `/mcp` in Claude Code
     and approve `i-orca`; **or**
   - add it explicitly: `claude mcp add i-orca -- .venv/bin/python -m i_orca.mcp_server`
     (run from the repo root so `-m i_orca.mcp_server` resolves).
3. Verify it connects: `claude mcp list` should show `i-orca: ✔ Connected`.
4. **Reload the session** if you added it mid-conversation — a running session only
   surfaces MCP tools that existed at startup.

**Tool surface (full parity with the CLI):**

| MCP tool | Isabelle? | CLI equivalent |
|----------|-----------|----------------|
| `parse_proof(source)` | no | `parse` |
| `verify_proof(source, strict)` | no | `verify` |
| `compile_proof(source, target, document, theory)` | no | `compile` |
| `refine_proof(source)` | no | (structured errors) |
| `proof_metrics(source)` | no | `metrics` |
| `check_proof(source, timeout_s, dirs, session)` | **yes** | `check` |
| `hammer_step(source, step_id, timeout_s, dirs, session)` | **yes** | `hammer` |
| `prove_proof(source, timeout_s, dirs, session)` | **yes** | `prove` |
| `describe_tools()` | no | `tools` |

`dirs` / `session` (and the CLI's `-d/--dir` / `--session`) register **project-local
theory directories** so a `## imports` line can name a sibling theory — see §5.

---

## 4. CLI quickstart

```bash
PY=.venv/bin/python

# structural verify (instant, no Isabelle): DAG / scope / discharge / naming
$PY -m i_orca.cli verify examples/fieldrun/fieldrun.i.orca.md

# compile to a backend (holes → sorry); --document makes one combined theory
$PY -m i_orca.cli compile examples/fieldrun/fieldrun.i.orca.md --target isar
$PY -m i_orca.cli compile examples/fieldrun/fieldrun.i.orca.md --target tex --document

# coverage estimate (no Isabelle)
$PY -m i_orca.cli metrics examples/fieldrun/fieldrun.i.orca.md

# kernel-check (needs ISABELLE_HOME)
ISABELLE_HOME=/path/to/Isabelle $PY -m i_orca.cli check examples/fieldrun/fieldrun.i.orca.md
```

## 5. Checking proofs that import project-local theories

The **paper proofs** ([`examples/fieldrun/fieldrun.i.orca.md`](examples/fieldrun/fieldrun.i.orca.md))
import only standard sessions (`Complex_Main`, `HOL-Analysis.*`, `Main`), so they
check with no extra flags.

Some files cite lemmas from **sibling theories in this repo** — e.g.
[`examples/complexity/complexity.i.orca.md`](examples/complexity/complexity.i.orca.md)
states each non-paper theorem and discharges it by `(rule <lemma>)` against a lemma
in `MinimalDecider` / `Hub` / `MarginBridge`. Those theories aren't standard sessions,
so tell the backend where they live with `-d` (repeatable):

```bash
ISABELLE_HOME=/path/to/Isabelle .venv/bin/python -m i_orca.cli check \
  examples/complexity/complexity.i.orca.md \
  -d examples/complexity -d examples/fieldrun/separation
```

The same as an MCP call:

```jsonc
check_proof({
  "source": "<contents of complexity.i.orca.md>",
  "dirs": ["examples/complexity", "examples/fieldrun/separation"]
})
```

Each registered directory is emitted as an Isabelle `directories` entry in the
throwaway build session, so `imports MinimalDecider` resolves from source instead of
being looked up as a bare file. (Tip: don't list the cited lemma in `## context` —
the compiler lowers context rows to local `assumes`, which would turn a cite into a
vacuous `P ⟹ P`; rely on `## imports` + the `(rule …)` method instead.)

## 6. The autonomous loop

```
generate .i.orca.md → verify_proof (cheap) → refine until valid
   → compile_proof isar → check_proof (warm session)
   → for each open obligation: hammer_step → on fail, refine that step
   → repeat until formal_fraction_real → 1.0
```

`prove` / `prove_proof` runs the verify → check half and reports
`formal_fraction_static` vs `formal_fraction_real` per theorem.
