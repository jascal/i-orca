# i-orca — project conventions (OpenSpec)

i-orca is a Markdown-table DSL for writing mathematical proofs at the register
LLMs naturally produce, with **Isabelle/Isar** as the canonical backend and TeX
+ Lean 4 as secondary exports. It is a Pillar-1 sibling in the Orca language
family (`i-orca : Isabelle :: n-orca : PyTorch :: orca-lang : XState`).

## Toolchain

- Python 3.12, `pytest` + `ruff`, packaged with hatchling.
- `.venv/bin/pytest` for the suite; `.venv/bin/ruff check .` for lint.
- The MCP server uses the optional `mcp` SDK; everything else is dependency-free.
- The Isabelle backend (`i_orca/backend`) needs an Isabelle distribution for
  `check`/`hammer`; it degrades gracefully when absent. Point it at one with
  `ISABELLE`, `ISABELLE_BIN`, or `ISABELLE_HOME`.

## Conventions

- OpenSpec-driven: non-trivial work lands through a change in
  `openspec/changes/<id>/` (`proposal.md`, `tasks.md`,
  `specs/<capability>/spec.md`). Validate with `openspec validate <id>`.
- Project-local skills in `.claude/skills/`: `i-orca-verify`, `i-orca-compile`,
  `i-orca-prove`. Prefer them over hand-rolling equivalent operations.
- **Honesty discipline (load-bearing, SPEC §2/§11.5):** i-orca is a structural
  linter + scaffold compiler, **not** a proof checker. A green `verify` means
  the proof skeleton is well-formed — never that the proof is true. Every
  surface must distinguish *structurally well-formed* from *kernel-proved*. Only
  Isabelle's kernel (`i-orca check`, status `checked`) certifies truth.

## Layout

```
i_orca/
  ast.py                 # Theorem, Imports, Context, Goal, Step, Block, Proof
  parser/                # markdown tables → AST
  verifier/              # structural.py · scope.py · cases.py · discharge.py · naming.py
  compiler/              # isar.py (PRIMARY) · tex.py · lean4.py
  backend/               # isabelle.py: warm session, Sledgehammer, result parse
  metrics.py · tools.py · cli.py · mcp_server.py
examples/fieldrun/       # proofs of the fieldrun paper's theorems (+ artifacts/)
docs/                    # grammar.md · mcp.md · verifier-backend-metrics.md
```
