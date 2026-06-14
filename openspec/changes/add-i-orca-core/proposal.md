# Add i-orca core toolchain

## Why

SPEC.md described i-orca as a design proposal ("nothing here is built"). This
change implements the full toolchain so the family's verify-before-execute
discipline extends into formal mathematics, and uses it to formalise the
theorems of the fieldrun paper.

## What changes

- **Parser** (`i_orca/parser`): Markdown tables → AST (`Theorem`, `Imports`,
  `Context`, `Goal`, `Step`, `Block`, `Proof`).
- **Static verifier** (`i_orca/verifier`): five decidable check families with
  stable codes (DAG, discharge, scope, cases/induction, naming), zero Isabelle.
- **Compilers** (`i_orca/compiler`): Isar (primary, checkable `.thy` + combined
  document), TeX (always emits), Lean 4 (structure-only skeleton).
- **Backend** (`i_orca/backend`): Isabelle runner with graceful degradation;
  `check_proof` / `hammer_step` with structured open obligations.
- **Surfaces**: `cli.py` (parse/verify/compile/metrics/check/hammer/prove/tools),
  `mcp_server.py` (seven-tool MCP surface + `--tools` self-description),
  `metrics.py` (`formal_fraction_static`/`_real`).
- **Corpus**: `examples/fieldrun/` — i-orca proofs of all ten fieldrun
  theorems/propositions, with generated artifacts and a kernel-check report.

## Non-goals

- Not a proof checker (SPEC §2): the static layer decides only well-formedness.
- Lean export is structure-only; methods do not transfer (SPEC §11.4).

## Impact

New package `i_orca`; new examples and docs. No external dependencies for the
cheap loop; the optional `mcp` SDK and an Isabelle distribution gate the MCP
server and the kernel path respectively.
