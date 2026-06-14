# Tasks — add i-orca core toolchain

## 1. AST + parser
- [x] 1.1 Dataclass AST (`ast.py`)
- [x] 1.2 Line-oriented Markdown parser (sections, tables, blocks, witnesses)

## 2. Static verifier
- [x] 2.1 Shared name/scope resolution
- [x] 2.2 DAG checks (duplicate, circular, forward, orphan)
- [x] 2.3 Discharge checks (undischarged goal, iff, existentials)
- [x] 2.4 Scope checks (out-of-scope hypothesis, unbound var)
- [x] 2.5 Cases/induction checks (base/step, exhaustiveness)
- [x] 2.6 Naming check (unknown lemma reference)

## 3. Compilers
- [x] 3.1 Isar (primary, `.thy` + combined document, `\<...>` symbol escapes)
- [x] 3.2 TeX (always emits)
- [x] 3.3 Lean 4 (structure-only skeleton)

## 4. Backend + surfaces
- [x] 4.1 Isabelle runner with graceful degradation
- [x] 4.2 CLI (parse/verify/compile/metrics/check/hammer/prove/tools)
- [x] 4.3 MCP server (seven tools + self-description)
- [x] 4.4 Metrics (`formal_fraction_static`/`_real`)

## 5. Corpus + verification
- [x] 5.1 Author i-orca proofs of all fieldrun theorems
- [x] 5.2 Static-verify all (zero errors)
- [x] 5.3 Generate Isar/TeX/Lean artifacts
- [x] 5.4 Kernel-check against Isabelle (closed-form results)

## 6. Tests + docs
- [x] 6.1 pytest suite (parser, verifier, compilers, backend, cli, mcp, fieldrun)
- [x] 6.2 docs (grammar, mcp), skills, AGENTS.md, README.md
- [x] 6.3 ruff clean
