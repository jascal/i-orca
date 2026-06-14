# Spec: proof-dsl

## ADDED Requirements

### Requirement: Markdown-table proof documents parse to a typed AST
An `.i.orca.md` document SHALL declare one or more `# theorem` blocks, each with
optional `## imports` / `## context`, a single `## goal`, and a `## proof` whose
rows are `| Id | Claim | By | Using | Method | Status |`, plus optional
`## base` / `## step (ih: …)` / `## case <name>` scoped sub-blocks.

#### Scenario: A well-formed theorem parses
- **WHEN** a document with a `# theorem`, `## goal`, and `## proof` table is parsed
- **THEN** the result is a `Theorem` whose steps preserve Id, Claim, Using DAG,
  Method, and an inferred or authored Status

#### Scenario: Existential witnesses
- **WHEN** a Claim uses the `obtain <vars> where <prop>` form
- **THEN** the step records the witnesses and lowers to Isar `obtain`

### Requirement: The static verifier decides skeleton well-formedness with stable codes
The verifier SHALL run with zero Isabelle and emit stable, LLM-actionable codes
for DAG, discharge, scope, cases/induction, and naming failures, distinguishing
errors (block the lowering) from advisories (degrade when the splitting
principle is undeclared). It SHALL NOT assert the truth of any step.

#### Scenario: Forward reference is rejected
- **WHEN** a step cites another step declared later
- **THEN** the report is invalid with code `FORWARD_REFERENCE`

#### Scenario: Holes are frontier, not errors
- **WHEN** a step's method is `sledgehammer`/`sorry`/absent
- **THEN** it is reported in `frontier` and excluded from `formal_fraction_static`,
  never as an error

### Requirement: Compilation to three asymmetric backends
The toolchain SHALL compile a theorem to Isar (primary, a checkable `.thy` with
`## context` as named assumptions and holes as `sorry`), TeX (always emits), and
Lean 4 (structure-only skeleton). Propositions emitted to Isar SHALL use
Isabelle `\<...>` symbol escapes.

#### Scenario: Isar lowering is self-contained
- **WHEN** a verified theorem is compiled to Isar
- **THEN** the `.thy` declares the context rows as `assumes`, every step as a
  `have`/`show`/`obtain`, and is accepted by Isabelle's kernel for steps with a
  correct concrete method

### Requirement: The Isabelle backend degrades gracefully
`check_proof` and `hammer_step` SHALL find Isabelle via `ISABELLE` /
`ISABELLE_BIN` / `ISABELLE_HOME` / `PATH`, and when none is present SHALL return
a structured `available: False` result with the static fallback rather than
raising.

#### Scenario: No Isabelle present
- **WHEN** `check_proof` runs without an Isabelle distribution
- **THEN** it returns `available: False`, `formal_fraction_real: null`, and the
  per-step static statuses plus open obligations
