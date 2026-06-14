# i-orca grammar

An `.i.orca.md` file is Markdown: `#`/`##` headings, blockquotes, and GitHub
tables. The parser is line-oriented (no Markdown library) — the same idiom as
n-orca / q-orca. This document is the normative reference for the surface syntax;
see [`../SPEC.md`](../SPEC.md) for the design rationale.

## Document structure

```
# theorem <Name>
> one-line informal description        (optional blockquote)

## imports        | Theory |
## context        | Name | Statement |
## goal           | Statement |
## proof [(method)]   | Id | Claim | By | Using | Method | Status |
## base               (proof sub-block: induction base case)
## step (ih: …)       (proof sub-block: induction step; binds the hypothesis `ih`)
## case <name>        (proof sub-block: one arm of a case split)
```

A file may hold several `# theorem` blocks. Each runs until the next `# theorem`
(or any other `#` H1) or end of file. Everything from `## proof` to the end of
the theorem belongs to one proof; the `## base` / `## step` / `## case` headings
in that span open scoped sub-blocks.

## Sections

| Section | Columns | Lowers to |
|---------|---------|-----------|
| `## imports` | `Theory` | Isar `imports` (defaults to `Main`) |
| `## context` | `Name`, `Statement` | named theorem `assumes` + the `UNKNOWN_LEMMA_REFERENCE` namespace + Sledgehammer hints |
| `## goal` | `Statement` | the `shows` proposition |
| `## proof [(m)]` | step rows | `proof (m) … qed` (default `proof -`) |

The optional `## proof` argument is the outer Isar method: `(rule ccontr)`,
`(induction n)`, `(cases x)`, etc. A contradiction rule auto-introduces the
negated goal as the assumption `neg`.

## The proof-step row

```
| Id | Claim | By | Using | Method | Status |
```

- **Id** — unique step name; becomes the Isar fact name (`have Id: …`).
- **Claim** — the proposition, in Isabelle/HOL surface syntax. **The single
  source of truth**: the Isar `have`, the TeX statement, and the Lean `have`
  type all derive from it. Existentials may use the `obtain <vars> where <prop>`
  form to name witnesses (→ Isar `obtain`).
- **By** — informal intermediate-register justification. Not decoration: it
  becomes the prompt context when Sledgehammer fires at this step.
- **Using** — comma-separated ids this step depends on. **This column is the
  dependency DAG** the verifier checks; it also lowers to Isar `using` (the
  Sledgehammer relevance filter). May cite prior step ids, `## context` names,
  an in-scope `ih`, or the implicit `neg` (under a contradiction rule).
- **Method** — optional Isar method (`simp`, `auto`, `(metis …)`, `blast`,
  `algebra`, `sledgehammer`, `sorry`). A concrete method counts toward
  `formal_fraction_static`; `sledgehammer`/`sorry`/absent is a frontier hole.
- **Status** — lifecycle, authored as intent and overwritten by a backend run:

  | Status | Meaning | In `formal_fraction`? |
  |--------|---------|-----------------------|
  | `sketched` | prose only / `sorry`, no method | no (NL-only) |
  | `hammer` | marked for Sledgehammer (a structured hole) | no (frontier) |
  | `method` | explicit method present, expected to check | static estimate |
  | `checked` | Isabelle confirmed (backend-populated) | yes (real) |
  | `failed` | method present but Isabelle rejected it | no — a real error |

  A blank/`—` status is inferred from the method.

Empty cells may be written `—`, `-`, or left blank.

## Worked example

See [`../examples/fieldrun/fieldrun.i.orca.md`](../examples/fieldrun/fieldrun.i.orca.md)
for ten complete proofs (the theorems of the fieldrun paper), and SPEC §4 for the
`SqrtTwoIrrational` walkthrough.

## What the verifier checks

Decidable, zero-Isabelle structural checks only (SPEC §5). Stable codes:

- **DAG** — `DUPLICATE_STEP_ID`, `CIRCULAR_DEPENDENCY`, `FORWARD_REFERENCE`,
  `ORPHAN_STEP` (warning).
- **Discharge** — `UNDISCHARGED_GOAL`, `IFF_ONE_DIRECTION`, `EXISTS_NO_WITNESS`.
- **Scope** — `HYP_OUT_OF_SCOPE`, `VAR_UNBOUND` (advisory).
- **Cases/Induction** — `NON_EXHAUSTIVE_CASES` (advisory unless a disjunction is
  declared), `INDUCTION_MISSING_BASE`, `INDUCTION_MISSING_STEP`.
- **Naming** — `UNKNOWN_LEMMA_REFERENCE`.

A green verify means the proof *skeleton* is well-formed — **not** that the proof
is true. Truth comes only from the Isabelle kernel (`i-orca check`).
