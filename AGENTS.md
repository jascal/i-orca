# AGENTS.md — i-orca

Orientation for coding agents working in this repo. Read
[`SPEC.md`](./SPEC.md) for the full design and the *honest reckonings* (§11);
this file is the operational summary.

## What i-orca is (and is not)

i-orca is a **Markdown-table DSL for mathematical proofs at the register LLMs
naturally produce**, with **Isabelle/Isar** as the canonical, checkable backend
and **TeX** + **Lean 4** as secondary exports.

```
i-orca : Isabelle  ::  n-orca : PyTorch  ::  orca-lang : XState
```

**It is a structural linter + scaffold compiler, NOT a proof checker.** The
verifier decides a strictly-weaker, *decidable* property — that the proof
*skeleton* is well-formed (the dependency DAG, scoping, case/induction
structure, name resolution). Truth is delegated to Isabelle's kernel. A green
`verify` must never be read as "proved" (SPEC §2, §11.5). This is load-bearing:
a structurally-valid proof can be mathematically false and looks authoritative.

## The two layers

| Layer | Decidable? | Tool | Needs Isabelle? |
|-------|-----------|------|-----------------|
| Proof skeleton — DAG, scope, cases, naming | yes | `verify` | no |
| Step validity — is each inference *true* | no | `check` / `hammer` | yes (warm session) |

`formal_fraction_static` (method coverage, no Isabelle) vs `formal_fraction_real`
(steps the kernel accepts). Their gap is the metric (SPEC §8).

## Commands

```bash
.venv/bin/pytest                              # full suite
.venv/bin/ruff check .                         # lint
i-orca verify  <file.i.orca.md>                # structural (cheap, no Isabelle)
i-orca compile <file> --target isar|tex|lean4  # backends (holes → sorry)
i-orca compile <file> --target isar --document # one combined .thy
i-orca check   <file>                          # kernel-check (needs Isabelle)
i-orca prove   <file> --out <dir>              # autonomous loop → .thy artifacts
i-orca --tools                                 # JSON self-description
```

`check`/`hammer` find Isabelle via `ISABELLE` / `ISABELLE_BIN` / `ISABELLE_HOME`
or `isabelle` on `PATH`, and degrade gracefully (`available: False`) when absent.

## Grammar in one screen

```
# theorem Name
> informal one-liner
## imports   | Theory |
## context   | Name | Statement |     (→ named assumptions; the lemma namespace)
## goal      | Statement |
## proof [(method)]   | Id | Claim | By | Using | Method | Status |
## base / ## step (ih: …) / ## case <name>   (scoped sub-blocks)
```

A step row `| Id | Claim | By | Using | Method | Status |` lowers to
`have Id: "Claim" using Using by Method`. The **Claim** is the single source of
truth; **Using** is the dependency DAG *and* the Sledgehammer relevance filter;
**Method** = hole (`sledgehammer`/`sorry`/blank) → `sorry` + frontier. See
[`docs/grammar.md`](./docs/grammar.md).

## Stable verifier codes (SPEC §5)

`DUPLICATE_STEP_ID`, `CIRCULAR_DEPENDENCY`, `FORWARD_REFERENCE`, `ORPHAN_STEP` ·
`UNDISCHARGED_GOAL`, `IFF_ONE_DIRECTION`, `EXISTS_NO_WITNESS` ·
`HYP_OUT_OF_SCOPE`, `VAR_UNBOUND` · `NON_EXHAUSTIVE_CASES`,
`INDUCTION_MISSING_BASE`, `INDUCTION_MISSING_STEP` · `UNKNOWN_LEMMA_REFERENCE`.
Errors block the Isar lowering; advisories degrade where the splitting principle
isn't declared.

## The worked corpus

[`examples/fieldrun/fieldrun.i.orca.md`](./examples/fieldrun/fieldrun.i.orca.md)
proves the ten theorems/propositions of the fieldrun paper ("What a Transformer
Retrieves and What It Computes"). The closed-form results
(cardinality-inertness, the non-truth-functionality budget, the weighted-
threshold witness, recovered probability = softmax, the power-diagram cell
identity, the margin–distance identity) carry a concrete method on every step;
the parts the paper itself leaves open (general Horn separation; the Maslov
limit; the asymptotic localisation bound) are honest frontier holes. Generated
`.thy` / `.tex` / `.lean` artifacts live under `examples/fieldrun/artifacts/`.

## Gotchas

- **Emit Isabelle `\<...>` symbol escapes in propositions, not raw Unicode** —
  the Isar compiler does this automatically (`isar_term`); document text in
  `text \<open>…\<close>` cartouches passes raw Unicode through.
- **No `|` inside a table cell** — it splits the Markdown column. Use words
  (`norm`, `card V`) or other delimiters.
- Mark a step honestly: a concrete method you believe checks is `method`; a step
  you intend Sledgehammer to fill is `hammer`; a genuine hole is `sketched`.
  Never paper over a real gap with a method that won't check — `check` will mark
  it `failed`, which is the point.
