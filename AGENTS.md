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
Retrieves and What It Computes"). **All ten are fully kernel-proved** under
Isabelle2025-2 — the combined `Fieldrun.thy` builds clean (exit 0) with zero
`sorry`. The analytic steps (the k/PR limit, the Diffuseness k-source fraction,
both Maslov bounds) are real multi-step i-orca proofs; Theorem 3's open half was
restated faithfully (the first encoding was a vacuous placeholder) — see the
research note in `examples/fieldrun/RESULTS.md` and the companion
`examples/fieldrun/separation/Separation.thy`. Generated `.thy` / `.tex` /
`.lean` artifacts live under `examples/fieldrun/artifacts/`.

Four further corpora extend the examples on the same substrate-`.thy` +
thin-`.i.orca.md`-surface pattern: `examples/complexity/` (non-paper extensions) and
`examples/provenance/` (the attribution dichotomy), both in-house, plus a **"canonical
proofs from other authors"** track — `examples/watermark/` (Aaronson's LLM watermark:
distortion-free sampling + key-based detectability, 12 theorems), `examples/tropical/`
(the tropical-geometry view of ReLU networks — Zhang–Naitzat–Lim, ICML 2018, with
Pachter–Sturmfels and Maragos et al.; 20 theorems), `examples/superposition/` (the
geometric core of Anthropic's "Toy Models of Superposition": interference, orthogonal
capacity, and the Welch bound; 10 theorems), and `examples/jl/` (the
Johnson–Lindenstrauss random-projection lemma: unbiased projection, O(log n/ε²)
dimension, probabilistic-method existence; 6 theorems). All kernel-checked under Isabelle2025-2;
each ships its own `PROPOSAL.md` / `README.md` / `RESULTS.md`.

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
