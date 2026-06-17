# Aaronson's LLM watermark — i-orca corpus

A kernel-checked formalisation of the mathematical core of **Scott Aaronson's
watermarking scheme for language-model output** (UT Austin; OpenAI 2022–2023). This is
the first entry in i-orca's **"canonical proofs from other authors"** track: the same
discipline as the in-house `fieldrun` / `complexity` / `provenance` corpora, applied to
a well-known external result.

> ⚠️ As everywhere in i-orca, a green `i-orca verify` certifies only that the proof
> *skeleton* is well-formed. Truth is the kernel's: every theorem here is discharged by
> `(rule <lemma>)` against a hand-authored Isabelle lemma, and the whole `Watermark`
> session builds under Isabelle2025-2 with **zero `sorry`**.

## The idea in one line

Replace sampling `token ∼ p` with `token = argmax_i r_i^(1/p_i)`, where the `r_i ∈ (0,1)`
come from a secret-keyed PRF on the context. This is **distortion-free** (marginally the
output is still distributed as `p`) yet **detectable by anyone with the key** (the chosen
token's `r` is biased toward 1). See [`PROPOSAL.md`](PROPOSAL.md).

## Layout

| File | Role |
|------|------|
| [`GumbelSelect.thy`](GumbelSelect.thy) | the selection rule: Gumbel-max ⇔ exponential-race, determinism, per-coordinate pushforward CDF |
| [`Unbiased.thy`](Unbiased.thy) | distortion-freeness: the conditional-win collapse and the `∫₀¹ u^((1−p)/p) du = p` payoff |
| [`Detect.thy`](Detect.thy) | detectability: null score `Exp(1)`, score monotonicity, the chosen-value bias and its mean `1/(1+p)` |
| [`ROOT`](ROOT) | Isabelle session `Watermark` (parent `HOL-Analysis`) |
| [`watermark.i.orca.md`](watermark.i.orca.md) | the i-orca surface: 12 theorems, each `(rule <lemma>)` |
| [`PROPOSAL.md`](PROPOSAL.md) | the scheme, the formal-vs-meta table, honest reckonings, open targets |
| [`RESULTS.md`](RESULTS.md) | verification status and commands |

The `.thy` files are the **hand-authored, kernel-checked substrate**; the `.i.orca.md`
is the thin i-orca surface over it (the `complexity` / `provenance` pattern). Heavy
content — the `powr`/`ln` algebra, the FTC-free power integral, the order isomorphisms —
lives in the substrate; each surface theorem states the result in i-orca form and cites
its lemma.

## Verify

```bash
# Layer 1 — structural skeleton (zero Isabelle)
i-orca verify examples/watermark/watermark.i.orca.md
#   -> all 12 theorems VALID, formal_fraction_static = 1.000

# Layer 2 — kernel check of the substrate (the load-bearing math)
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/watermark \
  -o quick_and_dirty Watermark
#   -> Finished Watermark, exit 0, zero sorry
```

To also kernel-check the **surface**, compile it into the session and rebuild:

```bash
i-orca compile examples/watermark/watermark.i.orca.md --target isar \
  --document --theory WatermarkSurface --out examples/watermark/WatermarkSurface.thy
# append "WatermarkSurface" to ROOT, rebuild -> exit 0 (every (rule ...) non-vacuous)
# WatermarkSurface.thy is a regenerable artifact; not committed.
```

The standalone `i-orca check` builds each theorem under a plain HOL parent and cannot
load this project-local session — an import-resolution limit, not a math failure (same
caveat as the `provenance` and `complexity` corpora).

## What it proves (and what it doesn't)

Twelve kernel-checked cores spanning the selection rule, distortion-freeness, and
detectability — see the table in [`PROPOSAL.md`](PROPOSAL.md). The theorems are honest
about scope: independence is modelled algebraically (the product-measure/Fubini lift is
an open target), the integrals stay in the elementary regime, and the `T`-token
concentration bound that turns mean-separation into a false-positive guarantee is left
to `HOL-Probability`. None of these caveats touch the parts that are proven.
