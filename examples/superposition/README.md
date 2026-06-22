# Toy Models of Superposition — i-orca corpus

A kernel-checked formalisation of the geometric core of Anthropic's **"Toy Models of
Superposition"** (Elhage et al., Transformer Circuits Thread, 2022) — the third entry in
i-orca's **"canonical proofs from other authors"** track (after
[`../watermark`](../watermark) and [`../tropical`](../tropical)).

> ⚠️ As everywhere in i-orca, a green `i-orca verify` certifies only that the proof
> *skeleton* is well-formed. Truth is the kernel's: every theorem here is discharged by
> `(rule <lemma>)` against a hand-authored Isabelle lemma, and the whole `Superposition`
> session builds under Isabelle2025-2 with **zero `sorry`**.

## The idea in one line

A model packs `n` features into `m < n` dimensions as the columns `W_i` of `W`; the
off-diagonal Gram entries `⟨W_i, W_j⟩` are **interference**, and the **Welch bound**
says you cannot make them all small — packing more features than dimensions has an
unavoidable, quantifiable cost. See [`PROPOSAL.md`](PROPOSAL.md).

## Layout

| File | Role |
|------|------|
| [`Superposition.thy`](Superposition.thy) | inner product over a coordinate set; reconstruction error of a unit feature `=` its total interference; orthogonal features reconstruct perfectly |
| [`Welch.thy`](Welch.thy) | the **Welch bound** `welch_sos` (proved from scratch), and its corollaries: orthogonal capacity `≤ m`, superposition forces interference, total interference `≥ n(n−m)/m` |
| [`RoutingWelch.thy`](RoutingWelch.thy) | a **PIL** contribution: the routing-side instance — `n` routing features in `M` rule-coordinates, so `n > M` forces Welch interference; the generator-side dual of `tropical/DecodeCapacity` |
| [`Examples.thy`](Examples.thy) | the antipodal pair — two features in one dimension — that achieves the Welch bound with equality |
| [`ROOT`](ROOT) | Isabelle session `Superposition` (parent `HOL-Analysis`) |
| [`superposition.i.orca.md`](superposition.i.orca.md) | the i-orca surface: 13 theorems, each `(rule <lemma>)` |
| [`PROPOSAL.md`](PROPOSAL.md) | the source, the formal-vs-meta table, honest reckonings, open targets |
| [`RESULTS.md`](RESULTS.md) | verification status and commands |

## Verify

```bash
# Layer 1 — structural skeleton (zero Isabelle)
i-orca verify examples/superposition/superposition.i.orca.md
#   -> all 13 theorems VALID, formal_fraction_static = 1.000

# Layer 2 — kernel check of the substrate (the load-bearing math)
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/superposition \
  -o quick_and_dirty Superposition
#   -> Finished Superposition, exit 0, zero sorry
```

To also kernel-check the **surface**, compile it into the session and rebuild:

```bash
i-orca compile examples/superposition/superposition.i.orca.md --target isar \
  --document --theory SuperpositionSurface --out examples/superposition/SuperpositionSurface.thy
# append "SuperpositionSurface" to ROOT, rebuild -> exit 0 (every (rule ...) non-vacuous)
# SuperpositionSurface.thy is a regenerable artifact; not committed.
```

The standalone `i-orca check` builds each theorem under a plain HOL parent and cannot
load this project-local session — an import-resolution limit, not a math failure (same
caveat as the `watermark` / `tropical` / `provenance` / `complexity` corpora).

## What it proves (and what it doesn't)

Ten kernel-checked cores: interference = reconstruction loss, orthogonal capacity, the
Welch bound (proved from scratch), the forcing of interference under overpacking, and a
concrete antipodal pair achieving the bound — see the table in
[`PROPOSAL.md`](PROPOSAL.md). The theorems are honest about scope: the reconstruction
model is linear (no ReLU/bias), and the paper's sparsity-driven phase transitions and
specific polytope geometries are flagged as open targets. None of those caveats touch
the parts that are proven.
