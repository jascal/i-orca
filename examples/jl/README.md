# Johnson–Lindenstrauss — i-orca corpus

A kernel-checked formalisation of the structural pillars of the **Johnson–Lindenstrauss
random-projection lemma** (Johnson & Lindenstrauss, 1984) — the fourth entry in i-orca's
**"canonical proofs from other authors"** track (after `watermark`, `tropical`,
`superposition`).

> ⚠️ As everywhere in i-orca, a green `i-orca verify` certifies only that the proof
> *skeleton* is well-formed. Truth is the kernel's: every theorem here is discharged by
> `(rule <lemma>)` against a hand-authored Isabelle lemma, and the whole `JL` session
> builds under Isabelle2025-2 with **zero `sorry`**.

## The idea in one line

`n` points embed into `k = O(log n / ε²)` dimensions preserving all pairwise distances:
a random projection preserves norms **in expectation**, **concentrates** around it, and a
**union bound + probabilistic method** over the `C(n,2)` pairs shows a single good
projection exists. See [`PROPOSAL.md`](PROPOSAL.md).

## Layout

| File | Role |
|------|------|
| [`JLProjection.thy`](JLProjection.thy) | the expectation pillar: a linear `E` commutes with finite sums, and `E[(∑ⱼ xⱼ gⱼ)²] = ∑ⱼ xⱼ²` (norm preserved in expectation) |
| [`JLDimension.thy`](JLDimension.thy) | the dimension pillar: `k > ln N / c ⟹ N·exp(−c k) < 1`, and the `O(log n/ε²)` bound |
| [`JLExistence.thy`](JLExistence.thy) | the existence pillar: the probabilistic method, and the assembled "a distance-preserving projection exists" |
| [`Examples.thy`](Examples.thy) | a concrete instance: four projections, two constraints, a good projection exists (the union bound in miniature) |
| [`ROOT`](ROOT) | Isabelle session `JL` (parent `HOL`) |
| [`jl.i.orca.md`](jl.i.orca.md) | the i-orca surface: 7 theorems, each `(rule <lemma>)` |
| [`PROPOSAL.md`](PROPOSAL.md) | the source, the formal-vs-meta table, honest reckonings, open targets |
| [`RESULTS.md`](RESULTS.md) | verification status and commands |

## Verify

```bash
# Layer 1 — structural skeleton (zero Isabelle)
i-orca verify examples/jl/jl.i.orca.md
#   -> all 7 theorems VALID, formal_fraction_static = 1.000

# Layer 2 — kernel check of the substrate (the load-bearing math)
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/jl -o quick_and_dirty JL
#   -> Finished JL, exit 0, zero sorry
```

To also kernel-check the **surface**, compile it into the session and rebuild:

```bash
i-orca compile examples/jl/jl.i.orca.md --target isar \
  --document --theory JLSurface --out examples/jl/JLSurface.thy
# append "JLSurface" to ROOT, rebuild -> exit 0 (every (rule ...) non-vacuous)
# JLSurface.thy is a regenerable artifact; not committed.
```

The standalone `i-orca check` builds each theorem under a plain HOL parent and cannot
load this project-local session — an import-resolution limit, not a math failure (same
caveat as the other corpora).

## What it proves (and what it doesn't)

Seven kernel-checked cores: the unbiased random projection (norm preserved in expectation),
the `O(log n/ε²)` dimension arithmetic, and the probabilistic-method existence assembly —
see the table in [`PROPOSAL.md`](PROPOSAL.md). The theorems are honest about scope: the
expectation is modelled abstractly (no Gaussian measure), the probabilistic method is the
finite-counting form, and the **per-pair concentration bound is a hypothesis** — the
chi-squared tail that is the genuine probabilistic content of J-L is the meta input,
flagged as the open target. Everything structural around it is kernel-checked.
