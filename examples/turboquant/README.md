# TurboQuant — i-orca corpus

A kernel-checked formalisation of the distortion-rate structure of **TurboQuant** (Zandieh,
Daliri, Hadian & Mirrokni, Google / NYU, arXiv:2504.19874, 2025) — the fifth entry in
i-orca's **"canonical proofs from other authors"** track (after `watermark`, `tropical`,
`superposition`, `jl`).

> ⚠️ As everywhere in i-orca, a green `i-orca verify` certifies only that the proof
> *skeleton* is well-formed. Truth is the kernel's: every theorem here is discharged by
> `(rule <lemma>)` against a hand-authored Isabelle lemma, and the whole `TurboQuant`
> session builds under Isabelle2025-2 with **zero `sorry`**.

## The idea in one line

A vector quantizer that hits distortion `D ≤ (√3π/2)·(1/4ᵇ)` per `b` bits — within a
constant `≈ 2.7` of the information-theoretic floor `1/4ᵇ`, *for every bit-width and
dimension* — and estimates inner products **unbiasedly**. See [`PROPOSAL.md`](PROPOSAL.md).

## Layout

| File | Role |
|------|------|
| [`DistortionRate.thy`](DistortionRate.thy) | the MSE / inner-product upper & lower bounds as functions; the near-optimality ratio is a constant (`√3π/2`, `√3π²`), the rate is geometric (`1/4ᵇ`), the constant is `≈ 2.7`, the bounds are consistent, and the inner-product bound decays in dimension |
| [`Unbiased.thy`](Unbiased.thy) | the inner-product unbiasedness: a linear `E` commutes with sums, so coordinatewise unbiasedness gives `E[⟨y, dq⟩] = ⟨y, x⟩` |
| [`Examples.thy`](Examples.thy) | a concrete operating point: the 4-bit MSE distortion bound is below `0.011` |
| [`ROOT`](ROOT) | Isabelle session `TurboQuant` (parent `HOL-Analysis`) |
| [`turboquant.i.orca.md`](turboquant.i.orca.md) | the i-orca surface: 11 theorems, each `(rule <lemma>)` |
| [`PROPOSAL.md`](PROPOSAL.md) | the source, the formal-vs-meta table, honest reckonings, open targets |
| [`RESULTS.md`](RESULTS.md) | verification status and commands |

## Verify

```bash
# Layer 1 — structural skeleton (zero Isabelle)
i-orca verify examples/turboquant/turboquant.i.orca.md
#   -> all 11 theorems VALID, formal_fraction_static = 1.000

# Layer 2 — kernel check of the substrate (the load-bearing math)
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/turboquant \
  -o quick_and_dirty TurboQuant
#   -> Finished TurboQuant, exit 0, zero sorry
```

To also kernel-check the **surface**, compile it into the session and rebuild:

```bash
i-orca compile examples/turboquant/turboquant.i.orca.md --target isar \
  --document --theory TurboQuantSurface --out examples/turboquant/TurboQuantSurface.thy
# append "TurboQuantSurface" to ROOT, rebuild -> exit 0 (every (rule ...) non-vacuous)
# TurboQuantSurface.thy is a regenerable artifact; not committed.
```

The standalone `i-orca check` builds each theorem under a plain HOL parent and cannot load
this project-local session — an import-resolution limit, not a math failure (same caveat as
the other corpora).

## What it proves (and what it doesn't)

Eleven kernel-checked cores: the distortion-rate algebra (near-optimality ratio is a
constant; geometric `1/4ᵇ` rate; the `≈ 2.7` constant proved numerically; consistency;
high-dimensional decay) and the inner-product unbiasedness — see the table in
[`PROPOSAL.md`](PROPOSAL.md). The theorems are honest about scope: the MSE/inner-product
bounds are encoded as the functions whose rate structure is then proved; the
**achievability** of the upper bounds (random rotation, Beta concentration, Lloyd–Max
optimality) and the **Shannon + Yao lower bound** are the meta inputs, and the expectation
is modelled abstractly. None of those caveats touch the parts that are proven — including
the genuine numeric bound `2.7 < √3π/2 < 2.73`.
