# Provenance & influence attribution

A kernel-checked formalisation of a design-discussion thread on **what is provable
about per-token corpus provenance** in a density-min bucketed generation pipeline.
The short version:

> **Syntactic provenance** (which bucket/corpus label produced a token) is **exact
> — probability 1, zero entropy.** **Statistical generative influence** (which
> corpus *shaped the parameters* behind a token) is **fundamentally bounded** —
> except inside well-isolated, high-density buckets, where it collapses back to the
> exact syntactic answer.

Scope is **i-orca + fieldrun**: the bucketing premise is the companion to fieldrun's
activation/firing machinery ([`../complexity/Density.thy`](../complexity/Density.thy)),
and the corpus is a standalone classical-attribution development. See
[`PROPOSAL.md`](PROPOSAL.md) for the design, the formal-vs-meta split, the open
targets, and the note on why q-orca (floated in the original thread) is excluded.

## Files

- [`provenance.i.orca.md`](provenance.i.orca.md) — the i-orca surface: ten
  theorems, each STATED in the table DSL and discharged by `(rule <lemma>)` against
  a kernel-checked Isabelle lemma (same pattern as
  [`../complexity/complexity.i.orca.md`](../complexity/complexity.i.orca.md)).
  `i-orca verify` → all VALID, `formal_fraction_static = 1.000`.
- [`Provenance.thy`](Provenance.thy) — the syntactic-vs-statistical core.
  `synt_post` (the indicator posterior), `synt_post_sum_one` (valid distribution),
  `synt_entropy_zero` (**Problem 1 is exact: zero Shannon entropy**); `plogp`/
  `shannon` (bits); `mixed_entropy_pos` (**irreversible mixing ⇒ a 2-source split has
  strictly positive entropy** — irreducible uncertainty).
- [`CondNumber.thy`](CondNumber.thy) — the Hessian-conditioning limit. `kappa`,
  `condition_number_tight` (**worst-case influence-error amplification equals the
  condition number, exactly**), `kappa_ge_one` / `kappa_one` (κ ≥ 1, and κ = 1 in
  the perfectly-conditioned / isolated-bucket case).
- [`Attribution.thy`](Attribution.thy) — the synthesis. `candidates` /
  `consistent`; `provenance_support_bound` (**the data-processing support bound**:
  no influence mass off the used buckets — the discrete shadow of the MI bound);
  `isolated_attribution_exact` (**the payoff**: inside an isolated single-source
  response the statistical posterior IS the exact syntactic indicator).
- [`ReprProvenance.thy`](ReprProvenance.thy) — **scenario (ii)** (only the
  bucketing-pass data is known, not the model's training data — the realistic case).
  `faithful_posterior_agreement` (**recovery**: faithfulness ⇒ representational =
  generative provenance), `generative_underdetermined_off_used` (**the weakening**:
  off-coverage the generative label is provably ambiguous),
  `uncovered_forces_abstention` (**honesty**: uncovered buckets ⇒ abstain, never
  guess). See PROPOSAL.md "Two scenarios".
- [`ROOT`](ROOT) — the `Provenance` Isabelle session (parent `HOL`).

## Build (kernel check)

```bash
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/provenance \
  -o quick_and_dirty Provenance
```

All four theories build clean under **Isabelle2025-2** (exit 0, zero `sorry`).
Compiling the surface and building it in-session likewise kernel-checks every
theorem:

```bash
i-orca compile examples/provenance/provenance.i.orca.md --target isar \
  --document --theory ProvenanceSurface --out examples/provenance/ProvenanceSurface.thy
# add ProvenanceSurface to ROOT, then `isabelle build` as above  → exit 0
```

(As with the complexity corpus, the standalone `i-orca check` cannot load this
project-local session, so kernel-checking the surface goes through `isabelle build`,
not the batch backend — an import-resolution limit, not a math failure.)
