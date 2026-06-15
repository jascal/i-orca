# Complexity of irreducibility (WIP)

Exploratory investigation on branch `complexity/irreducibility-hardness` — **how
hard is it to decide whether a composed token is irreducible?** Builds on the
kernel-checked characterisation in `../fieldrun/separation/` (`main`); does not
touch the fully-proven fieldrun corpus.

- [`PROPOSAL.md`](PROPOSAL.md) — design: the margin/cone formulation, the
  formal-vs-meta split, Route A (NP-hardness via PARTITION + anchor gadget),
  Route B (poly for bounded #competitors — likely the real answer), milestones.
- [`Hardness.thy`](Hardness.thy) — Isabelle, kernel-checked: `decides_via_margin`
  (the margin reformulation) and `single_competitor_reducible` /
  `irreducible_needs_two_competitors` (Route B base case: **irreducibility needs
  ≥ 2 competitors**). Route A/B gadgets are documented targets.
- [`Hardness_RouteB.thy`](Hardness_RouteB.thy) — Route B, K = 2, kernel-checked:
  `pp_nonempty_reducible` / `mm_nonempty_reducible` settle the both-positive and
  both-negative sign classes (a one-pass test); the residual pm/mp-only case is
  the genuine pseudo-poly core (where the irreducible witnesses live).
- [`hardness.i.orca.md`](hardness.i.orca.md) — a concrete i-orca witness of the
  single-competitor base case (verifies + kernel-checks).

Build the Isabelle development:

```bash
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/complexity -o quick_and_dirty Hardness
```

This branch is expected to carry WIP / open targets; the clean zero-`sorry`
corpus lives on `main`.
