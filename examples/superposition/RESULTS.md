# Superposition corpus — verification results

Status of the `examples/superposition/` corpus under **Isabelle2025-2**. Two layers
(SPEC §2, §8): the cheap structural skeleton (`i-orca verify`, no Isabelle) and the
real kernel check (`isabelle build`).

## Commands

```bash
# Layer 1 — structural skeleton (zero Isabelle)
i-orca verify examples/superposition/superposition.i.orca.md
#   -> all 13 theorems VALID, formal_fraction_static = 1.000, 0 frontier holes

# Layer 2 — kernel check of the substrate (the load-bearing math)
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/superposition \
  -o quick_and_dirty Superposition
#   -> Finished Superposition, exit 0, zero sorry

# Layer 2 — kernel check of the SURFACE (compile, add to ROOT, build in-session)
i-orca compile examples/superposition/superposition.i.orca.md --target isar \
  --document --theory SuperpositionSurface --out examples/superposition/SuperpositionSurface.thy
#   append "SuperpositionSurface" to ROOT, rebuild  -> exit 0
#   (SuperpositionSurface.thy is a regenerable artifact; not committed)
```

## Outcome

| Layer | Tool | Result |
|-------|------|--------|
| Skeleton | `i-orca verify` | 13/13 VALID, `formal_fraction_static = 1.000` |
| Substrate | `isabelle build` (`Superposition` session) | exit 0, **zero `sorry`** |
| Surface | `isabelle build` (compiled `SuperpositionSurface` in-session) | exit 0 — every `(rule …)` non-vacuous |

No `sorry`, `oops`, or `sledgehammer` placeholders remain in the substrate — every step
is a concrete method the kernel accepts.

## Theorems (surface → kernel-checked substrate lemma)

**Interference = reconstruction loss** (`Superposition.thy`)
- `InnerProductSymmetric` → `ip_commute`
- `ReconstructionErrorIsInterference` → `recon_error_eq_interference`
- `OrthogonalPerfectRecovery` → `orthogonal_perfect_recovery'`

**The Welch bound** (`Welch.thy`)
- `WelchSumOfSquares` → `welch_sos` (proved from scratch, no matrix library)
- `OrthogonalCapacity` → `orth_capacity'`
- `SuperpositionForcesInterference` → `superposition_forces_interference'`
- `WelchBound` → `welch_offdiag'`

**Routing-side Welch** (`RoutingWelch.thy`, a *PIL* contribution — the third leg of the two-sided packing story)

The `n` realized **routing features** of a rule bank (`f_c = E[h|A] − E[h|B]`, the per-decision direction in
rule-activation space `ℝ^M`) are `n` vectors in `m = M` rule-coordinates, so the proved Welch machinery applies
verbatim — the generator-side dual of `tropical/DecodeCapacity`'s frame packing and the quantitative form of
`tropical/RoutingRank`'s "superposition forced when `n > M`":

- `RoutingCapacity` → `routing_capacity` (cross-talk-free routing needs `M ≥ n` rules)
- `RoutingForcesInterference` → `routing_forces_interference` (`n > M` ⟹ some routing pair interferes)
- `RoutingInterferenceWelch` → `routing_interference_welch` (total routing interference `≥ n(n−M)/M`)

Honestly scoped to the count/interference statement; the further "coherence degrades the decode margin" step is
empirically **mild** (trained rules pack near the Welch floor with margins still healthy — PIL
`docs/notes/pil_learning_dynamics.md` §5f), so it is the measured consequence, not a kernel claim.

**Worked example** (`Examples.thy`, the antipodal pair)
- `AntipodalInterference` → `antipodal_interference`
- `AntipodalIsSuperposition` → `antipodal_is_superposition`
- `AntipodalAchievesWelch` → `antipodal_achieves_welch`

## Notes

- Vectors are modelled as functions over a finite coordinate set `K` (the embedding
  dimension is `m = card K`); the inner product is `ip K x y = Σ_{k∈K} x k * y k`. This
  keeps the whole development — including the Welch bound — elementary, with no matrix,
  eigenvalue, or inner-product-space library.
- The Welch sum-of-squares proof needs `sum_squared_le_sum_of_squares` from
  `HOL-Analysis.Convex`; that is the only non-`Main` dependency.
- The antipodal pair (`AntipodalAchievesWelch`) is the **optimal** packing of two
  features into one dimension: both the realised off-diagonal interference and the Welch
  lower bound `n(n−m)/m` equal `2` (at `n = 2`, `m = 1`), so the bound is saturated.
- The four corollaries with per-feature hypotheses are surfaced via primed variants
  (`orthogonal_perfect_recovery'`, `orth_capacity'`,
  `superposition_forces_interference'`, `welch_offdiag'`) that state the unit-norm /
  orthogonality premises as bounded quantifiers, so the i-orca goal matches with
  `(rule …)` without a meta-`⋀` premise.
- The standalone `i-orca check` cannot load this project-local session (it builds each
  theorem under a plain HOL parent), so the surface is kernel-checked via
  `isabelle build` rather than the batch backend — an import-resolution limit, not a
  math failure (same as the other corpora).
- Scope and the formal-vs-meta split (linear reconstruction model; phase transitions and
  specific geometries left open) are recorded in [`PROPOSAL.md`](PROPOSAL.md).
