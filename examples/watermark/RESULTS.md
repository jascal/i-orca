# Watermark corpus — verification results

Status of the `examples/watermark/` corpus under **Isabelle2025-2**. Two layers
(SPEC §2, §8): the cheap structural skeleton (`i-orca verify`, no Isabelle) and the
real kernel check (`isabelle build`).

## Commands

```bash
# Layer 1 — structural skeleton (zero Isabelle)
i-orca verify examples/watermark/watermark.i.orca.md
#   -> all 12 theorems VALID, formal_fraction_static = 1.000, 0 frontier holes

# Layer 2 — kernel check of the substrate (the load-bearing math)
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/watermark \
  -o quick_and_dirty Watermark
#   -> Finished Watermark, exit 0, zero sorry

# Layer 2 — kernel check of the SURFACE (compile, add to ROOT, build in-session)
i-orca compile examples/watermark/watermark.i.orca.md --target isar \
  --document --theory WatermarkSurface --out examples/watermark/WatermarkSurface.thy
#   append "WatermarkSurface" to ROOT, rebuild  -> exit 0
#   (WatermarkSurface.thy is a regenerable artifact; not committed)
```

## Outcome

| Layer | Tool | Result |
|-------|------|--------|
| Skeleton | `i-orca verify` | 12/12 VALID, `formal_fraction_static = 1.000` |
| Substrate | `isabelle build` (`Watermark` session) | exit 0, **zero `sorry`** |
| Surface | `isabelle build` (compiled `WatermarkSurface` in-session) | exit 0 — every `(rule …)` non-vacuous |

No `sorry`, `oops`, or `sledgehammer` placeholders remain in the substrate — every step
is a concrete method the kernel accepts.

## Theorems (surface → kernel-checked substrate lemma)

**Selection rule** (`GumbelSelect.thy`)
- `GumbelMaxLogEquivalence` → `gumbel_mono`
- `SelectionEqualsExponentialRace` → `selects_iff_erace`
- `SelectionDeterministic` → `selects_unique`
- `SelectionPushforwardCDF` → `gscore_le_iff`

**Distortion-free / unbiased** (`Unbiased.thy`)
- `ConditionalWinCollapse` → `cwin_collapse`
- `DistortionFreeSampling` → `win_prob_integral` (`∫₀¹ u^((1−p)/p) du = p`)
- `FullSupportPreserved` → `cwin_pos`

**Detectability** (`Detect.thy`)
- `NullScoreIsExponential` → `wscore_cdf` (null score is `Exp(1)`)
- `ScoreIncreasingInPRF` → `wscore_mono`
- `ChosenValueStochasticallyLarger` → `chosen_r_dominates`
- `ChosenValueIsProperDensity` → `dwin_integral_one`
- `ChosenValueMeanBias` → `chosen_r_mean` (`E[r_chosen] = 1/(1+p)`)

## Notes

- Two surface goals (`DistortionFreeSampling`, `ChosenValueStochasticallyLarger`) carry
  an explicit `::real` annotation. They use only `powr`/arithmetic with no real-typed
  constant to pin the type, so without the annotation the goal variables stay at an
  abstract sort and `(rule …)` will not unify with the `real`-fixed lemma. The other ten
  goals are pinned to `real` by a real-typed constant (`gscore`, `cwin`, `wscore`,
  `dwin`) and need no annotation.
- The standalone `i-orca check` cannot load this project-local session (it builds each
  theorem under a plain HOL parent), so the surface is kernel-checked via
  `isabelle build` rather than the batch backend — an import-resolution limit, not a
  math failure (same as the `provenance` and `complexity` corpora).
- Scope and the formal-vs-meta split (independence modelled algebraically; the
  product-measure/Fubini lift and the `T`-token concentration bound left to
  `HOL-Probability`) are recorded in [`PROPOSAL.md`](PROPOSAL.md).
