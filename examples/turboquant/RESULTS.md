# TurboQuant corpus — verification results

Status of the `examples/turboquant/` corpus under **Isabelle2025-2**. Two layers
(SPEC §2, §8): the cheap structural skeleton (`i-orca verify`, no Isabelle) and the real
kernel check (`isabelle build`).

## Commands

```bash
# Layer 1 — structural skeleton (zero Isabelle)
i-orca verify examples/turboquant/turboquant.i.orca.md
#   -> all 11 theorems VALID, formal_fraction_static = 1.000, 0 frontier holes

# Layer 2 — kernel check of the substrate (the load-bearing math)
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/turboquant \
  -o quick_and_dirty TurboQuant
#   -> Finished TurboQuant, exit 0, zero sorry

# Layer 2 — kernel check of the SURFACE (compile, add to ROOT, build in-session)
i-orca compile examples/turboquant/turboquant.i.orca.md --target isar \
  --document --theory TurboQuantSurface --out examples/turboquant/TurboQuantSurface.thy
#   append "TurboQuantSurface" to ROOT, rebuild  -> exit 0
#   (TurboQuantSurface.thy is a regenerable artifact; not committed)
```

## Outcome

| Layer | Tool | Result |
|-------|------|--------|
| Skeleton | `i-orca verify` | 11/11 VALID, `formal_fraction_static = 1.000` |
| Substrate | `isabelle build` (`TurboQuant` session) | exit 0, **zero `sorry`** |
| Surface | `isabelle build` (compiled `TurboQuantSurface` in-session) | exit 0 — every `(rule …)` non-vacuous |

No `sorry`, `oops`, or `sledgehammer` placeholders remain in the substrate — every step is
a concrete method the kernel accepts.

## Theorems (surface → kernel-checked substrate lemma)

**Near-optimality** (`DistortionRate.thy`)
- `MSEApproximationRatio` → `mse_ratio_const`
- `MSERatioIsConstant` → `mse_ratio_eq` (`mse_ub/mse_lb = √3π/2`)
- `ProdApproximationRatio` → `prod_ratio_const`
- `NearOptimalConstant` → `mse_const_approx` (`2.7 < √3π/2 < 2.73`)
- `MSEAboveLowerBound` → `mse_achievable`

**Geometric rate** (`DistortionRate.thy`)
- `MSEGeometricDecay` → `mse_decay`
- `ProdGeometricDecay` → `prod_decay`

**High-dimensional advantage** (`DistortionRate.thy`)
- `ProdDimensionDecay` → `prod_dim_decay`

**Unbiased inner product** (`Unbiased.thy`)
- `ExpectationLinearOverSum` → `expectation_sum'`
- `InnerProductUnbiased` → `inner_product_unbiased'`

**Worked example** (`Examples.thy`)
- `FourBitDistortion` → `example_four_bit_distortion` (`mse_ub 4 < 0.011`)

## Notes

- The four distortion bounds are modelled as functions `mse_ub`, `mse_lb`, `prod_ub`,
  `prod_lb`; the theorems are the exact rate algebra they satisfy. The achievability and
  the Shannon + Yao lower bound are meta (see [`PROPOSAL.md`](PROPOSAL.md)).
- `NearOptimalConstant` is a genuine numeric bound: `√3` is bracketed in `(1.7320, 1.7321)`
  via `real_less_rsqrt` / `real_sqrt_less_mono`, and `π` via `pi_approx`
  (`3.141592653588 ≤ π ≤ 3.1415926535899` from `HOL-Analysis`), giving
  `2.7 < √3π/2 < 2.73`. This `pi_approx` is the only reason the session parents on
  `HOL-Analysis` rather than plain `HOL`.
- Linearity of the expectation is bundled into a `lin_exp` predicate; the per-coordinate
  unbiasedness hypothesis is surfaced via the primed `inner_product_unbiased'` /
  `expectation_sum'` so the i-orca goals match with `(rule …)` without meta-`⋀` premises
  (same pattern as the `jl` corpus).
- All eleven goals are pinned to a concrete type by a real-typed constant (`mse_ub`,
  `prod_ub`, `lin_exp`, `sqrt`, `pi`), so — unlike one goal in the `jl` corpus — none needs
  an explicit `::real` annotation.
- The standalone `i-orca check` cannot load this project-local session (it builds each
  theorem under a plain HOL parent), so the surface is kernel-checked via `isabelle build`
  rather than the batch backend — an import-resolution limit, not a math failure.
