# Johnson–Lindenstrauss corpus — verification results

Status of the `examples/jl/` corpus under **Isabelle2025-2**. Two layers (SPEC §2, §8):
the cheap structural skeleton (`i-orca verify`, no Isabelle) and the real kernel check
(`isabelle build`).

## Commands

```bash
# Layer 1 — structural skeleton (zero Isabelle)
i-orca verify examples/jl/jl.i.orca.md
#   -> all 6 theorems VALID, formal_fraction_static = 1.000, 0 frontier holes

# Layer 2 — kernel check of the substrate (the load-bearing math)
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/jl -o quick_and_dirty JL
#   -> Finished JL, exit 0, zero sorry

# Layer 2 — kernel check of the SURFACE (compile, add to ROOT, build in-session)
i-orca compile examples/jl/jl.i.orca.md --target isar \
  --document --theory JLSurface --out examples/jl/JLSurface.thy
#   append "JLSurface" to ROOT, rebuild  -> exit 0
#   (JLSurface.thy is a regenerable artifact; not committed)
```

## Outcome

| Layer | Tool | Result |
|-------|------|--------|
| Skeleton | `i-orca verify` | 6/6 VALID, `formal_fraction_static = 1.000` |
| Substrate | `isabelle build` (`JL` session) | exit 0, **zero `sorry`** |
| Surface | `isabelle build` (compiled `JLSurface` in-session) | exit 0 — every `(rule …)` non-vacuous |

No `sorry`, `oops`, or `sledgehammer` placeholders remain in the substrate — every step
is a concrete method the kernel accepts. The corpus needs no `HOL-Analysis` (the session
parent is plain `HOL`; everything is in `Complex_Main`).

## Theorems (surface → kernel-checked substrate lemma)

**Expectation pillar** (`JLProjection.thy`)
- `ExpectationLinearOverSum` → `expectation_sum'`
- `ProjectionUnbiased` → `projection_unbiased'` (`E[(∑ⱼ xⱼ gⱼ)²] = ∑ⱼ xⱼ²`)

**Dimension pillar** (`JLDimension.thy`)
- `DimensionUnionBound` → `jl_dimension` (`k > ln N/c ⟹ N·exp(−c k) < 1`)
- `LogarithmicDimension` → `jl_log_dimension` (`k > 16 ln n/ε²` ⟹ union bound `< 1`)

**Existence pillar** (`JLExistence.thy`)
- `ProbabilisticMethod` → `probabilistic_method'`
- `GoodProjectionExists` → `jl_good_projection_exists'`

## Notes

- Linearity of the expectation functional is bundled into a `lin_exp` predicate, and the
  per-feature/per-pair hypotheses are surfaced via primed variants (`expectation_sum'`,
  `projection_unbiased'`, `probabilistic_method'`, `jl_good_projection_exists'`) stating
  them as bounded quantifiers / a predicate, so the i-orca goals match with `(rule …)`
  without meta-`⋀` premises.
- `DimensionUnionBound` carries an explicit `(1::real)` annotation: its goal uses only
  `ln`/`exp`/arithmetic with no real-typed constant to pin the type, so without it the
  goal variables stay at an abstract sort and `(rule jl_dimension)` will not unify (same
  gotcha as two goals in the `watermark` corpus). The other five goals are pinned to a
  concrete type by `real (...)`, `lin_exp`, `card`, etc.
- The standalone `i-orca check` cannot load this project-local session (it builds each
  theorem under a plain HOL parent), so the surface is kernel-checked via `isabelle build`
  rather than the batch backend — an import-resolution limit, not a math failure.
- Scope and the formal-vs-meta split (Gaussian concentration is the meta input; the
  expectation is modelled abstractly; the probabilistic method is the finite-counting
  form) are recorded in [`PROPOSAL.md`](PROPOSAL.md).
```
