# Tropical corpus — verification results

Status of the `examples/tropical/` corpus under **Isabelle2025-2**. Two layers
(SPEC §2, §8): the cheap structural skeleton (`i-orca verify`, no Isabelle) and the
real kernel check (`isabelle build`).

## Commands

```bash
# Layer 1 — structural skeleton (zero Isabelle)
i-orca verify examples/tropical/tropical.i.orca.md
#   -> all 18 theorems VALID, formal_fraction_static = 1.000, 0 frontier holes

# Layer 2 — kernel check of the substrate (the load-bearing math)
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/tropical \
  -o quick_and_dirty Tropical
#   -> Finished Tropical, exit 0, zero sorry

# Layer 2 — kernel check of the SURFACE (compile, add to ROOT, build in-session)
i-orca compile examples/tropical/tropical.i.orca.md --target isar \
  --document --theory TropicalSurface --out examples/tropical/TropicalSurface.thy
#   append "TropicalSurface" to ROOT, rebuild  -> exit 0
#   (TropicalSurface.thy is a regenerable artifact; not committed)
```

## Outcome

| Layer | Tool | Result |
|-------|------|--------|
| Skeleton | `i-orca verify` | 18/18 VALID, `formal_fraction_static = 1.000` |
| Substrate | `isabelle build` (`Tropical` session) | exit 0, **zero `sorry`** |
| Surface | `isabelle build` (compiled `TropicalSurface` in-session) | exit 0 — every `(rule …)` non-vacuous |

No `sorry`, `oops`, or `sledgehammer` placeholders remain in the substrate — every step
is a concrete method the kernel accepts.

## Theorems (surface → kernel-checked substrate lemma)

**Max-plus semiring** (`TropicalSemiring.thy`)
- `TropicalDistributivity` → `tmul_tadd_distrib_left`
- `TropicalAdditionIdempotent` → `tadd_idem`
- `TropicalMultiplicativeIdentity` → `tmul_left_id`

**Tropical polynomials are convex** (`TropicalPoly.thy`)
- `TropicalMonomialConvex` → `convex_on_affine`
- `MaxOfConvexIsConvex` → `convex_on_max`
- `TropicalPolynomialConvex` → `troppoly_convex`
- `TropicalPolynomialScaleClosed` → `troppoly_scale_nonneg`

**ReLU networks are tropical rational** (`ReLUNet.thy`, Thm 5.4 core)
- `AffineIsTropicalRational` → `troprat_affine`
- `ReluOfAffineIsTropicalRational` → `troprat_relu_affine`
- `TropicalRationalClosedUnderSum` → `troprat_add`
- `TropicalRationalClosedUnderReLU` → `troprat_relu`
- `OneHiddenLayerIsTropicalRational` → `troprat_one_hidden_layer`
- `TropicalRationalIsContinuous` → `troprat_continuous`

**Max-plus residuation** (`MaxPlus.thy`, Maragos et al.)
- `MaxPlusResiduationFeasible` → `mpres_feasible`
- `MaxPlusResiduationGreatest` → `mpres_greatest'`

**Polytope propagation** (`Newton.thy`, Pachter–Sturmfels / Cor 3.4)
- `TropicalProductIsPointwiseSum` → `tpoly_tprod`
- `MonomialCountSubmultiplicative` → `tprod_card_le`
- `NewtonSupportIsMinkowskiSum` → `tprod_slope_sumset`

## Notes

- The substrate uses `'a::real_inner` for the convexity / tropical-polynomial /
  tropical-rational results (so they hold in any real inner-product space, not just
  `ℝ`); the semiring, residuation, and Newton-polytope results are stated on `ℝ` and
  one-variable monomials respectively.
- All eighteen surface goals are pinned to a concrete type by a typed constant
  (`tadd`/`tmul`, `convex_on`/`inner`, `troppoly`/`troprat`/`relu`, `mpmul`/`mpres`,
  `tpoly`/`tprod`), so — unlike two goals in the `watermark` corpus — none needs an
  explicit `::real` annotation for `(rule …)` to unify.
- The standalone `i-orca check` cannot load this project-local session (it builds each
  theorem under a plain HOL parent), so the surface is kernel-checked via
  `isabelle build` rather than the batch backend — an import-resolution limit, not a
  math failure (same as the `watermark` / `provenance` / `complexity` corpora).
- Scope and the formal-vs-meta split (scalar/closure form of Thm 5.4; one-variable
  Newton polytopes; the multivariate region bound of Thm 6.3 and Prop 6.1 left open)
  are recorded in [`PROPOSAL.md`](PROPOSAL.md).
```
