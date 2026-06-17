# Tropical geometry of deep neural networks — proposal

The second entry in i-orca's **"canonical proofs from other authors"** track (after
[`../watermark`](../watermark), Aaronson's LLM watermark): a kernel-checked
formalisation of the mathematical core of the **tropical-geometry view of ReLU
networks**.

**Primary source.** Zhang, Naitzat & Lim, *"Tropical Geometry of Deep Neural
Networks"*, Proc. ICML 2018, PMLR 80:5824–5832 — especially **Theorem 5.4** (a
feedforward ReLU network *is* a tropical rational map), **Def 2.4** (tropical rational
function), and the **Newton-polytope** region machinery (**Def 3.2 / Cor 3.4**).

**Surrounding literature.**
- Pachter & Sturmfels, *"Tropical Geometry of Statistical Models"*, PNAS
  101(46):16132–16137, 2004 — graphical models as algebraic varieties; **polytope
  propagation = geometric sum-product**.
- Maragos, Charisopoulos & Theodosis, *"Tropical Geometry and Machine Learning"*,
  Proc. IEEE 109(5):728–755, 2021 (+ Maragos ICASSP 2024 tutorial) — morphological /
  max-plus networks, **max-plus residuation**, Newton-polytope/zonotope pruning.

## The idea

The **tropical (max-plus) semiring** is `(ℝ ∪ {−∞}, ⊕, ⊙)` with `a ⊕ b = max a b` and
`a ⊙ b = a + b`. A **tropical monomial** is an affine function `⟨a,x⟩ + c`; a **tropical
polynomial** is a tropical sum (pointwise max) of monomials, i.e. a convex
piecewise-linear function; a **tropical rational function** `f ⊘ g = f − g` is a
difference of two tropical polynomials, i.e. a general continuous piecewise-linear
function. Because `ReLU(t) = max(t, 0) = t ⊕ 0` and an affine layer is a tropical
monomial, a ReLU network is built entirely from tropical operations — and the algebra
explains its **linear regions** through the Newton polytopes of the underlying tropical
polynomials.

## What is formalised (and the formal-vs-meta split)

The Isabelle theorems are **honest, narrow, kernel-checked cores** — the algebra and
the analytic facts that carry the theory, not the full multivariate region-counting
geometry. Six theories, twenty surfaced theorems:

| # | i-orca theorem | Isabelle lemma | Proves (formal) | Supports (meta) |
|---|----------------|----------------|------------------|------------------|
| 1 | TropicalDistributivity | `tmul_tadd_distrib_left` | `a + max b c = max (a+c) (b+c)` | the semiring law that makes ReLU nets tropical |
| 2 | TropicalAdditionIdempotent | `tadd_idem` | `max a a = a` | `⊕` is a semilattice (no additive inverse) |
| 3 | TropicalMultiplicativeIdentity | `tmul_left_id` | `0 + a = a` | `0` is the `⊙`-identity |
| 4 | TropicalMonomialConvex | `convex_on_affine` | an affine function is convex | tropical monomials are convex |
| 5 | MaxOfConvexIsConvex | `convex_on_max` | max of two convex is convex | `⊕` preserves convexity (not in the library) |
| 6 | TropicalPolynomialConvex | `troppoly_convex` | every tropical polynomial is convex | tropical polys = convex PL functions |
| 7 | TropicalPolynomialScaleClosed | `troppoly_scale_nonneg` | non-neg scaling stays a tropical poly | closure of the monomial class |
| 8 | AffineIsTropicalRational | `troprat_affine` | an affine map is tropical rational | a linear layer is tropical |
| 9 | ReluOfAffineIsTropicalRational | `troprat_relu_affine` | `relu(⟨a,x⟩+c)` is tropical rational | a single neuron is tropical |
| 10 | TropicalRationalClosedUnderSum | `troprat_add` | the class is closed under `+` | nets can add neuron outputs |
| 11 | TropicalRationalClosedUnderReLU | `troprat_relu` | `relu(g−h) = max g h − h` | the inductive step of Thm 5.4 |
| 12 | OneHiddenLayerIsTropicalRational | `troprat_one_hidden_layer` | a 1-hidden-layer scalar ReLU net is tropical rational | **Theorem 5.4, worked instance** |
| 13 | TropicalRationalIsContinuous | `troprat_continuous` | tropical rationals are continuous | = continuous PL functions |
| 14 | MaxPlusResiduationFeasible | `mpres_feasible` | `A ⊙ x̂ ≤ b` for `x̂ⱼ = minᵢ(bᵢ−Aᵢⱼ)` | greatest subsolution exists |
| 15 | MaxPlusResiduationGreatest | `mpres_greatest'` | every subsolution `≤ x̂` | the max-plus Galois connection |
| 16 | TropicalProductIsPointwiseSum | `tpoly_tprod` | `tpoly(P⊗Q) = tpoly P + tpoly Q` | **polytope propagation** (Pachter–Sturmfels) |
| 17 | MonomialCountSubmultiplicative | `tprod_card_le` | `card(P⊗Q) ≤ card P · card Q` | the region-count mechanism (Cor 3.4) |
| 18 | NewtonSupportIsMinkowskiSum | `tprod_slope_sumset` | slope support of a product is the sumset | Newton polytope = Minkowski sum |
| 19 | AbsValueNetworkComputesAbs | `relu_plus_relu_neg` | `relu x + relu(−x) = ¦x¦` | a concrete 2-neuron net computes `¦x¦` |
| 20 | AbsValueNetworkIsTropicalRational | `abs_network_troprat` | that network is tropical rational | **Thm 5.4 in miniature** — `¦x¦ = max x (−x)` |

The **meta** column is deliberately not claimed as proven. E.g. theorem 12 proves that
*one concrete* one-hidden-layer scalar network is a tropical rational function (from the
closure results), not the full multivariate, multilayer, vector-output equivalence of
Theorem 5.4.

## Honest reckonings

- **Theorem 5.4 — scalar / closure form (thm 8–12).** We formalise the
  representational *direction* through the closed class `troprat` (differences of
  tropical polynomials): affine maps and ReLU-of-affine are in it, and it is closed
  under `+`, real scaling, finite sums, and ReLU post-composition — so every scalar
  function a ReLU network computes is tropical rational, witnessed concretely by the
  one-hidden-layer theorem. The full statement (an `n→m` network as a tropical rational
  *map*, both directions, with the explicit max-plus matrix form per layer) is the
  stated lift, not done here.
- **Polynomials in one variable (Newton.thy, thm 16–18).** The Newton-polytope results
  are proved for one-variable tropical polynomials (monomials = `(slope, intercept)`
  pairs), where the Newton polytope is a segment and the Minkowski sum is the slope
  sumset. The multivariate Newton polytope (a genuine polytope in slope space) and the
  exact **linear-region upper bound** of Thm 6.3 are the open targets — the
  combinatorics there (dual subdivisions, zonotope vertex counts) is the heavy lift.
- **Decision boundary = tropical hypersurface (Prop 6.1)** is not attempted; it needs
  a development of tropical hypersurfaces.
- **Convexity is genuine and general.** `convex_on_affine`, `convex_on_max`, and
  `troppoly_convex` are proved for any real inner-product space, not just `ℝ` — so
  "tropical polynomials are convex" holds in the multivariate setting.

## Milestones / open targets

1. **(done)** The twenty-theorem development above — all kernel-checked under
   Isabelle2025-2 (`isabelle build -D examples/tropical Tropical`, exit 0, zero
   `sorry`), including the concrete worked example `Examples.thy` (a two-neuron ReLU
   net computing `¦x¦`, rendered as the tropical polynomial `max x (−x)`). See
   [`RESULTS.md`](RESULTS.md).
2. The full multivariate / multilayer Theorem 5.4: a network `ℝⁿ → ℝᵐ` as a tropical
   rational map, via an explicit per-layer max-plus matrix form.
3. Multivariate Newton polytopes and the linear-region upper bound of Theorem 6.3
   (zonotope vertex counts).
4. Tropical hypersurfaces and Prop 6.1 (decision boundary = tropical hypersurface).
5. Connect the max-plus layer (`MaxPlus.mpmul`) to `ReLUNet`, so a morphological /
   max-plus network and its tropical-rational form are the same object.
