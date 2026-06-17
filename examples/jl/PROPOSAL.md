# Johnson–Lindenstrauss — proposal

The fourth entry in i-orca's **"canonical proofs from other authors"** track (after the
Aaronson watermark, the tropical geometry of ReLU networks, and Anthropic's Toy Models of
Superposition): a kernel-checked formalisation of the structural pillars of the
**Johnson–Lindenstrauss random-projection lemma**.

**Source.** W. B. Johnson & J. Lindenstrauss, *"Extensions of Lipschitz mappings into a
Hilbert space"*, Contemporary Mathematics **26** (1984) 189–206.

## The idea

The lemma: any `n` points in a high-dimensional Euclidean space can be embedded into
`k = O(log n / ε²)` dimensions so that **all pairwise distances are preserved up to a
factor `1 ± ε`**. The standard proof projects with a random matrix `R` (scaled by
`1/√k`) and rests on three pillars:

1. **Expectation** — the projection preserves each vector's squared length *on average*:
   `E[‖Rx‖²/k] = ‖x‖²` (a second-moment computation).
2. **Concentration** — `‖Rx‖²/k` concentrates around `‖x‖²`, so a single pair is
   distorted only with small probability `≈ exp(−c ε² k)` (a Gaussian / chi-squared tail).
3. **Union bound + probabilistic method** — there are only `C(n,2)` pairs; if each fails
   rarely and `k` is large enough that the total failure probability is `< 1`, then a
   single projection preserving *every* pair must exist.

`k = O(log n / ε²)` falls out of `C(n,2)·exp(−c ε² k) < 1`.

## What is formalised (and the formal-vs-meta split)

We kernel-check the **deterministic structural pillars (1 and 3) and the dimension
arithmetic**; the Gaussian **concentration (2)** is the honest meta input, supplied as a
hypothesis. Three theories, six surfaced theorems:

| # | i-orca theorem | Isabelle lemma | Proves (formal) | Supports (meta) |
|---|----------------|----------------|------------------|------------------|
| 1 | ExpectationLinearOverSum | `expectation_sum'` | a linear `E` commutes with finite sums | the workhorse for pillar 1 |
| 2 | ProjectionUnbiased | `projection_unbiased'` | `E[(∑ⱼ xⱼ gⱼ)²] = ∑ⱼ xⱼ²` for orthonormal coordinates | **pillar 1**: norm preserved in expectation |
| 3 | DimensionUnionBound | `jl_dimension` | `k > ln N / c ⟹ N·exp(−c k) < 1` | the union bound goes below 1 |
| 4 | LogarithmicDimension | `jl_log_dimension` | `k > 16 ln n / ε² ⟹ n²·exp(−(ε²/8)k) < 1` | **the `O(log n/ε²)` dimension** |
| 5 | ProbabilisticMethod | `probabilistic_method'` | few bad events ⟹ a point avoids them all | **pillar 3**: combinatorial core |
| 6 | GoodProjectionExists | `jl_good_projection_exists'` | per-pair concentration + small count ⟹ a good projection exists | **pillar 3**: the assembled existence |

The **meta** column is deliberately not claimed as proven. E.g. theorem 2 proves the
exact second moment for *any* expectation functional with orthonormal coordinates; it
does not construct the Gaussian measure. Theorem 6 *assumes* the per-pair concentration
bound `card(bad p) ≤ q·card Ω`; the chi-squared tail that justifies it is meta.

## Honest reckonings

- **Expectation modelled abstractly (thm 1, 2).** The expectation `E` is modelled by its
  defining algebraic properties — linearity (`lin_exp`) plus the second-moment identity
  `E[gⱼ g_l] = [j=l]` — rather than as a Gaussian integral. This is exactly the
  elementary second-moment computation; building the actual Gaussian measure and proving
  these properties is the lift to `HOL-Probability`.
- **Probabilistic method as finite counting (thm 5, 6).** `probabilistic_method` is the
  uniform-measure (counting) form: over a *finite* sample space `Ω`, if `∑ card(bad p) <
  card Ω` then a good point exists. The continuous-measure version (`P(⋃ bad) ≤ ∑ P(bad) <
  1` over a Gaussian projection space) is the same statement via `HOL-Probability`; the
  counting form is honest for a finite/discretised source and is the open lift.
- **The concentration bound is a hypothesis.** The whole probabilistic difficulty of J-L
  — the chi-squared tail giving `q ≈ exp(−c ε² k)` per pair — is the meta input. What is
  kernel-checked is everything around it: the second moment, the union bound, the
  dimension arithmetic, and the assembly into existence.
- **Constants are schematic.** The `16` and `ε²/8` in `jl_log_dimension` track an
  illustrative concentration constant `c`; the exact constant depends on the chi-squared
  tail bound used and is not pinned.

## Milestones / open targets

1. **(done)** The six-theorem development above — all kernel-checked under Isabelle2025-2
   (`isabelle build -D examples/jl JL`, exit 0, zero `sorry`). See [`RESULTS.md`](RESULTS.md).
2. The Gaussian (or Rademacher) concentration bound itself — the chi-squared tail giving
   the per-pair failure probability — in `HOL-Probability`.
3. Construct the actual random projection measure and discharge `lin_exp` /
   the orthonormal second moments, turning theorem 2 into a statement about a concrete
   random matrix.
4. Assemble 2 + 3 + the union bound into the full quantitative J-L statement (a map
   `f : ℝ^d → ℝ^k` with `(1−ε)‖u−v‖² ≤ ‖f(u)−f(v)‖² ≤ (1+ε)‖u−v‖²` for all pairs).
5. Connect to the `superposition` corpus: J-L's near-orthogonal random directions are the
   capacity counterpart of the Welch bound's interference floor.
