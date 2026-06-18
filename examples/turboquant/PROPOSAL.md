# TurboQuant — proposal

The fifth entry in i-orca's **"canonical proofs from other authors"** track (after the
Aaronson watermark, the tropical geometry of ReLU networks, Anthropic's Toy Models of
Superposition, and Johnson–Lindenstrauss): a kernel-checked formalisation of the
distortion-rate structure of **TurboQuant**.

**Source.** Amir Zandieh, Majid Daliri, Majid Hadian & Vahab Mirrokni, *"TurboQuant:
Online Vector Quantization with Near-optimal Distortion Rate"*, Google Research / Google
DeepMind / NYU, arXiv:2504.19874, 2025.

## The idea

TurboQuant compresses high-dimensional vectors (LLM KV caches, embeddings) to `b`
bits/coordinate while preserving their geometry. It **randomly rotates** the input —
inducing a concentrated **Beta** distribution on each coordinate (converging to
`N(1, 1/d)` in high dimension) — then applies **optimal scalar Lloyd–Max quantizers**
per coordinate, exploiting the near-independence of distinct coordinates. For unbiased
inner-product estimation it composes an MSE quantizer with a **1-bit Quantized-JL**
transform on the residual. The paper's bounds, for any worst-case unit vector `x`:

| | upper bound (achievable) | lower bound (Shannon + Yao) |
|---|---|---|
| **MSE** (Thm 1, 3) | `D_mse ≤ (√3·π/2)·(1/4ᵇ)` | `D_mse ≥ 1/4ᵇ` |
| **inner product** (Thm 2, 3) | `D_prod ≤ (√3·π²·‖y‖²/d)·(1/4ᵇ)` | `D_prod ≥ (‖y‖²/d)·(1/4ᵇ)` |

with `E[⟨y, dequant(x)⟩] = ⟨y, x⟩` (unbiased). The upper bounds match the lower bounds up
to the small constant `√3π/2 ≈ 2.7`.

## What is formalised (and the formal-vs-meta split)

We model the four bounds as functions and kernel-check the **quantitative structure** the
paper highlights — the rate arithmetic those bounds imply — together with the
inner-product unbiasedness. The *achievability* of the upper bounds (random rotation,
Beta concentration, Lloyd–Max optimality) and the *lower bound* proof itself are the
honest meta inputs. Three theories, eleven surfaced theorems:

| # | i-orca theorem | Isabelle lemma | Proves (formal) | Supports (meta) |
|---|----------------|----------------|------------------|------------------|
| 1 | MSEApproximationRatio | `mse_ratio_const` | `mse_ub = (√3π/2)·mse_lb` | upper is a fixed multiple of lower |
| 2 | MSERatioIsConstant | `mse_ratio_eq` | `mse_ub/mse_lb = √3π/2` | **near-optimal across all bit-widths** |
| 3 | ProdApproximationRatio | `prod_ratio_const` | `prod_ub = (√3π²)·prod_lb` | ratio constant in `d`, `‖y‖²`, `b` |
| 4 | MSEGeometricDecay | `mse_decay` | `mse_ub(b+1) = mse_ub(b)/4` | **geometric rate** `1/4ᵇ` |
| 5 | ProdGeometricDecay | `prod_decay` | `prod_ub(b+1) = prod_ub(b)/4` | geometric rate (inner product) |
| 6 | NearOptimalConstant | `mse_const_approx` | `2.7 < √3π/2 < 2.73` | the `≈ 2.7` constant |
| 7 | MSEAboveLowerBound | `mse_achievable` | `mse_lb ≤ mse_ub` | the bounds bracket without crossing |
| 8 | ProdDimensionDecay | `prod_dim_decay` | `prod_ub` decreasing in `d` | **high-dimensional advantage** |
| 9 | ExpectationLinearOverSum | `expectation_sum'` | a linear `E` commutes with sums | workhorse for unbiasedness |
| 10 | InnerProductUnbiased | `inner_product_unbiased'` | coordinatewise-unbiased ⟹ `E[⟨y,dq⟩]=⟨y,x⟩` | **Thm 2 unbiasedness** |
| 11 | FourBitDistortion | `example_four_bit_distortion` | `mse_ub 4 < 0.011` | a concrete operating point |

The **meta** column is deliberately not claimed as proven. E.g. theorem 1 proves the ratio
is the stated constant *given* the two bounds; it does not prove TurboQuant *achieves* the
upper bound, nor that `1/4ᵇ` is the true Shannon rate.

## Honest reckonings

- **Bounds as hypotheses (thm 1–8, 11).** The MSE/inner-product upper and lower bounds
  are encoded as the functions `mse_ub`, `mse_lb`, `prod_ub`, `prod_lb`; the theorems are
  the exact algebra those four functions satisfy (ratio is constant, rate is geometric,
  bounds are consistent, the constant is `≈2.7`, the inner-product bound decays in `d`).
  This is the genuinely-checkable quantitative essence; the *derivation* of the bounds is
  meta.
- **The achievability is meta.** The random rotation, the Beta/`N(1,1/d)` concentration of
  a coordinate of a uniform point on the sphere, the near-independence of coordinates, and
  the Lloyd–Max scalar-quantizer optimality — the whole probabilistic/source-coding engine
  behind the upper bounds — are not formalised. Likewise the Shannon + Yao minimax lower
  bound (Thm 3).
- **Unbiasedness modelled abstractly (thm 9, 10).** As in the `jl` corpus, the expectation
  is a `lin_exp` functional (linear), and the per-coordinate unbiasedness of the
  Quantized-JL residual is a hypothesis; the inner-product unbiasedness then follows by
  linearity. Constructing the actual QJL measure and proving the coordinate unbiasedness is
  the lift to `HOL-Probability`.
- **The `2.7` constant is genuine.** `mse_const_approx` is a real kernel-checked numeric
  bound `2.7 < √3π/2 < 2.73`, from `pi_approx` and rational bounds on `√3` — not assumed.

## Milestones / open targets

1. **(done)** The eleven-theorem development above — all kernel-checked under
   Isabelle2025-2 (`isabelle build -D examples/turboquant TurboQuant`, exit 0, zero
   `sorry`). See [`RESULTS.md`](RESULTS.md).
2. The Beta/`N(1,1/d)` concentration of a coordinate of a uniformly random unit vector,
   in `HOL-Probability` (the heart of the achievability).
3. The Lloyd–Max scalar-quantizer optimality (a continuous 1-D `k`-means argument).
4. The Shannon + Yao minimax lower bound (Theorem 3) from differential entropy / mutual
   information.
5. Connect the 1-bit Quantized-JL stage to the `jl` corpus, so the unbiased estimator's
   per-coordinate unbiasedness is discharged rather than assumed.
