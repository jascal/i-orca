<!--
  i-orca surface for TURBOQUANT -- the fifth entry in i-orca's "canonical proofs from other
  authors" track (after watermark, tropical, superposition, jl).

  Source: Amir Zandieh, Majid Daliri, Majid Hadian & Vahab Mirrokni, "TurboQuant: Online
  Vector Quantization with Near-optimal Distortion Rate", Google Research / Google DeepMind
  / NYU, arXiv:2504.19874, 2025. TurboQuant quantizes high-dimensional vectors (KV caches,
  embeddings) to b bits/coordinate with near-optimal distortion, by randomly rotating the
  input (inducing a Beta distribution on coordinates) and applying optimal scalar Lloyd-Max
  quantizers, plus a 1-bit Quantized-JL transform on the residual for unbiased inner
  products.

  The paper's headline bounds (||x|| = 1):
    Thm 1 (MSE)        D_mse  <= (sqrt 3 * pi / 2) / 4^b
    Thm 2 (inner-prod) D_prod <= (sqrt 3 * pi^2 * ||y||^2 / d) / 4^b ,  E[<y,dq>] = <y,x>
    Thm 3 (lower bnd)  D_mse  >= 1/4^b ;  D_prod >= (||y||^2/d)/4^b

  We model the four bounds as functions and kernel-check the QUANTITATIVE STRUCTURE they
  imply -- the near-optimality ratio is a constant (the 4^b/d/||y||^2 cancel), the rate is
  geometric in bit-width, the constant is ~2.7, the upper bound is consistent with the
  lower bound, and the inner-product estimator is unbiased. The achievability of the upper
  bounds (random rotation, Beta concentration, Lloyd-Max optimality) and the lower bound
  itself are the META inputs; what is proved is the rate arithmetic. Each theorem below is
  discharged by `(rule <lemma>)`.

  Verification:
    - `i-orca verify` (structural, zero Isabelle): all theorems VALID, fraction 1.000.
    - Kernel check: built INSIDE the `TurboQuant` session (this directory's ROOT):
          ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/turboquant \
            -o quick_and_dirty TurboQuant
      (standalone `i-orca check` cannot load the project-local session -- same caveat as
      the other corpora.)

  Map to the paper:
    NEAR-OPTIMALITY -> MSEApproximationRatio, MSERatioIsConstant, ProdApproximationRatio,
                       NearOptimalConstant, MSEAboveLowerBound
    GEOMETRIC RATE  -> MSEGeometricDecay, ProdGeometricDecay
    HIGH-DIM BENEFIT-> ProdDimensionDecay
    UNBIASED PROD   -> ExpectationLinearOverSum, InnerProductUnbiased
    WORKED EXAMPLE  -> FourBitDistortion
-->

# theorem MSEApproximationRatio
> Near-optimality of the MSE bound: the TurboQuant upper bound is a fixed constant multiple `√3·π/2` of the information-theoretic lower bound — the SAME multiple for every bit-width `b`, because the `1/4ᵇ` rate factor is common to both. Cites `mse_ratio_const`.

## imports
| Theory         |
|----------------|
| DistortionRate |

## goal
| Statement |
|-----------|
| mse_ub b = (sqrt 3 * pi / 2) * mse_lb b |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | mse_ub b = (sqrt 3 * pi / 2) * mse_lb b | the upper and lower bounds share the 1/4ᵇ rate; their ratio is the constant √3π/2 | — | (rule mse_ratio_const) | method |


# theorem MSERatioIsConstant
> The same fact as a ratio: `D_mse_ub / D_mse_lb = √3·π/2`, a constant independent of the bit-width — the precise sense of "near-optimal across all bit-widths". Cites `mse_ratio_eq`.

## imports
| Theory         |
|----------------|
| DistortionRate |

## goal
| Statement |
|-----------|
| mse_ub b / mse_lb b = sqrt 3 * pi / 2 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | mse_ub b / mse_lb b = sqrt 3 * pi / 2 | the 4ᵇ cancels in the quotient | — | (rule mse_ratio_eq) | method |


# theorem ProdApproximationRatio
> Near-optimality of the inner-product bound: its ratio to the lower bound is the constant `√3·π²`, the SAME for every dimension `d`, squared norm `‖y‖²`, and bit-width `b` — they all cancel. Cites `prod_ratio_const`.

## imports
| Theory         |
|----------------|
| DistortionRate |

## goal
| Statement |
|-----------|
| prod_ub d ny b = (sqrt 3 * pi\<^sup>2) * prod_lb d ny b |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | prod_ub d ny b = (sqrt 3 * pi\<^sup>2) * prod_lb d ny b | the d, ‖y‖² and 4ᵇ factors are common to both bounds | — | (rule prod_ratio_const) | method |


# theorem MSEGeometricDecay
> Geometric rate: each additional bit quarters the MSE distortion bound, `D(b+1) = D(b)/4` — distortion decays as `1/4ᵇ`, the exponential improvement in bit-width the paper claims. Cites `mse_decay`.

## imports
| Theory         |
|----------------|
| DistortionRate |

## goal
| Statement |
|-----------|
| mse_ub (Suc b) = mse_ub b / 4 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | mse_ub (Suc b) = mse_ub b / 4 | the bound carries a 1/4ᵇ factor | — | (rule mse_decay) | method |


# theorem ProdGeometricDecay
> The inner-product distortion bound also quarters with each extra bit. Cites `prod_decay`.

## imports
| Theory         |
|----------------|
| DistortionRate |

## goal
| Statement |
|-----------|
| prod_ub d ny (Suc b) = prod_ub d ny b / 4 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | prod_ub d ny (Suc b) = prod_ub d ny b / 4 | the bound carries a 1/4ᵇ factor | — | (rule prod_decay) | method |


# theorem NearOptimalConstant
> The near-optimality constant is approximately 2.7: `2.7 < √3·π/2 < 2.73`, kernel-checked from the rational bounds on `π` and `√3`. Cites `mse_const_approx`.

## imports
| Theory         |
|----------------|
| DistortionRate |

## goal
| Statement |
|-----------|
| 2.7 < sqrt 3 * pi / 2 ∧ sqrt 3 * pi / 2 < 2.73 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 2.7 < sqrt 3 * pi / 2 ∧ sqrt 3 * pi / 2 < 2.73 | bound √3 in (1.7320, 1.7321) and π via pi_approx | — | (rule mse_const_approx) | method |


# theorem MSEAboveLowerBound
> Consistency: TurboQuant's achievable MSE upper bound sits above the information-theoretic lower bound (the near-optimality factor `√3π/2 ≥ 1`), so the two bounds bracket the true distortion without crossing. Cites `mse_achievable`.

## imports
| Theory         |
|----------------|
| DistortionRate |

## goal
| Statement |
|-----------|
| mse_lb b ≤ mse_ub b |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | mse_lb b ≤ mse_ub b | the achievable bound is √3π/2 ≥ 1 times the lower bound | — | (rule mse_achievable) | method |


# theorem ProdDimensionDecay
> High-dimensional advantage: the inner-product distortion bound shrinks as the embedding dimension `d` grows — quantization becomes more accurate in higher dimensions (the `1/d` factor). Cites `prod_dim_decay`.

## imports
| Theory         |
|----------------|
| DistortionRate |

## goal
| Statement |
|-----------|
| 0 < d ⟹ d ≤ d' ⟹ 0 ≤ ny ⟹ prod_ub d' ny b ≤ prod_ub d ny b |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < d ⟹ d ≤ d' ⟹ 0 ≤ ny ⟹ prod_ub d' ny b ≤ prod_ub d ny b | the bound is proportional to 1/d, decreasing in d | — | (rule prod_dim_decay) | method |


# theorem ExpectationLinearOverSum
> A linear expectation functional commutes with finite sums: `E[∑ⱼ Fⱼ] = ∑ⱼ E[Fⱼ]`. The workhorse for the unbiasedness below. Cites `expectation_sum'`.

## imports
| Theory   |
|----------|
| Unbiased |

## goal
| Statement |
|-----------|
| lin_exp Exp ⟹ finite A ⟹ Exp (λs. ∑a∈A. F a s) = (∑a∈A. Exp (F a)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | lin_exp Exp ⟹ finite A ⟹ Exp (λs. ∑a∈A. F a s) = (∑a∈A. Exp (F a)) | additivity lifted over a finite sum by induction | — | (rule expectation_sum') | method |


# theorem InnerProductUnbiased
> Theorem 2's unbiasedness: if the dequantized residual is coordinatewise unbiased (`E[dqⱼ] = xⱼ`), then by linearity the inner-product estimator is unbiased, `E[⟨y, dq⟩] = ⟨y, x⟩` — the property the 1-bit Quantized-JL stage delivers. Cites `inner_product_unbiased'`.

## imports
| Theory   |
|----------|
| Unbiased |

## goal
| Statement |
|-----------|
| finite J ⟹ lin_exp Exp ⟹ (∀j∈J. Exp (dq j) = x j) ⟹ Exp (λs. ∑j∈J. y j * dq j s) = (∑j∈J. y j * x j) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite J ⟹ lin_exp Exp ⟹ (∀j∈J. Exp (dq j) = x j) ⟹ Exp (λs. ∑j∈J. y j * dq j s) = (∑j∈J. y j * x j) | push E through the sum, pull out yⱼ, use the per-coordinate unbiasedness | — | (rule inner_product_unbiased') | method |


# theorem FourBitDistortion
> A concrete operating point: at a bit-width of 4 the MSE distortion bound is below `0.011` (the closed form is `(√3π/2)/256`), matching the paper's reported small-bit-width figure. Cites `example_four_bit_distortion`.

## imports
| Theory   |
|----------|
| Examples |

## goal
| Statement |
|-----------|
| mse_ub 4 < 0.011 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | mse_ub 4 < 0.011 | (√3π/2)/256 < 2.73/256 < 0.011 | — | (rule example_four_bit_distortion) | method |
