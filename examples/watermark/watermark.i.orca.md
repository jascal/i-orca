<!--
  i-orca surface for AARONSON'S LLM WATERMARK -- the first entry in i-orca's
  "canonical proofs from other authors" track.

  Scheme: Scott Aaronson (UT Austin; OpenAI 2022-2023). At each step the model emits a
  probability vector p over the vocabulary; a secret-keyed pseudorandom function turns
  the recent context into one uniform value r i in (0,1) per token; the watermark emits
  argmax_i (r i) powr (1 / p i) instead of sampling. The scheme is simultaneously:

    DISTORTION-FREE -- marginally, token k is emitted with probability exactly p k, so
      watermarked text matches ordinary-sampling quality (the Gumbel / exponential-race
      identity); and
    DETECTABLE WITH THE KEY -- a verifier recomputing r scores each token by
      -ln(1 - r); the chosen token's r is biased toward 1, so the score-sum exceeds its
      key-free null mean.

  As in ../provenance/provenance.i.orca.md and ../complexity/complexity.i.orca.md, the
  heavy content lives in the kernel-checked Isabelle theories in this directory
  (GumbelSelect.thy, Unbiased.thy, Detect.thy); each theorem below is STATED in i-orca
  form and discharged by `(rule <lemma>)` against its Isabelle lemma, resolved through
  `## imports`. We deliberately do NOT list the cited lemma in `## context` (the
  compiler lowers context rows to local `assumes`, which would turn the cite into a
  vacuous P => P).

  Verification:
    - `i-orca verify` (structural, zero Isabelle): all theorems VALID,
      formal_fraction_static = 1.000.
    - Kernel check: the compiled `theorem T: "<goal>" by (rule <lemma>)` is non-vacuous
      and kernel-checks when built INSIDE the `Watermark` session (this directory's ROOT):
          ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/watermark \
            -o quick_and_dirty Watermark
      The standalone `i-orca check` builds each theorem under a plain HOL parent and
      cannot load this project-local session -- an import-resolution limit, not a math
      failure (same caveat as the provenance and complexity corpora).

  Map to the scheme:
    SELECTION RULE        -> GumbelMaxLogEquivalence, SelectionEqualsExponentialRace,
                             SelectionDeterministic, SelectionPushforwardCDF
    DISTORTION-FREE       -> ConditionalWinCollapse, DistortionFreeSampling,
                             FullSupportPreserved
    DETECTABILITY         -> NullScoreIsExponential, ScoreIncreasingInPRF,
                             ChosenValueStochasticallyLarger, ChosenValueIsProperDensity,
                             ChosenValueMeanBias
-->

# theorem GumbelMaxLogEquivalence
> The Gumbel-max trick. Maximising the watermark score `(r i) powr (1/p i)` is the same as minimising the exponential-race statistic `erace (r i) (p i) = -ln(r i)/p i`: token 2 beats token 1 in the score exactly when it has the smaller race statistic. Since `-ln r` is an Exp(1) variate for `r ~ U(0,1)`, this is the classical competing-exponentials race. Cites `gumbel_mono`.

## imports
| Theory       |
|--------------|
| GumbelSelect |

## goal
| Statement |
|-----------|
| 0 < r1 ⟹ 0 < r2 ⟹ 0 < p1 ⟹ 0 < p2 ⟹ (gscore r1 p1 < gscore r2 p2) = (erace r2 p2 < erace r1 p1) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < r1 ⟹ 0 < r2 ⟹ 0 < p1 ⟹ 0 < p2 ⟹ (gscore r1 p1 < gscore r2 p2) = (erace r2 p2 < erace r1 p1) | exp is strictly monotone, so the powr-ordering and the log-ratio ordering coincide | — | (rule gumbel_mono) | method |


# theorem SelectionEqualsExponentialRace
> Lifted to the whole vocabulary: the watermark's argmax-of-score rule is exactly the argmin-of-exponential-race rule. The token the watermark emits is the one with the smallest `-ln(r i)/p i`. Cites `selects_iff_erace`.

## imports
| Theory       |
|--------------|
| GumbelSelect |

## goal
| Statement |
|-----------|
| (∀i∈V. 0 < r i) ⟹ (∀i∈V. 0 < p i) ⟹ k ∈ V ⟹ selects V r p k = erace_selects V r p k |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (∀i∈V. 0 < r i) ⟹ (∀i∈V. 0 < p i) ⟹ k ∈ V ⟹ selects V r p k = erace_selects V r p k | apply the pointwise Gumbel-max equivalence under each token's positivity | — | (rule selects_iff_erace) | method |


# theorem SelectionDeterministic
> Determinism / reproducibility. Two tokens cannot both strictly dominate, so the emitted token is unique — a deterministic function of the key-derived `r` and the model's `p`. The keyed verifier, recomputing the same `r` from the same context, recovers the same winner; this is what makes detection well-defined. Cites `selects_unique`.

## imports
| Theory       |
|--------------|
| GumbelSelect |

## goal
| Statement |
|-----------|
| selects V r p k ⟹ selects V r p l ⟹ k ∈ V ⟹ l ∈ V ⟹ k = l |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | selects V r p k ⟹ selects V r p l ⟹ k ∈ V ⟹ l ∈ V ⟹ k = l | if both win then each strictly dominates the other — contradiction | — | (rule selects_unique) | method |


# theorem SelectionPushforwardCDF
> The per-coordinate pushforward CDF. Pushing a uniform `r` through the watermark map gives, for a threshold `y` in (0,1), the event `r ≤ y powr p`; under `r ~ U(0,1)` this has probability `y powr p`. This is the building block multiplied out in the distortion-free computation. Cites `gscore_le_iff`.

## imports
| Theory       |
|--------------|
| GumbelSelect |

## goal
| Statement |
|-----------|
| 0 < r ⟹ 0 < y ⟹ 0 < p ⟹ (gscore r p ≤ y) = (r ≤ y powr p) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < r ⟹ 0 < y ⟹ 0 < p ⟹ (gscore r p ≤ y) = (r ≤ y powr p) | raising to the power p (resp. 1/p) is monotone and inverts the watermark map on the positives | — | (rule gscore_le_iff) | method |


# theorem ConditionalWinCollapse
> Distortion-free, step 1. Conditioned on the chosen token's own PRF value `r k = u`, the probability every other token loses is the product of their independent lose-probabilities `u powr (p i / p k)`, which collapses to a single power `u powr ((1 - p k)/p k)` — because the other tokens carry total mass `1 - p k`. Cites `cwin_collapse`.

## imports
| Theory   |
|----------|
| Unbiased |

## goal
| Statement |
|-----------|
| 0 < u ⟹ finite S ⟹ k ∈ S ⟹ (∑i∈S. p i) = 1 ⟹ 0 < p k ⟹ cwin p k S u = u powr ((1 - p k) / p k) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < u ⟹ finite S ⟹ k ∈ S ⟹ (∑i∈S. p i) = 1 ⟹ 0 < p k ⟹ cwin p k S u = u powr ((1 - p k) / p k) | equal-base product collapses to a power of the summed exponents; the others sum to 1 - p k | — | (rule cwin_collapse) | method |


# theorem DistortionFreeSampling
> The headline. Marginalising the collapsed conditional win probability over the winner's own uniform value gives selection probability EXACTLY `p` — the watermark does not change the model's output distribution. The value of the elementary integral `∫₀¹ u powr ((1-p)/p) du = p`. Cites `win_prob_integral`.

## imports
| Theory   |
|----------|
| Unbiased |

## goal
| Statement |
|-----------|
| 0 < p ⟹ p ≤ 1 ⟹ ((λu. u powr ((1 - p) / p)) has_integral (p::real)) {0..1} |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < p ⟹ p ≤ 1 ⟹ ((λu. u powr ((1 - p) / p)) has_integral (p::real)) {0..1} | the unbiasedness integral evaluates to p at exponent (1-p)/p | — | (rule win_prob_integral) | method |


# theorem FullSupportPreserved
> A corollary of distortion-freeness: on the interior every token keeps strictly positive selection probability, so the watermark never zeroes a feasible token — it is a faithful sampler, not a hard filter. Cites `cwin_pos`.

## imports
| Theory   |
|----------|
| Unbiased |

## goal
| Statement |
|-----------|
| 0 < u ⟹ finite S ⟹ 0 < cwin p k S u |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < u ⟹ finite S ⟹ 0 < cwin p k S u | a product of strictly positive powers of a positive base is positive | — | (rule cwin_pos) | method |


# theorem NullScoreIsExponential
> Detection calibration. Under the null (text produced without the key) the chosen token's `r` is a fresh `U(0,1)` draw, so the verifier's per-token score `wscore r = -ln(1 - r)` is Exponential(1): `P[wscore r ≤ t] = 1 - exp(-t)`. Each token contributes mean 1, so the score-sum over T tokens has null mean T — the calibrated baseline a threshold sits above. Cites `wscore_cdf`.

## imports
| Theory |
|--------|
| Detect |

## goal
| Statement |
|-----------|
| 0 ≤ t ⟹ r < 1 ⟹ (wscore r ≤ t) = (r ≤ 1 - exp (- t)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 ≤ t ⟹ r < 1 ⟹ (wscore r ≤ t) = (r ≤ 1 - exp (- t)) | invert the score through exp/ln monotonicity to the exact quantile of the uniform | — | (rule wscore_cdf) | method |


# theorem ScoreIncreasingInPRF
> The score is strictly increasing in the PRF value: a token whose recomputed `r` is closer to 1 contributes more detection evidence. Combined with the chosen-value bias below, this is the source of the watermark signal. Cites `wscore_mono`.

## imports
| Theory |
|--------|
| Detect |

## goal
| Statement |
|-----------|
| 0 ≤ r1 ⟹ r1 < r2 ⟹ r2 < 1 ⟹ wscore r1 < wscore r2 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 ≤ r1 ⟹ r1 < r2 ⟹ r2 < 1 ⟹ wscore r1 < wscore r2 | -ln(1 - r) is strictly increasing on [0,1) | — | (rule wscore_mono) | method |


# theorem ChosenValueStochasticallyLarger
> Why watermarked text scores high. Under the watermark the winning token's own PRF value is biased toward 1: its CDF `u powr (1/p)` lies below the uniform CDF `u` (first-order stochastic dominance), because `1/p ≥ 1`. So the verifier systematically sees large `r` at watermarked positions. Cites `chosen_r_dominates`.

## imports
| Theory |
|--------|
| Detect |

## goal
| Statement |
|-----------|
| 0 ≤ u ⟹ u ≤ 1 ⟹ 0 < p ⟹ p ≤ 1 ⟹ (u::real) powr (1 / p) ≤ u |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 ≤ u ⟹ u ≤ 1 ⟹ 0 < p ⟹ p ≤ 1 ⟹ (u::real) powr (1 / p) ≤ u | for a base in [0,1], powr is antitone in the exponent and 1/p ≥ 1 | — | (rule chosen_r_dominates) | method |


# theorem ChosenValueIsProperDensity
> The winner's value, given that token k wins, has the law with density `dwin p u = (1/p) · u powr (1/p − 1)` on (0,1). This confirms it is a genuine probability density — it integrates to 1 — so the mean below is well-defined. Cites `dwin_integral_one`.

## imports
| Theory |
|--------|
| Detect |

## goal
| Statement |
|-----------|
| 0 < p ⟹ p ≤ 1 ⟹ ((λu. dwin p u) has_integral 1) {0..1} |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < p ⟹ p ≤ 1 ⟹ ((λu. dwin p u) has_integral 1) {0..1} | the density integrates to 1 by the elementary power integral | — | (rule dwin_integral_one) | method |


# theorem ChosenValueMeanBias
> The detection signal, quantified. The winner's PRF value has mean `1/(1+p)` — at least `1/2`, rising to 1 as `p → 0` (high-entropy positions). This positive bias over the key-free null mean `1/2` is exactly what lifts the per-token score above 1 and pushes the score-sum above its null mean T, letting the verifier detect the watermark. Cites `chosen_r_mean`.

## imports
| Theory |
|--------|
| Detect |

## goal
| Statement |
|-----------|
| 0 < p ⟹ p ≤ 1 ⟹ ((λu. u * dwin p u) has_integral (1 / (1 + p))) {0..1} |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < p ⟹ p ≤ 1 ⟹ ((λu. u * dwin p u) has_integral (1 / (1 + p))) {0..1} | integrate u against the winner-value density to get 1/(1+p) | — | (rule chosen_r_mean) | method |
