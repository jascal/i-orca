# Aaronson's LLM watermark — proposal

The first entry in i-orca's **"canonical proofs from other authors"** track: a
kernel-checked formalisation of the mathematical core of **Scott Aaronson's
watermarking scheme for language-model output** (UT Austin; developed while at OpenAI,
2022–2023). Where the `fieldrun` / `complexity` / `provenance` corpora formalise this
workspace's own research, this corpus reconstructs a well-known external result, in the
same i-orca discipline: honest, narrow, kernel-checked cores with an explicit
formal-vs-meta split.

## The scheme

At each generation step the model emits a probability vector `p = (p_1,…,p_N)` over the
vocabulary `V` (`p_i > 0`, `∑ p_i = 1`). A **secret key** drives a pseudorandom function
(PRF) on the recent context (the previous n-gram), producing one uniform value
`r_i ∈ (0,1)` per token. Instead of sampling from `p`, the watermark **emits the token
that maximises**

```
        gscore(r_i, p_i) = r_i ^ (1 / p_i).
```

Taking logs, maximising `r_i^(1/p_i)` is the same as **minimising**
`erace(r_i, p_i) = −ln(r_i) / p_i`. Since `−ln r_i` is an `Exp(1)` variate when
`r_i ∼ U(0,1)`, and `−ln(r_i)/p_i ∼ Exp(p_i)`, the emitted token is the winner of a race
of independent exponentials — the classical *competing-exponentials* / *Gumbel-max*
construction.

## The two properties

The scheme is simultaneously invisible and detectable — the crux of why it is useful.

**1. Distortion-free (unbiased).** Marginally over the key, token `k` is emitted with
probability *exactly* `p_k`. The watermark does **not** change the output distribution,
so watermarked text is statistically indistinguishable in quality from ordinary
sampling. The computation: conditioned on the winner's own value `r_k = u`, every other
token loses independently with probability `u^(p_i/p_k)` (the pushforward CDF), so the
product over the others is `u^((1−p_k)/p_k)`; marginalising over `u ∼ U(0,1)` gives

```
        P[k wins] = ∫₀¹ u^((1−p_k)/p_k) du = p_k.
```

**2. Detectable with the key.** A verifier holding the key recomputes each token's `r`
(deterministic given key + context) and accumulates the score `wscore(r) = −ln(1−r)`.

- *Null model* (no watermark / wrong key): the chosen token's `r` is a fresh `U(0,1)`
  draw, so `wscore(r) ∼ Exp(1)` — each token contributes mean 1, and the sum over `T`
  tokens has null mean `T`.
- *Signal* (watermarked): the winner's own `r` is biased toward 1 (its CDF `u^(1/p)`
  lies below the uniform CDF `u`), with mean `1/(1+p) ≥ 1/2`, rising to 1 as `p → 0`
  (high-entropy positions). So each `wscore` sits above its null mean and the sum
  exceeds `T` — the watermark is detected. The verifier needs only the key, not the
  model's probabilities.

## What is formalised (and the formal-vs-meta split)

The Isabelle theorems are **honest, narrow, kernel-checked cores** — the algebra and the
single-coordinate / elementary-integral content of the scheme, not the full
product-measure probability statements. The mapping from theorem to the meta-claim it
supports:

| # | i-orca theorem | Isabelle lemma | Proves (formal) | Supports (meta) |
|---|----------------|----------------|------------------|------------------|
| 1 | GumbelMaxLogEquivalence | `gumbel_mono` | `gscore`-argmax order = `erace`-argmin order | the rule is the exponential race |
| 2 | SelectionEqualsExponentialRace | `selects_iff_erace` | argmax-of-score = argmin-of-race over `V` | the emitted token is the race winner |
| 3 | SelectionDeterministic | `selects_unique` | the strict argmax is unique | output is a deterministic fn of (key→`r`, `p`); detector reproduces it |
| 4 | SelectionPushforwardCDF | `gscore_le_iff` | `gscore r p ≤ y ⟺ r ≤ y^p` | per-coordinate CDF `y^p` (the unbiasedness factor) |
| 5 | ConditionalWinCollapse | `cwin_collapse` | `∏_{i≠k} u^(p_i/p_k) = u^((1−p_k)/p_k)` | the others' independent lose-probabilities combine |
| 6 | DistortionFreeSampling | `win_prob_integral` | `∫₀¹ u^((1−p)/p) du = p` | **distortion-free**: `P[k wins] = p_k` |
| 7 | FullSupportPreserved | `cwin_pos` | win probability `> 0` on the interior | a faithful sampler, never a hard filter |
| 8 | NullScoreIsExponential | `wscore_cdf` | `P[wscore ≤ t] = 1 − e^{−t}` | null score is `Exp(1)`; sum has mean `T` |
| 9 | ScoreIncreasingInPRF | `wscore_mono` | `wscore` strictly increasing on `[0,1)` | larger `r` ⇒ more evidence |
| 10 | ChosenValueStochasticallyLarger | `chosen_r_dominates` | `u^(1/p) ≤ u` (CDF below uniform) | watermarked `r` is biased toward 1 |
| 11 | ChosenValueIsProperDensity | `dwin_integral_one` | the winner-value density integrates to 1 | the bias law is well-posed |
| 12 | ChosenValueMeanBias | `chosen_r_mean` | `E[r_chosen] = 1/(1+p)` | **the signal**: mean above the null `1/2` |

The **meta** column is deliberately not claimed as proven. E.g. theorem 6 proves the
exact value of the marginal integral that *is* the distortion-free probability for one
token; it does not, by itself, carry the full `N`-coordinate product-measure argument
(see Honest reckonings).

## Honest reckonings

- **Independence modelled algebraically (thm 4–6).** The per-coordinate pushforward CDF
  `u^(p_i/p_k)` and the product-over-others encode independence of the PRF coordinates;
  `cwin_collapse` and `win_prob_integral` are the exact algebraic and analytic steps of
  the distortion-free proof. Assembling them into a single statement over the full
  product probability space (a Fubini argument in `HOL-Probability`) is the stated lift,
  not done here — in the same spirit as the diagonal/eigenbasis witnesses in the
  `provenance` corpus.
- **Elementary regime for the integrals.** Every integral used is
  `∫₀¹ u^c du = 1/(c+1)` with `c ≥ 0` (`win_prob_integral`, `dwin_integral_one`,
  `chosen_r_mean`), discharged from the library's `has_integral_powr_from_0`; the
  exponent never enters the improper regime `c ∈ (−1,0)`.
- **Detection concentration not attempted.** `wscore_cdf` is the exact per-token null
  law (`Exp(1)`) and `chosen_r_mean` quantifies the watermarked mean shift, but the
  concentration of the `T`-token score-sum — the Chernoff / p-value bound that turns
  mean separation into a false-positive guarantee — is a probabilistic lift left to
  `HOL-Probability`.
- **Single-position model.** Each theorem concerns one generation step. Context
  windowing, the n-gram hashing of the PRF, and robustness to edits/paraphrase
  (substitution, insertion, deletion of tokens) are out of scope.

## Milestones / open targets

1. **(done)** The twelve-theorem development above — all kernel-checked under
   Isabelle2025-2 (`isabelle build -D examples/watermark Watermark`, exit 0, zero
   `sorry`). See [`RESULTS.md`](RESULTS.md).
2. The product-measure / Fubini lift of distortion-freeness: from the per-coordinate CDF
   to `P[k wins] = p_k` over `∏ U(0,1)` in `HOL-Probability`.
3. A Chernoff bound on the `T`-token score-sum giving an explicit false-positive rate at
   a threshold — the formal detection guarantee.
4. Robustness: bound the score loss under a bounded number of token edits.
5. Relate the per-token entropy `p` to fieldrun's `density_on` so "high-entropy
   position ⇒ strong watermark signal" is the same quantity fieldrun measures.
