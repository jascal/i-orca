<!--
  i-orca surface for BITNET b1.58 / TERNARY WEIGHTS -- the sixth entry in i-orca's
  "canonical proofs from other authors" track (after watermark, tropical, superposition,
  jl, turboquant).

  Source: Ma, Wang, Ma, Wang, Wang, Huang, Dong, Wang, Xue & Wei, "The Era of 1-bit LLMs:
  All Large Language Models are in 1.58 Bits", Microsoft Research, arXiv:2402.17764, 2024.
  BitNet b1.58 makes every weight ternary {-1, 0, 1} (~1.58 = log2 3 bits each), turning the
  matmul into a multiplication-free signed sum. Weights come from an absmean RoundClip
  quantizer: W~ = RoundClip(W/(gamma+eps), -1, 1), gamma = mean|W|.

  This corpus formalises the structural cores, AND -- prompted by a question about whether a
  LOSSLESS transformation to BitNet is theoretically possible -- the precise answer:

    * per-weight ternarization is necessarily LOSSY (the quantizer is non-injective);
    * BUT a finite-precision (integer-weight) layer has an EXACT, lossless ternary
      realization by EXPANSION: every integer weight is a balanced-ternary combination
      SUM_j t_j 3^j (t_j in {-1,0,1}), and distributing those digits through the matmul
      gives the integer-weight output as a power-of-3 weighted sum of ternary matmuls.

  The expansion factor (number of trits ~ precision / log2 3) is the price; minimising it --
  the sparsest behaviourally-equivalent ternary net -- is the genuine optimisation problem,
  well-posed over a relational / Datalog encoding (existence is easy; minimality is hard).

  As in the sibling corpora, the heavy content lives in the Isabelle theories here and each
  theorem below is discharged by `(rule <lemma>)`.

  Verification:
    - `i-orca verify` (structural, zero Isabelle): all theorems VALID, fraction 1.000.
    - Kernel check: built INSIDE the `BitNet` session (this directory's ROOT):
          ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/bitnet \
            -o quick_and_dirty BitNet
      (standalone `i-orca check` cannot load the project-local session -- same caveat as
      the other corpora.)

  Map to the paper / the lossless question:
    MULT-FREE MATMUL  -> TernaryProductIsMultiplication, TernaryDotIsSignedSum
    ABSMEAN QUANTIZER -> QuantizerIsTernary, QuantizerNotInjective
    LOSSLESS-BY-EXPANSION -> BalancedTernaryExists, LosslessRealization, LosslessWeight
    1.58 BITS         -> TernaryBitWidth, FiveTritsPerByte
-->

# theorem TernaryProductIsMultiplication
> A ternary weight acts on x without multiplication: `tprod w x` is `+x`, `-x`, or `0`, and equals `(of_int w)·x` for `w ∈ {−1,0,1}`. The atomic operation of a BitNet layer. Cites `tprod_is_mult`.

## imports
| Theory  |
|---------|
| Ternary |

## goal
| Statement |
|-----------|
| w ∈ {-1, 0, 1} ⟹ tprod w x = of_int w * x |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | w ∈ {-1, 0, 1} ⟹ tprod w x = of_int w * x | a ternary weight selects +x, -x, or 0 | — | (rule tprod_is_mult) | method |


# theorem TernaryDotIsSignedSum
> The multiplication-free matmul. A ternary dot product is the sum of x over the `+1` weights minus the sum over the `−1` weights — additions and subtractions only, no multiplies. This is the computational payoff of BitNet. Cites `ternary_dot_signed_sum`.

## imports
| Theory  |
|---------|
| Ternary |

## goal
| Statement |
|-----------|
| finite I ⟹ (∀i∈I. w i ∈ {-1, 0, 1}) ⟹ (∑i∈I. tprod (w i) (x i)) = (∑i∈{i∈I. w i = 1}. x i) - (∑i∈{i∈I. w i = - 1}. x i) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite I ⟹ (∀i∈I. w i ∈ {-1, 0, 1}) ⟹ (∑i∈I. tprod (w i) (x i)) = (∑i∈{i∈I. w i = 1}. x i) - (∑i∈{i∈I. w i = - 1}. x i) | split the index set by weight sign; the zero weights drop out | — | (rule ternary_dot_signed_sum) | method |


# theorem QuantizerIsTernary
> The absmean RoundClip quantizer maps any real value into the ternary set `{−1,0,1}`. Cites `roundclip_ternary`.

## imports
| Theory  |
|---------|
| Ternary |

## goal
| Statement |
|-----------|
| roundclip x ∈ {-1, 0, 1} |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | roundclip x ∈ {-1, 0, 1} | round then clip to [-1, 1] lands in {-1, 0, 1} | — | (rule roundclip_ternary) | method |


# theorem QuantizerNotInjective
> Per-weight ternarization is necessarily LOSSY: the quantizer collapses distinct weights to the same ternary value (e.g. `0.3` and `0.4` both map to `0`), so it has no inverse. The honest counterpoint to the lossless-by-expansion results below. Cites `roundclip_not_injective`.

## imports
| Theory  |
|---------|
| Ternary |

## goal
| Statement |
|-----------|
| ∃a b. a ≠ b ∧ roundclip a = roundclip b |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∃a b. a ≠ b ∧ roundclip a = roundclip b | two distinct reals rounding to the same ternary value | — | (rule roundclip_not_injective) | method |


# theorem BalancedTernaryExists
> The lossless-by-expansion crux: every integer is a balanced-ternary combination `n = ∑ⱼ tⱼ·3ʲ` with each `tⱼ ∈ {−1,0,1}`. A finite-precision weight decomposes EXACTLY into ternary digits — no information lost, only the representation expands. Cites `balanced_ternary_exists`.

## imports
| Theory          |
|-----------------|
| BalancedTernary |

## goal
| Statement |
|-----------|
| ∃ts. (∀d∈set ts. d ∈ {-1, 0, 1}) ∧ (n::int) = (∑j<length ts. ts ! j * 3 ^ j) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∃ts. (∀d∈set ts. d ∈ {-1, 0, 1}) ∧ (n::int) = (∑j<length ts. ts ! j * 3 ^ j) | extract balanced residues by strong induction on the magnitude | — | (rule balanced_ternary_exists) | method |


# theorem LosslessRealization
> The lossless ternary realization of a layer: an integer-weight dot product equals a power-of-3 weighted sum of ternary dot products, by distributing each weight's balanced-ternary digits through the matmul. The real layer's exact output is recovered from ternary matmuls. Cites `lossless_realization`.

## imports
| Theory   |
|----------|
| Lossless |

## goal
| Statement |
|-----------|
| finite I ⟹ (∑i∈I. (∑j<K. (t i j::int) * 3 ^ j) * x i) = (∑j<K. 3 ^ j * (∑i∈I. t i j * x i)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite I ⟹ (∑i∈I. (∑j<K. (t i j::int) * 3 ^ j) * x i) = (∑j<K. 3 ^ j * (∑i∈I. t i j * x i)) | swap the weight and digit sums; factor out each power of 3 | — | (rule lossless_realization) | method |


# theorem LosslessWeight
> The unconditional single-weight form (the direct answer): every integer weight `w`, acting on `x`, is EXACTLY a power-of-3 weighted sum of ternary products — each `tⱼ·x` being `+x`, `0`, or `−x`. Lossless, multiplication-free, by expansion. Cites `lossless_weight`.

## imports
| Theory   |
|----------|
| Lossless |

## goal
| Statement |
|-----------|
| ∃ts. (∀d∈set ts. d ∈ {-1, 0, 1}) ∧ (w::int) * x = (∑j<length ts. 3 ^ j * (ts ! j * x)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∃ts. (∀d∈set ts. d ∈ {-1, 0, 1}) ∧ (w::int) * x = (∑j<length ts. 3 ^ j * (ts ! j * x)) | decompose w into balanced-ternary digits and distribute over x | — | (rule lossless_weight) | method |


# theorem TernaryBitWidth
> The "1.58 bits": a ternary symbol carries `log₂3` bits, with `1.5 < log₂3 < 1.6` (true value ≈ 1.585) — kernel-checked from `2^1.5 < 3` and `3 < 2^1.6`. Cites `log2_3_approx`.

## imports
| Theory   |
|----------|
| BitWidth |

## goal
| Statement |
|-----------|
| 1.5 < log 2 3 ∧ log 2 3 < 1.6 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 1.5 < log 2 3 ∧ log 2 3 < 1.6 | raise to integer powers: 2^3 < 3^2 and 3^5 < 2^8 | — | (rule log2_3_approx) | method |


# theorem FiveTritsPerByte
> The packing fact behind the upper bound: five trits fit in a byte, `3⁵ = 243 ≤ 256 = 2⁸` — equivalently `log₂3 < 1.6`. Cites `five_trits_per_byte`.

## imports
| Theory   |
|----------|
| BitWidth |

## goal
| Statement |
|-----------|
| (3::nat) ^ 5 ≤ 2 ^ 8 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (3::nat) ^ 5 ≤ 2 ^ 8 | 243 ≤ 256 | — | (rule five_trits_per_byte) | method |
