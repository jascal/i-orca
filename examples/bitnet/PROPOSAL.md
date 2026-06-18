# BitNet b1.58 / ternary weights — proposal

The sixth entry in i-orca's **"canonical proofs from other authors"** track (after the
Aaronson watermark, tropical geometry of ReLU networks, Toy Models of Superposition,
Johnson–Lindenstrauss, and TurboQuant): a kernel-checked formalisation of the structural
math of **ternary-weight LLMs (BitNet b1.58)**, built around a concrete theoretical
question — *can a finite-precision network be transformed into a ternary one losslessly?*

**Source.** Ma, Wang, Ma, Wang, Wang, Huang, Dong, Wang, Xue & Wei, *"The Era of 1-bit
LLMs: All Large Language Models are in 1.58 Bits"*, Microsoft Research, arXiv:2402.17764,
2024.

## The idea

BitNet b1.58 makes **every weight ternary** `{−1, 0, 1}` (so ≈ `log₂3 ≈ 1.58` bits each).
A ternary weight matrix needs **no multiplications** — the matmul is a signed sum. Weights
come from an **absmean RoundClip** quantizer:

```
        W~ = RoundClip(W / (γ + ε), −1, 1),   RoundClip(x,a,b) = max(a, min(b, round x)),
        γ = mean |W_ij|.
```

## The lossless question (and the answer this corpus proves)

> *Is a lossless transformation of a trained network into a BitNet (ternary) one
> theoretically possible — e.g. via a relational / Datalog encoding, as an analytical
> optimisation problem?*

The corpus answers it precisely:

- **Per-weight ternarization is necessarily lossy.** `roundclip` is non-injective
  (`0.3` and `0.4` both map to `0`), so it has no inverse: you cannot recover a real (or
  16-bit) weight from one trit. A trit holds only `log₂3` bits.
- **But a lossless realization exists by EXPANSION.** Every integer (hence every
  finite-precision) weight has a **balanced-ternary** expansion `w = Σⱼ tⱼ·3ʲ`,
  `tⱼ ∈ {−1,0,1}` (`balanced_ternary_exists`). Distributing those digits through the matmul
  (`lossless_realization`) gives the integer-weight layer's **exact output** as a
  power-of-3 weighted sum of *ternary* matmuls. The network's function is preserved
  exactly; only the representation expands (by `K ≈ precision / log₂3` trits per weight).
- **The Datalog framing is sound, and locates the hard part.** A finite-precision network
  is finite-state arithmetic, expressible relationally (Datalog with bounded-integer
  aggregation). The ternarization is then a *deterministic, lossless* rewrite (replace each
  integer-weight fact by its balanced-ternary digits; replace matmul rules by summed
  ternary-matmul rules). Existence of a lossless ternary net is therefore easy; the
  genuine **optimisation** is *minimising the expansion* — the sparsest behaviourally-
  equivalent ternary net (exactly, or within ε on a dataset) — which is NP-hard in general
  (an integer program / MaxSAT-shaped problem over the relational form).

So: **yes, lossless transformation is possible** (as behavioural equivalence by expansion),
and the relational/Datalog route makes it analytical — but the value is in optimising the
blow-up, not in existence.

## What is formalised (and the formal-vs-meta split)

Four theories, nine surfaced theorems:

| # | i-orca theorem | Isabelle lemma | Proves (formal) | Supports (meta) |
|---|----------------|----------------|------------------|------------------|
| 1 | TernaryProductIsMultiplication | `tprod_is_mult` | a ternary weight gives `+x`, `0`, or `−x` | the atomic mult-free op |
| 2 | TernaryDotIsSignedSum | `ternary_dot_signed_sum` | ternary dot = (Σ over +1) − (Σ over −1) | **mult-free matmul** |
| 3 | QuantizerIsTernary | `roundclip_ternary` | `roundclip x ∈ {−1,0,1}` | absmean maps into the ternary set |
| 4 | QuantizerNotInjective | `roundclip_not_injective` | the quantizer collapses distinct values | **per-weight ternarization is lossy** |
| 5 | BalancedTernaryExists | `balanced_ternary_exists` | every integer `= Σⱼ tⱼ·3ʲ`, `tⱼ ∈ {−1,0,1}` | **lossless-by-expansion crux** |
| 6 | LosslessRealization | `lossless_realization` | integer matmul `=` Σⱼ 3ʲ·(ternary matmul) | **lossless ternary layer** |
| 7 | LosslessWeight | `lossless_weight` | every `w·x = Σⱼ 3ʲ·(tⱼ·x)`, `tⱼ` ternary | the unconditional single-weight form |
| 8 | TernaryBitWidth | `log2_3_approx` | `1.5 < log₂3 < 1.6` | **the ≈1.58 bits** |
| 9 | FiveTritsPerByte | `five_trits_per_byte` | `3⁵ ≤ 2⁸` | five trits pack into a byte |

The **meta** column is deliberately not claimed as proven. The lossless realization is for
*finite-precision (integer)* weights and exact arithmetic; it says nothing about lossless
recovery of the original *real-valued* training, which is impossible (theorem 4).

## Honest reckonings

- **Lossless = behavioural exactness for finite precision.** `lossless_realization` /
  `lossless_weight` reproduce the integer-weight layer's *exact* output via ternary
  matmuls. They do not claim a *same-size* ternary net (the expansion is real) nor lossless
  recovery of real weights (theorem 4 rules that out).
- **Balanced ternary, kernel-checked.** `balanced_ternary_exists` is proved from scratch by
  strong induction on `|n|` (extract the balanced residue `((n+1) mod 3) − 1 ∈ {−1,0,1}`,
  recurse on `(n+1) div 3`), not assumed.
- **The 1.58 constant is genuine but loose.** `log2_3_approx` proves `1.5 < log₂3 < 1.6`
  (true value ≈ 1.585); the bound reduces to the integer comparisons `2³ < 3²` and
  `3⁵ < 2⁸`. A tighter bracket would need much larger integer powers.
- **Quantizer modelled, not the training.** `roundclip` is the absmean RoundClip map; the
  scaling `γ = mean|W|` and the straight-through-estimator training are out of scope.
- **The Datalog encoding itself is not formalised.** The relational rewriting argument is
  the meta narrative; what is kernel-checked is the algebra it rests on (balanced-ternary
  decomposition + the matmul distribution).

## Milestones / open targets

1. **(done)** The nine-theorem development above — all kernel-checked under Isabelle2025-2
   (`isabelle build -D examples/bitnet BitNet`, exit 0, zero `sorry`). See [`RESULTS.md`](RESULTS.md).
2. The uniform-`K` multi-weight lossless layer: a single `K` (max digit count) across a
   whole weight matrix, giving the full `Wx = Σⱼ 3ʲ Tⱼx` with `Tⱼ` ternary matrices.
3. Balanced-ternary **uniqueness** and the minimal digit count (the `K ≈ precision/log₂3`
   expansion factor as a theorem).
4. The relational / Datalog encoding of a finite-precision layer, and the lossless
   rewriting as a formal program transformation — turning "minimise the expansion" into a
   stated optimisation objective.
5. An `ε`-lossless variant: exact preservation of behaviour on a finite dataset with a
   smaller ternary net (the practically relevant relaxation).
