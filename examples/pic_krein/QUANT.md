# Within-tolerance lossless compression for *any* PIC system — geometry + the margin certificate

Can geometry (packing / quantization) give a *within-tolerance lossless* compression that works for any
PIC system — float, int, or ternary weights, Euclidean or Krein? **Yes.** Kernel anchor: `PIC_Quant.thy`.

## What "within-tolerance lossless" means

**Decode-lossless.** The compressed (quantized) frame produces the **exact same decoded token** as the
original, and the equality is *certified* — even though the weights are lossy at the bit level. Only the
softmax *probabilities* move within the tolerance; the *decision* (the argmax, and every margin theorem
of §5) does not. This is "lossless" in the only sense the model's output cares about.

It is also **value-system- and metric-agnostic**: everything below is about the scalar logits, so it
holds for float / int / ternary weights and for PIC *and* Krein-PIC alike. The number system is just the
*alphabet of the quantization cells*; the **geometry sets the rate**.

## The mechanism (three kernel-checked lemmas)

1. **`margin_certified`** — the margin certificate (`PIC_SPEC` §5.5), self-contained: if the winner `t`
   beats every competitor by `≥ m`, every logit moves by `≤ δ`, and `2δ < m`, then `t` is still the
   strict winner. *(A `δ`-perturbation cannot flip a `>2δ` margin.)*
2. **`frame_quant_logit_bound`** — Cauchy–Schwarz: quantizing a frame vector `U → Ũ` perturbs its logit
   `⟨r,U⟩` by `≤ ‖r‖·‖Ũ−U‖`. So an `ε`-cell quantization with `‖r‖ ≤ ρ` moves every logit by `≤ ρε`.
3. **`quant_decode_preserved`** — the composition, the **within-tolerance lossless compression theorem**:
   quantize the frame to per-token cell size `‖Ũ_v − U_v‖ ≤ ε` (on *any* grid), `‖r‖ ≤ ρ`; if the
   original margin exceeds `2ρε`, the **quantized decode equals the original**, exactly and certified.

## The rate — geometry / packing  `[engineering, not formalized]`

To place each frame vector within `ε` inside a radius-`ρ` ball needs about `(ρ/ε)^d` cells, i.e.

> **bits / vector ≈ `d · log₂(ρ/ε)`**   (the `ε`-covering number — the packing bound of `DecodeCapacity`, Cor 5.1)

and with `ε` set by the margin budget (`ε < margin/(2ρ)`):

> **bits / vector ≈ `d · log₂(2ρ² / margin)`**.

So the **coarser the tolerance the margin allows, the fewer bits**. This makes the compression
**heterogeneous and margin-aware**:

- **High-margin (head) tokens** (`PIC_SPEC` §5.4) tolerate coarse cells → compress hard.
- **Small-margin (tail / forge-tax residue) tokens** force a tiny `ε` → cost the most bits, exactly where
  the decode is least certain. Compression is hardest precisely on the uncertified residue.

The value system chooses how the `ε`-cells are *encoded* (binary for int/float, base-3 for ternary —
`ternary_byte_packing` packs a chosen ternary grid at ≈1.58 bits/cell), but the *number* of cells (the
rate) is geometric.

## Why this beats bit-exact lossless

`ternary_widen_lossless` (bit-exact) is **bit-neutral** — it re-encodes without compressing. The
within-tolerance scheme **spends bits only down to the margin budget**, exploiting the decode's slack, so
it genuinely compresses. The trade is explicit and certified: you pay in tolerance (`2ρε < margin`) and
get the exact decode back.

## Honest scope

- **Lossless at the decode (argmax), not the softmax.** Probabilities/entropy (the `T`-dependent part,
  §3.1) move within tolerance; the decision and all §5 margin theorems are exact. State it as
  *argmax-lossless / margin-certified*, not *probability-lossless*.
- **Worst-case bound.** `δ = ρε` is Cauchy–Schwarz (worst-case over residual direction); the actual
  residuals usually allow more aggressive `ε`. `ρ` is a uniform residual-norm bound.
- **Rate is `[engineering]`.** `margin_certified`, `frame_quant_logit_bound`, `quant_decode_preserved`
  are kernel-proved; the `d·log₂(ρ/ε)` covering-number rate is the standard packing estimate (Cor 5.1),
  not separately mechanized here.
- **Dimensional floor.** Quantizing values does not reduce dimension; lossless *dimensional* compression
  is bounded by the frame rank — the `Θ(d)` frozen-compression floor of `PIC_SPEC` §5/§6.
