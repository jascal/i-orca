# Ternary, bitnet, PIC, and Krein-PIC — connections and provable value-system differences

Is a ternary `{−1, 0, +1}` structure best described by PIC or by Krein-PIC? It depends on whether the
ternary lives in the **data** or in the **metric** — and along the way there are *provable* differences
between ternary / integer / float value systems. Kernel anchors: `KreinTernary.thy` (this tree) and the
`examples/bitnet` corpus (BitNet b1.58, arXiv:2402.17764).

## 1. Ternary as DATA → standard PIC (no Krein needed)

If `{−1,0,1}` is in the *vectors* (ternary weights / unembedding rows, BitNet style), standard Euclidean
PIC already covers it — the incidence `⟨d, U⟩` is a signed real, so `+ / − / 0` outcomes need no
indefinite metric. The bitnet corpus is exactly this, in the Euclidean setting:

- `Ternary.tprod` / `tprod_is_mult` — a ternary weight acts as `+x, 0, −x` (no multiply).
- `Ternary.ternary_dot_signed_sum` — a ternary incidence **is a multiplication-free signed sum**:
  `Σᵢ wᵢ xᵢ = Σ_{wᵢ=+1} xᵢ − Σ_{wᵢ=−1} xᵢ`. This is the PIC monomial `⟦S⟧(v)` with ternary sources.
- `Ternary.roundclip_not_injective` — per-weight ternarization is **lossy** (the honest counterpoint).
- `BalancedTernary.balanced_ternary_exists` — every integer is `Σⱼ tⱼ 3ʲ`, `tⱼ ∈ {−1,0,1}`; so an
  **integer frame is a lossless power-of-3 stack of ternary frames** (`Lossless.lossless_realization`).
- `BitWidth` — `log₂3 ∈ (1.5,1.6)`: ≈1.58 bits/coordinate.

## 2. Ternary as a SIGNATURE / metric → degenerate Krein-PIC

If `{−1,0,1}` is in the *metric* (`s_b ∈ {−1,0,1}` in `KreinWelch`'s form `[x,y] = Σ_b s_b x_b y_b`),
it is **not strict Krein**: the fundamental symmetry is *binary* (`J² = I` forces eigenvalues `±1`;
`Js_involution` needs `s² = 1`). The zeros make the form **degenerate** — a *Krein space with a radical*.

- **`Js_tripotent`** (`s³ = s ⟹ Js∘Js∘Js = Js`): the ternary law. The three real roots of `s³ = s` are
  exactly `{−1,0,1}`, so the balanced-ternary value set *is* the solution set of the tripotent law — the
  ternary analogue of the Krein involution `Js∘Js = id`.
- **`Js_sq`** (`Js∘Js = ` multiply-by-`s²`): for ternary `s`, `s² ∈ {0,1}` is the support indicator, so
  `Js∘Js` is the projection onto `{b : s_b ≠ 0}` and the **radical** is `{b : s_b = 0}`.
- So a ternary signature is the full **Sylvester inertia triple `(p,q,z)`** — `p` spacelike, `q`
  timelike, `z` null-in-the-radical — one notch more general than Krein's `(p,q)`.

**The bridge:** a bitnet ternary *weight* vector and a Krein ternary *signature* are the **same**
`{−1,0,1}^d` object, characterized by the same tripotent law `Js³ = Js`. The three ternary values are the
three inertia classes: `+1` spacelike (promote), `−1` timelike (suppress), `0` null/radical (neutral).

## 3. Provable value-system differences (decode-side, hence metric-free)

These are about the *number system*, not the metric, so they hold in PIC and Krein-PIC alike.

| property | ternary `{−1,0,1}` | integer `ℤ` | float `ℝ̃` |
|---|---|---|---|
| incidence | signed sum, multiplication-free, **exact** | exact sum | **rounded**, `δ > 0` |
| frame space | **finite, `3^d`** (`card_ternary_frame`) | countable (bounded: `(2B+1)^d`) | continuum |
| achievable margins | `0` or `≥ 1` (a **gap**) | `0` or `≥ 1` (gap) | dense in `ℝ₊` (no gap) |
| robustness from a strict win | survives any `δ < ½` (`int_strict_winner_robust`) | survives any `δ < ½` | none — depends on the margin |
| margin-certificate `2δ` band | empty above ties | empty above ties | a continuum-wide uncertified band |
| as a metric/signature | tripotent, degenerate (`Js³=Js`) | 3-adic stack of ternary (balanced-ternary) | general real symmetric (strict Krein) |
| bits / coordinate | `log₂3 ≈ 1.58` | `log₂(2B+1)` | 16 / 32 |
| lossless from higher precision | by 3-adic expansion (`balanced_ternary_exists`) | exact | (is the source) |

The two **kernel-checked** differences:

- **`int_strict_winner_robust`** — integer (hence ternary-incidence) logits have a *robustness floor*: a
  strict winner beats the field by `≥ 1`, so it survives **any** real perturbation `< ½`, no matter how
  close the runner-up. This is the proved margin certificate (the `2δ` threshold) with `δ < ½ < 1 ≤`
  margin. **Float has no floor** — a strict win by `ε` is not robust to `ε` noise — so float leaves a
  continuum-wide uncertified small-margin band that exact (ternary/integer) arithmetic does not. (This is
  the *decode-side* face of "exactness": ternary↔ternary and integer incidences are computed without
  rounding, so the certificate's representational `δ` is `0`.)
- **`card_ternary_frame`** — the ternary frame space is **finite, exactly `3^d`**; decode packing is then
  a finite ternary-coding question, not the continuous covering number `(1 + 2ρ/γ)^d` of
  `DecodeCapacity`. The float frame space is a continuum.

## 4. Verdict

- **Ternary data / weights** → best in **standard PIC** (signed incidence; `bitnet` formalizes it). Krein
  is not needed for the data.
- **Ternary metric / signature** → best in a **degenerate Krein-PIC** ("Krein with a radical", inertia
  triple `(p,q,z)`, `Js³ = Js`). Strict Krein can't represent the genuine `0`; Euclidean can't represent
  the `−1`; the ternary signature needs both, so it is the natural home only when your *metric* (not your
  data) is three-valued.
- **The symmetry you sense** is real and precise: it is the inertia trichotomy `+ / − / 0`, the same
  three-fold object whether read as a ternary weight or as a degenerate signature.

## 5. Lossless conversion to ternary — by *adding dimensions*

Per-weight ternarization (rounding into `{−1,0,1}`) is **lossy** (`Ternary.roundclip_not_injective`).
But with **dimension expansion** it is exact (`ternary_widen_lossless`): expand each integer weight into
its `K` balanced-ternary digits `w_j = Σ_{k<K} t_{jk} 3^k` (digits in `{−1,0,1}` exist by
`BalancedTernary.balanced_ternary_exists`), and the incidence rearranges as

> `⟨w, x⟩ = Σ_{k<K} 3^k · ⟨t_{·k}, x⟩`

— a fixed power-of-3 combination of `K` **ternary** incidences `⟨t_{·k},x⟩`, the `K` "trit-plane" hidden
dimensions added to the layer. The only non-ternary part is the fixed `3^k` read-out (no learned,
non-ternary weights). So:

- **Integer model → ternary, lossless, at a `K`-fold width blow-up**, `K = ⌈log₃(value range)⌉`.
- **Finite-precision fp model → ternary, lossless**: an fp weight is `mantissa × 2^exp`, so a finite set
  of fp weights is *integers × a common `2`-power scale*; clear to integers, convert as above, and the
  scale is **one fixed global multiplier**. (Genuinely infinite-precision reals are **not** finitely
  ternary-representable — balanced ternary terminates only for base-3 rationals.)

## 6. Lossless compression of a ternary frame

Yes — and it's the *storage* (bit) sense, provable:

- **Bit packing** (`ternary_byte_packing`, mirrors `bitnet.five_trits_per_byte` / `log2_3_approx`): a
  ternary frame packs losslessly at **5 trits/byte** (`3^5 = 243 ≤ 256 = 2^8`), ≈ **1.58 bits/weight** —
  a ~10–20× lossless storage compression over fp16/fp32. So a *natively-ternary* frame is compressible.

Three honest caveats on *where the compression comes from*:

1. **Conversion is bit-neutral.** Converting fp/int → ternary via §5 is **not** bit-compressing: the
   `K`-fold width expansion exactly offsets the per-weight bit drop (`K` trits = `log₂(range)` bits = the
   original integer's bits). Ternary **surfaces** the model's redundancy; it doesn't create compression.
2. **Below ~1.58 bits needs structure.** Trained ternary nets are *sparse* (mostly `0`), so the frame's
   entropy is `< log₂3`, and entropy coding compresses further — but **only down to the Shannon entropy**
   of the frame (no lossless scheme beats it).
3. **Decode-side floor is rank.** The frame matters only through the logits, so lossless
   decode-preserving compression is bounded below by the frame **rank** — the `Θ(d)` frozen-compression
   floor of `PIC_SPEC` §5/§6 (a rank-bottlenecked *retrained* update clears it; frozen compression does
   not). This floor is metric- and value-system-agnostic.

So: **lossless compression of a ternary frame exists and is provable at the bit level (≈1.58 bits/weight);
beyond that it is bounded by the frame's entropy (storage) and its rank (decode), and ternary conversion
itself is bit-neutral — the compression is the model's redundancy, surfaced by ternary, not created.**

## 7. Resource requirements & likely CPU runtime  `[engineering estimates]`

These are order-of-magnitude estimates (assumptions stated), not kernel results.

**Conversion (one-time, offline).** Balanced-ternary expansion is `O(n·K)` integer div/mods (`K` trits
per weight), `K = ⌈log₃(range)⌉`. For a 7B model that's `~7e9·K` cheap integer ops — seconds to a few
minutes on one CPU core; negligible. `K` itself: int8 → `K≈6`; fp16 → `K≈16` once you clear the
*exponent spread* to a common integer scale (the exponent range, not just the 11-bit mantissa, sets `K`).

**Storage.** Native ternary packs at ≈1.58 bits/weight (`ternary_byte_packing`): a 7B model is ~1.4 GB
vs 14 GB (fp16) — **~10× compression**. But a *losslessly converted* model is the `K` trit-planes:
`K·1.58` bits/orig-weight ≈ the original bit-width (the proved **bit-neutrality**), and with the `⌈·⌉`
waste it can be *larger* (int8→ternary ≈ 9.5 bits > 8; fp16→ternary ≈ 25 bits > 16). So **lossless
conversion of a dense int/fp model does not save storage** — the ~10× win is for *natively-ternary*
(BitNet-trained, lossy) models.

**CPU inference runtime.** Single-batch LLM decode on CPU is **memory-bandwidth-bound** (weights streamed
from RAM each token). The ternary matmul is *multiplication-free* (`Ternary.ternary_dot_signed_sum`: a
signed sum), so the win is bandwidth, not FLOPs (integer add ≈ multiply ≈ 1 cycle on modern cores):
- *Native ternary*: ~10× less weight traffic → up to ~10× throughput at the bandwidth limit; real
  LUT/SIMD kernels (e.g. `bitnet.cpp`) land ~**5–6×** after kernel overhead. (e.g. 7B: ~280 ms/token
  fp16 → ~30–50 ms/token ternary at ~50 GB/s.)
- *Lossless-converted*: **no speedup.** Bit-neutrality applies to bandwidth too (`K` planes ≈ original
  bits streamed), *plus* `K`-plane accumulation overhead (the `3^k` shifts/adds) and worse cache
  locality — so it is *slower* than the int/fp original. Useful only if you specifically need ternary
  kernels with exact outputs (niche).
- *Decompression* (unpack 5-trits/byte) is a few ops/weight, fused into the GEMV or done once at load —
  negligible.

**The tension (= the proved bit-neutrality, operationally).** From a dense fp model you get **lossless
*or* compressed/fast, not both.** Lossless conversion preserves bits → no storage/runtime win; the
compression-and-speed win needs the *lossy* native-ternary path, or genuine model redundancy (sparse
ternary → skip-zero kernels and entropy coding; low rank → factor first). Ternary *surfaces* redundancy;
it doesn't manufacture a free lunch.

### Worked sizing example (reusable formulas)

Two numbers decide everything for single-batch (batch-1) CPU decode of a **dense** model:

> **footprint** = `bits_per_weight · params / 8`         **decode tok/s** ≈ `sustained_RAM_BW / footprint`

(decode streams every weight once per token, so it is RAM-bandwidth-bound; cores only need to be enough
to saturate the bus and run the signed-sum). `bits_per_weight`: fp16 `16`, int8 `8`, int4 `4`, **native
(lossy) ternary `1.58`**, and **lossless ternary ≈ the source's bit-width** (bit-neutral, often worse).

**Instance: 300B dense model, 96 cores, 251 GB RAM** (assume ~250–450 GB/s sustained, ~350 central):

| representation | bits/wt | footprint | fits 251 GB? | decode tok/s (~350 GB/s) |
|---|---|---|---|---|
| fp16 (source) | 16 | 600 GB | no | (0.6) |
| int8 | 8 | 300 GB | no | (1.2) |
| **lossless ternary** (from fp16) | ~16–25 | ~600–940 GB | **no** | — |
| **lossless ternary** (from int8) | ~9.5 | ~356 GB | **no** | — |
| native ternary (**lossy**) | 1.58 | **~59 GB** | **yes** (+~190 GB for KV/acts) | **~4–8** (≈6) |
| int4 (lossy) | 4 | 150 GB | yes | ~2–3 |

Read-off: **lossless ternary does not fit** — it inherits the fp16 size (the proved bit-neutrality), and
would run *slower* than fp16 even if it fit. The only thing that fits-and-goes-fast is the **lossy**
native-ternary path (~59 GB, ~6 tok/s decode; prefill is compute-bound and faster). For a *lossless*
300B you need ≥~640 GB of RAM (or SSD offload → <0.1 tok/s, impractical). The 96 cores are not the
limit at any precision here — RAM bandwidth is.

## Honest status

`Js_tripotent`, `Js_sq`, `int_strict_winner_robust`, `card_ternary_frame` are **[proved]** here; the
`bitnet` lemmas cited are **[proved]** in `examples/bitnet`. That a real model *wants* a ternary metric
(rather than ternary data) is **[open/empirical]** — `bitnet` ternarizes the *weights/data*, and whether
an explicitly ternary *signature* buys anything is unmeasured.
