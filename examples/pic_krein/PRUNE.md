# Certificate-gated pruning — algorithms with provable within-tolerance outcomes

Pruning a PIC model (dropping sources / blocks / dimensions / tokens) with a **provable** guarantee that
the decode is unchanged. Kernel anchors: `PIC_Prune.thy` (source-side prune certificate), `PIC_Quant.thy`
(quantization + the underlying margin certificate), `tropical/HeadTail.thy` (exact head/tail).

## The principle: gate the search on the certificate

Every algorithm here is **certificate-gated** — it only emits a prune set `P` for which the
within-tolerance condition holds, so the proved certificate *certifies the outcome*. **Correctness is
decoupled from the search**: the algorithm may use any heuristic; as long as its output satisfies the
hypothesis, `prune_decode_preserved` (or its budget form) fires.

The condition, two forms (both proved):

> **exact, per-input** (`prune_decode_preserved`): `∀v. ¦Σ_{j∈P} c_j(v)¦ ≤ δ` and `2δ < m` ⇒ decode preserved.
> **budget** (`prune_budget_decode_preserved`): `2·Σ_{j∈P} β_j < m` with `¦c_j(v)¦ ≤ β_j` ⇒ decode preserved.

Here `c_j(v) = ⟨d_j, U_v⟩` is source `j`'s incidence on candidate `v`, `m` the margin to preserve, and
`β_j = sup_{v∈V} ¦c_j(v)¦` the per-source cost. The budget `Σ_{j∈P} β_j` is **monotone** in `P`
(`prune_budget_mono`), so the certifiable prune sets are downward-closed — greedy is well-founded.

## Algorithm A — greedy magnitude prune  *(provably max-count)*

```
beta_j := max_{v in V} |c_j(v)|              # per-source cost (O(|V|) per source)
B := (m - eps) / 2                           # half the margin to preserve (eps slack)
sort sources ascending by beta_j
P := {}; running := 0
for j in sorted order:
    if running + beta_j <= B:  P += j;  running += beta_j
    else: break
return P
```

- **Guarantee** (`prune_budget_decode_preserved`): `2·running < m` ⇒ decode preserved, certified.
- **Optimality**: smallest-`β` first **maximizes the prune count** under the `Σβ ≤ B` budget (a standard
  exchange argument; stated, not mechanized).
- **Tighter per-input variant**: replace the `β`-budget by the actual signed sum `¦Σ_{j∈P} c_j(v)¦`
  (exploits cancellation, certified per-input by `prune_decode_preserved`) — prunes more on a given input.

### Worked example (Algorithm A, end-to-end)

64 sources (DLA blocks); certified margin `m = 2.0` (logits). Per-source costs `β_j = max_{v∈V}¦c_j(v)¦`:
50 "small" sources at `β = 0.01`, 14 "large" at `β = 0.30`. Budget: `Σβ < m/2 = 1.0`.

1. Sort ascending; add all 50 small → `running = 0.50`.
2. Add large (0.30 each): `0.50 + 0.30 = 0.80 < 1.0` (add 1); `0.80 + 0.30 = 1.10 ≥ 1.0` (stop).
3. **Prune set** `P` = 50 small + 1 large = **51 of 64 sources**, `Σ_{j∈P} β_j = 0.80`.
4. **Certificate check**: `2·Σβ = 1.60 < 2.0 = m` ✓ → `prune_budget_decode_preserved` fires → **decode preserved, certified**.

Outcome: ~80% of sources dropped with a kernel-checked guarantee the decode is unchanged. (The per-input
signed-sum variant usually certifies even more, via cancellation.)

## Algorithm B — head/tail structural prune  *(exact, δ = 0)*

Keep the dominating head (the sources/tokens whose tropical value dominates the rest), drop the tail.

- **Guarantee** (`HeadTail.head_certifies_decode`, already proved): when the head dominates the tail, the
  pruned decode equals the original **exactly** — no tolerance needed. This is the measured "sparse decode
  head" (median 1–3 late-MLP blocks reproduce the decode); the tail is the explicit, uncertified residue.

## Algorithm C — knapsack utility prune  *(maximize savings)*

Each source has a saving `w_j` (FLOPs/bytes) and cost `β_j`; **maximize `Σ_{j∈P} w_j` s.t.
`2·Σ_{j∈P} β_j < m`**. This is 0/1 knapsack (NP-hard; use greedy-by-`w_j/β_j`, or DP for pseudo-poly).

- **Guarantee**: the certificate holds for *any* feasible `P`, so the optimizer is free to use any
  heuristic — the within-tolerance outcome is provable regardless of how good the search is.

## Algorithm D — iterative prune → optimize → re-certify

```
repeat:
   P := greedy/knapsack prune (A or C)
   fine-tune the pruned model to shrink the residual logit error
   measure delta := max_v |L'(v) - L(v)|   # post-hoc, on the actual model
   accept if 2*delta < m  (else roll back the last batch)
```

- **Guarantee**: the certificate is **post-hoc** — it certifies the (original, final) pair regardless of
  how the final model was produced. So fine-tuning that *reduces* `δ` strictly enlarges the certifiable
  set. Prune + rewrite + quantize can all run inside this loop.

## Algorithm E — unified budget across operations

Quantize (`δ_q = ρε`, `PIC_Quant`), prune (`δ_p = Σ_{j∈P} β_j`), low-rank rewrite (`δ_r = ‖r‖‖ΔU‖`):
by the triangle inequality the total logit drift is `≤ δ_q + δ_p + δ_r`, so **one certificate** covers a
*mix* of compression operations: `2·(δ_q + δ_p + δ_r) < m` ⇒ decode preserved (each piece bounded by its
own lemma; `margin_certified` fires on the sum). This is why the scheme is method-agnostic — the
certificate sees only the total perturbation.

## Relationship to `PIC_Quant` — one certificate, three operations

The whole "certified compression" story is **one margin certificate** (`margin_certified`) consumed by
three perturbation bounds. Each operation only has to bound its own logit drift `δ`; the certificate fires
on the **sum**:

| operation | what it edits | logit drift `δ` | bound lemma | certificate |
|---|---|---|---|---|
| **quantize** | weights (frame `U`) to `ε`-cells | `‖r‖·‖Ũ−U‖ ≤ ρε` | `frame_quant_logit_bound` (`PIC_Quant`) | `quant_decode_preserved` |
| **low-rank rewrite** | frame `U ≈ AB` | `‖r‖·‖Ũ−U‖` (same bound) | `frame_quant_logit_bound` | `quant_decode_preserved` |
| **prune** | drop sources `P` | `¦Σ_{j∈P} c_j(v)¦ ≤ Σβ_j` | `prune_dropped_le_budget` (`PIC_Prune`) | `prune_decode_preserved` |
| **mix (all three)** | any combination | `≤ δ_q + δ_p + δ_r` (triangle) | the three above | `margin_certified` on the sum |

Read top-to-bottom it is the full pipeline: rewrite to low rank, prune the now-redundant sources,
quantize the survivors — each step spends part of one shared budget `2·(δ_q+δ_p+δ_r) < m`, and the decode
is preserved with a single kernel-checked certificate.

## Compatibility with the rest of the tree (Scheme A, learned `J`, Krein)

The certificate is on the **scalar logits**, so it is indifferent to how the frame was produced or which
metric reads it:

- **Scheme A / learned `J` (PR #18):** these change *training dynamics* (the frame-update preconditioner)
  or the *metric*, not the certificate's hypothesis. Prune/quantize the **final** frame and certify
  post-hoc (Algorithm D's logic) — pruning composes with any training regime.
- **Krein / indefinite metric:** the logit is `[r,U_v] = ⟨Jr,U_v⟩`, still a scalar; pruning source `d_j`
  perturbs it by `[d_j,U_v]`, bounded the same way. So all certificates here apply verbatim in Krein-PIC
  (decode is metric-free, `KreinDecode`).

## What is proved vs. algorithmic

- **Proved (kernel)**: the certificates — `prune_decode_preserved`, `prune_budget_decode_preserved`,
  `prune_dropped_le_budget`, `prune_budget_mono`, `prune_logit_delta` (`PIC_Prune`),
  `quant_decode_preserved`, `margin_certified` (`PIC_Quant`), `head_certifies_decode` (`HeadTail`).
- **Algorithmic** (the search): greedy / knapsack / iterative — each *emits* a certificate-satisfying `P`,
  so its **outcome** is provably within tolerance; greedy's max-count optimality and knapsack's heuristics
  are standard combinatorics, stated not mechanized.

## Honest caveats

- **Local / per-input.** `m`, `β_j`, `δ` depend on the residual `r` and the candidate set `V` at a given
  input. A *global* guarantee needs `ρ = sup‖r‖` and the worst-case margin over the input distribution —
  the measurement/engineering part (the §5.5 "local certificate" caveat).
- **Argmax-lossless, not softmax-lossless.** The decision is exact; probabilities move within tolerance.
  *Practical implication*: safest for **argmax / greedy decoding and retrieval** (top-1 is provably
  unchanged); for softmax-probability-sensitive uses (temperature/nucleus sampling, calibrated
  confidences, log-prob scoring) the *distribution* shifts within `δ` and should be validated separately
  (or compressed to a tighter `δ`).
- **`β_j = sup_v ¦c_j(v)¦`** is the conservative cost; computing it is `O(|V|)` per source (or bound it).
  The per-input signed-sum bound is tighter but only certifies that input.
- **Dimension vs. value.** Pruning *sources/dimensions* is here; the decode-side lossless *dimensional*
  floor is the frame rank (`Θ(d)`, `PIC_SPEC` §5/§6).

## Empirical targets (future work)  `[open]`

Everything here is formal + algorithmic; none is measured. Natural validation, in increasing cost:
prune ratio at zero decode change vs. unstructured / magnitude pruning on small models (the certificate
predicts the *guaranteed-safe* ratio); the certified head size (Algorithm B) vs. the measured 1–3-block
decode head; how much the per-input signed-sum slack beats the `β`-budget in practice; and the unified
prune+quant+rewrite ratio at a fixed `δ`. The `fieldrun --pil-dump` seam already emits the incidences
`c_j(v)` these algorithms need, so the budgets are computable on real models without retraining.
