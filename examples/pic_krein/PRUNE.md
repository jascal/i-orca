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
- **`β_j = sup_v ¦c_j(v)¦`** is the conservative cost; computing it is `O(|V|)` per source (or bound it).
  The per-input signed-sum bound is tighter but only certifies that input.
- **Dimension vs. value.** Pruning *sources/dimensions* is here; the decode-side lossless *dimensional*
  floor is the frame rank (`Θ(d)`, `PIC_SPEC` §5/§6).
