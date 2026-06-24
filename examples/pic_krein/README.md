# PIC over a Krein space — a thought experiment (i-orca corpus)

A kernel-checkable exploration of what happens to **Projective Incidence Calculus**
(companion: `pic/spec/PIC_SPEC.md`) when its Euclidean residual geometry is replaced by an
**indefinite (Krein) inner product** `[x,y] = ⟨J x, y⟩`, where `J` is the *fundamental
symmetry* (`J` self-adjoint, `J∘J = id`, signature `(p,q)`) and `⟨·,·⟩` is the positive-definite
**majorant**.

> ⚠️ As everywhere in i-orca, a green `i-orca verify` certifies only that the proof *skeleton* is
> well-formed; **truth is the kernel's**. Each theorem here is discharged by `(rule <lemma>)` against
> a hand-authored Isabelle lemma in the `KreinPIC` session. This is a **thought experiment**, not part
> of the proved PIC corpus: it is an honest map of *which* PIC theorems are metric-free, which survive
> only in the majorant, and which break — not a claim that transformers are natively Krein.

## The idea in one line

`[d_j, U_v] = ⟨J d_j, U_v⟩`, so a Krein incidence is a Euclidean incidence of the **J-transformed
source**. The decode side (everything that flows into the semiring as a scalar logit) is therefore
**metric-free**; only the genuinely geometric **frame side** (capacity, Welch, coherence) feels the
signature. That split is exactly PIC's own frame/decode cut, now given a third axis: *metric-free vs
metric-dependent*. See [`PROPOSAL.md`](PROPOSAL.md).

## What the two halves say

| | result | meaning |
|---|---|---|
| **Decode (KreinDecode.thy)** | `krein_logit_definitize` | the PIC logit equals the Euclidean logit with `d'_j = J d_j` — monomials/argmax/semiring/margins transfer **verbatim** |
| | `kinner_majorant` | applying `J` twice recovers `⟨·,·⟩` — the "retreat to the majorant" escape hatch (and why a freely-absorbable `J` is trivial) |
| | `margin_pair_separation_k` | decode capacity (DecodeCapacity.thy) **survives** — *provided the residual ball is the majorant ball* |
| **Frame (KreinWelch.thy)** | `single_coord_self` | "unit norm" splits: features are spacelike (`+1`) or **timelike** (`−1`) |
| | `null_vector` | a non-zero **null token** (`[x,x]=0`) — a Krein-native intrinsically-composed proposition |
| | `kip_trace_eq_signature` | the Gram trace is the signature imbalance `p−q`, not the count `n` |
| | `krein_welch_driver_vanishes` | the Welch interference floor **degrades to `s²/|K|`**, vacuous at balanced signature |
| | `indefinite_ball_unbounded` | the indefinite pseudo-ball is non-compact — decode capacity **collapses** (timelike escape) |

## Layout

| File | Role |
|------|------|
| [`KreinDecode.thy`](KreinDecode.thy) | abstract `real_inner` + fundamental symmetry `J`: definitization, symmetry, majorant recovery, capacity-survives-in-majorant |
| [`KreinWelch.thy`](KreinWelch.thy) | coordinate signed inner product `kip s K` (mirrors `superposition/Welch.thy`'s `ip`): the signature phenomena — timelike units, null tokens, trace = signature, Welch degradation, ball unbounded |
| [`KreinBottomK.thy`](KreinBottomK.thy) | the bottom-K (min-plus) decode certificate — dual of `tropical/HeadTail.thy` — and bottom-K = top-K of the negated frame |
| [`KreinPrecond.thy`](KreinPrecond.thy) | Scheme A: an indefinite frame-update preconditioner is no reparametrization of SGD, the flow `U̇ = −J∇L` is not a descent flow, and the isotropic instability of minima |
| [`KreinTernary.thy`](KreinTernary.thy) | bridge to the `bitnet` corpus: ternary signature = tripotent degenerate fundamental symmetry (`Js³=Js`); value-system differences (integer/ternary robustness floor, finite `3^d` frame space) |
| [`ROOT`](ROOT) | Isabelle session `KreinPIC` (parent `HOL-Analysis`) |
| [`pic_krein.i.orca.md`](pic_krein.i.orca.md) | the i-orca surface: 31 theorems, each `(rule <lemma>)` |
| [`PROPOSAL.md`](PROPOSAL.md) | the motivation, the honest tag ledger, the QK / quantum-informational connections (flagged speculative), open targets |
| [`SCHEME_A.md`](SCHEME_A.md) | Scheme A dynamics (saddle-seeking, not descent) and the verification-intact min–max / annealing training recipe |
| [`LEARNED_J.md`](LEARNED_J.md) | adaptive / learned `J`: parametrizations (signature `s`, Grassmannian), the descent-iff-PSD dichotomy (saddle-free-Newton tension), and the two well-posed regimes |
| [`TERNARY.md`](TERNARY.md) | ternary ↔ `bitnet` ↔ PIC ↔ Krein-PIC: ternary-as-data (standard PIC) vs ternary-as-metric (degenerate Krein), and the provable ternary/integer/float value-system differences |
| [`RESULTS.md`](RESULTS.md) | verification status and commands |

## Verify

```bash
# Layer 1 — structural skeleton (zero Isabelle)
.venv/bin/i-orca verify examples/pic_krein/pic_krein.i.orca.md
#   -> all 31 theorems VALID, formal_fraction_static = 1.000

# Layer 2 — kernel check of the substrate (the load-bearing math)
isabelle build -d examples/pic_krein -o quick_and_dirty KreinPIC
#   -> Finished KreinPIC, zero sorry
```

## What it shows (and what it doesn't)

It **proves**: the decode-side definitization and capacity-survival (the metric-free half), and the
frame-side signature phenomena (timelike units, a null token, trace = signature, the Welch-floor
*driver* vanishing at balanced signature, and non-compactness of the indefinite ball).

It **does not** prove: that small total coherence with `n > d` features is *achievable* in an
indefinite frame (the Welch result here degrades the *guarantee*, not the *geometry* — Krein
orthonormal sets are still linearly independent, hence capped at `d`); that any real transformer
pairing (e.g. the QK bilinear form, whose symmetric part is generically indefinite) actually carries a
non-trivial signature (a `fieldrun` measurement, `[open/empirical]`); and anything in the
quantum-information analogy of [`PROPOSAL.md`](PROPOSAL.md), which is a structural conjecture, not a
theorem.
