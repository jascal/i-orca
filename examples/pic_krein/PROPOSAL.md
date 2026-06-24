# PIC over a Krein space — proposal & honest reckoning

**Track:** fieldrun / PIC thought experiments (sibling of `../tropical` DecodeCapacity/RoutingRank and
`../superposition` Welch). **Companion spec:** `pic/spec/PIC_SPEC.md`.

## Motivation

PIC fixes one incidence primitive: `j ▷ v = ⟨d_j, U_v⟩`, an inner product in a **Euclidean** residual
space. Every frame-side theorem (decode capacity, the Welch floor, cosine coherence) silently uses
*positive-definiteness* — but PIC never names it as a hypothesis. This corpus replaces the Euclidean
inner product with an **indefinite (Krein) form**

> `[x, y] = ⟨J x, y⟩`,  `J` the fundamental symmetry (`J = J* = J⁻¹`, signature `(p,q)`),

with `⟨·,·⟩` the positive-definite **majorant**, and asks the question that exposes the hidden
hypothesis: *which PIC theorems are metric-free, which survive only in the majorant, and which break?*

Two places make the indefinite reading more than a curiosity (both `[open/empirical]`, not proved here):

1. **The QK attention pairing.** Attention scores are `xᵀ W_Q W_Kᵀ x'`; the symmetric part of
   `W_Q W_Kᵀ` is generically **not PSD** and carries a fixed mixed signature. PIC models only the
   *decode* (unembedding) inner product, which is genuinely Euclidean — but a PIC that also covered
   query/key *incidence* would be working a natively indefinite form, and PSD-ifying it would discard
   structure.
2. **Indefinite / Lorentzian frames.** If token geometry is learned without a PSD constraint (indefinite
   kernels) or is explicitly Minkowski (hyperbolic / entailment-cone embeddings, signature `(1,d−1)`),
   the residual space *is* a Pontryagin space.

## The result, in one sentence

A Krein incidence is a Euclidean incidence of the **J-transformed source** (`[d,U_v] = ⟨J d, U_v⟩`),
so the **decode side is metric-free** and only the **frame side feels the signature** — which is
exactly PIC's own frame/decode cut, now equipped with a third axis: *metric-free vs metric-dependent.*

## The honest tag ledger (what this corpus formalizes)

| PIC item (spec §) | under Krein `[·,·]` | theorem here | tag |
|---|---|---|---|
| semiring, ⊕_T/⊗, Maslov, temp-invariance (§2,§3.1) | unchanged (scalar logits) | `krein_logit_definitize` | **proved** |
| symmetry of the Gram kernel (§1.1) | needs `J` self-adjoint | `kinner_sym` | **proved** |
| "absorb J" / majorant escape hatch | two-sided `J` = majorant | `kinner_majorant` | **proved** |
| decode capacity, Thm §5.1 | **survives in the majorant ball** | `margin_pair_separation_k` | **proved** |
| decode capacity, in the indefinite ball | **collapses** (timelike escape) | `indefinite_ball_unbounded` | **proved** |
| unit norm / cosine coherence (§4.2) | splits spacelike/timelike | `single_coord_self` | **proved** |
| Welch floor `n(n−d)/d` (§5.3) | driver degrades to `s²/\|K\|`, vacuous at `s=0` | `krein_welch_driver_vanishes`, `kip_trace_eq_signature` | **proved** |
| irreducibility (§5.7) | new frame-geometric sibling: the null token | `null_vector` | **proved** |

### What is *not* claimed
- **Welch achievability is open.** `krein_welch_driver_vanishes` kills the *lower bound* (the
  guarantee of forced interference), **not** the geometry: an indefinite J-orthonormal set is still
  linearly independent, hence still capped at `d`. Whether total coherence can actually be pushed below
  `n(n−d)/d` with `n>d` features is `[open]`.
- **The "absorb J" triviality.** With a *fixed, freely-absorbable* `J`, Krein-PIC ≅ Euclidean-PIC over
  `{J U_v}` (`kinner_majorant` is the escape hatch; `J = id` is ordinary PIC). The content appears only
  when `J` is *not* free to absorb — shared across two pairings, signature-constrained, or with the
  frame frozen and the *metric* the learnable object — **and** norms are read in `[·,·]`, not the
  majorant. This caveat is stated in both theory headers; it is the load-bearing honesty of the corpus.
- **Transformer relevance is `[open/empirical]`.** Nothing here measures a real model. The natural
  `fieldrun` probe: does the QK symmetric part carry a non-trivial signature; is a small negative
  subspace a better model of an unembedding frame than a PSD one?

## The quantum-informational connection (a structural conjecture — NOT a literature claim)

This started from arXiv:2509.09346 (Boyle–Turok–Vaibhav, a UV-fixed-point Standard-Model-like theory
with **36 four-derivative scalars**). That paper is about RG beta functions, *not* Krein spaces or
quantum information — and, as far as we can tell, **there may be no "Krein-space quantum information"
literature to cite at all.** What follows is therefore our own analogy, flagged `[speculative]`, leaning
only on *real, established physics* of indefinite-metric quantization (Pauli–Villars / Lee–Wick ghosts,
Gupta–Bleuler, pseudo-Hermitian / PT-symmetric QM), not on any claimed QI results.

The bridge is tight at three points, and each maps onto a theorem above:

1. **Fundamental symmetry `J` ≈ the metric operator `η` of pseudo-Hermitian QM.** A non-Hermitian `H`
   that is Hermitian w.r.t. an indefinite `[·,·]` is made probabilistic by constructing a positive `η`
   with `⟨·,·⟩_η = [·, η·]`. That construction is *exactly* `kinner_majorant` ("retreat to the
   majorant"). Unbroken-PT (real spectrum, positive majorant exists) ↔ Euclidean PIC; broken-PT (no
   positive majorant) ↔ the genuinely indefinite regime.
2. **Ghosts buy cancellation at the cost of positivity.** Four-derivative kinetic terms (Boyle–Turok's
   scalars; Pauli–Villars) carry negative-norm states that *cancel UV divergences*. This is the same
   trade as `krein_welch_driver_vanishes`: indefiniteness lets Gram eigenvalues cancel, weakening the
   interference floor — **finiteness/packing bought with would-be unitarity/margin-certifiability.** The
   capacity↔robustness axis of the frame side is the ghost trade-off in another costume.
3. **Null states ≈ zero-norm / gauge directions.** `null_vector` (a non-zero `[x,x]=0` token) is the
   PIC analogue of a zero-norm Gupta–Bleuler gauge state — present in the space, invisible to the
   indefinite form, never cleanly "retrievable."

We do **not** claim any of these as theorems about physics or about transformers; they are why the
thought experiment is interesting, and what a future, genuinely cross-disciplinary note could try to
make precise (e.g. an `η`/`J`-construction that is the literal frame-learning step of `pil`).

## Open targets (in rough order of tractability)

- **Signed Welch lower bound, achievability** (`[open]`): is there an indefinite frame with `n>d` units
  and total squared coherence `< n(n−d)/d`? Construct one, or prove the floor secretly survives.
- **`margin_pair_separation_k`, indefinite-ball form** (`[open]`): a usable capacity statement when the
  residual is constrained by `[r,r] ≤ 1` but the frame is Pontryagin (finite negative dimension `q`) —
  presumably a bound in `p` plus a `q`-dependent unbounded direction count.
- **fieldrun measurement** (`[empirical]`): signature of the QK symmetric part across architectures;
  negative-subspace dimension of unembedding frames.
- **`η = J` as the pil step** (`[speculative]`): formalize the pseudo-Hermitian metric construction as
  the frame-learning move and see whether it predicts anything `pil` measures.

## Feedback into the core PIC corpus

What from here is a candidate to graduate into the proved corpus, and when. The **decode-side metric
independence** is the one piece ready now and worth landing regardless of Krein: tag each `PIC_SPEC.md`
§5 theorem *metric-free vs metric-dependent* (the third axis alongside §4 frame/decode and §5.0
monomial/variable) — a small, non-speculative spec edit the whole tree justifies. The **bottom-K min-plus
dual** has already fed back (now in `tropical/HeadTail.thy`, Euclidean). The **`descends_all_iff_psd`
dichotomy** and the **Scheme A recipes** stay here as a thought experiment until an empirical signal
exists (`pil` §6.1: no frame knob yet beats SGD) — they would graduate only if a measured win, or a
`fieldrun` non-trivial QK signature, turns "could help" into "does." Until then they are a kernel-checked
*map* of where indefinite structure is and isn't a resource, not a recommendation to the core.
