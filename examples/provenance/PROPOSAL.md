# Provenance & influence attribution — proposal

A formalisation of a design-discussion thread: **given a density-min bucketed tree
with per-token source annotations, what can you actually prove about "which corpus
produced / influenced this token"?**

The thread's answer is a sharp dichotomy, and this directory turns each side of it
into a kernel-checked Isabelle theorem with an i-orca surface
([`provenance.i.orca.md`](provenance.i.orca.md)).

## Scope

This corpus lives in the **i-orca + fieldrun** world only. The bucketing premise is
the natural companion to fieldrun's activation/firing machinery (`active_on` /
`fires` / `density_on` in [`../complexity/Density.thy`](../complexity/Density.thy)):
fieldrun asks *which sources a transformer's decision is carried by*; this corpus
asks *what is provable about attributing a token back to a source corpus*. It is a
standalone classical-attribution development — thematically continuous with
fieldrun, with no formal dependency on it.

**Excluded — q-orca.** The original discussion (with Grok) also floated q-orca
"no-cloning hard zeros" as an attribution lever. That was stale context bleeding in
from unrelated past q-orca work, not part of this pipeline. The generation path here
is the **classical fieldrun transformer**, where no-cloning / unitarity place *no*
constraint on training-data attribution. The first draft included a `NoCloning.thy`
(an `r = r² ⇒ r ∈ {0,1}` overlap argument plus an `admissible`/`forbidden` posterior
predicate); it has been deliberately removed. It was the weakest part anyway: only 2
of the 9 theorems, nothing else depended on it, and the load-bearing step
(`forbidden_attribution_zero`) merely *assumed* the certificate→hard-zero bridge
rather than deriving it. The seven classical theorems below stand without it.

## The two problems

Let the corpora be disjoint, `C = ⋃_{j=1..m} C_j`. A density-min bucketed tree `T`
labels every bucket `b` with the source(s) `ℓ(b)` that built it; a generated
response `R = t_1…t_n` carries token annotations `a(t_i) = (b_i, ℓ_i)`,
`ℓ_i = ℓ(b_i)`.

**Problem 1 — syntactic / structural provenance.** "Which corpus label is attached
to the bucket that produced token `t_i`?" Deterministic lookup. The posterior is the
indicator at the bucket's label; **zero uncertainty**.

**Problem 2 — statistical generative influence.** "What is the probability that the
*parameters that caused the model to emit* `t_i` were most strongly shaped by
corpus `C_j`?" This is training-data attribution in an overparameterised
transformer, and it is fundamentally bounded:

1. **Hessian conditioning.** The influence function
   `I(z,R) ≈ −∇_R L(θ*)ᵀ H⁻¹ ∇_z L(θ*)` solves a system in the Hessian `H`, whose
   condition number `κ` in transformers is `1e6–1e10`. Relative error — and even the
   *sign* of a score — is amplified by `κ`.
2. **Irreversible mixing.** Once gradients from two corpora flow into the same
   parameters the map corpus→weights is many-to-one; the conditional entropy
   `H(C_j | R,T,a)` does not go to zero.
3. **Non-convexity / path dependence.** Influence functions are local linear
   approximations around one minimum; they do not capture global credit ambiguity.

**What the bucketing buys back.** Explicit, density-minimised bucketing gives
per-bucket (not per-document) influence — lower variance; and inside a single
well-isolated high-density bucket the local condition number is `≈ 1`, so the
estimate is tight. In the limit of perfect isolation the hard statistical question
collapses back to the trivial syntactic one (theorem 7).

## Two scenarios for an explain feature

The corpus answers a *training*-provenance question, but a fielded "explain" feature
almost never has the training data. Two epistemic regimes:

- **(i) Training data known** (only at the lab that trained the model). Buckets are
  over training data, so a bucket label *is* training provenance. The full Problem-2
  machinery applies — and bites: a generative attribution is *attemptable* but comes
  with `κ`-scaled error bars (thm 4–5) and irreducible mixing entropy (thm 3).
- **(ii) Only the bucketing-pass data known** (the realistic case). The pass runs a
  *known analysis corpus* through the *already-trained* model. A bucket label is then
  **representational** provenance ("emitted from a feature-space region my known data
  labels `C_j`"), **not** a claim about which corpus shaped the weights.

In (ii), theorems 1–2 and 6–7 carry over **verbatim** — they are statements about the
bucketing, which is fully known — but their *referent* shifts from generative to
representational. What (ii) **cannot** do is reach generative provenance; the
influence-function theorems (3–5) need training gradients and simply aren't runnable.
[`ReprProvenance.thy`](ReprProvenance.thy) pins the gap (thms 8–10): a **recovery**
condition, the **weakening**, and the **honesty** discipline.

## What is formalised (and the formal-vs-meta split)

The Isabelle theorems are **honest, narrow, kernel-checked cores** — not claims
about real GPT-scale Hessians. The mapping from theorem to the meta-claim it
supports:

| # | i-orca theorem | Isabelle lemma | Proves (formal) | Supports (meta) |
|---|----------------|----------------|------------------|------------------|
| 1 | SyntacticProvenanceExact | `synt_post_sum_one` | the indicator posterior is a valid distribution | Problem 1 is well-posed |
| 2 | SyntacticProvenanceZeroEntropy | `synt_entropy_zero` | a point-mass posterior has Shannon entropy 0 | Problem 1 is *exact* |
| 3 | MixedProvenancePositiveEntropy | `mixed_entropy_pos` | a 2-source split `0<q<1` has entropy `>0` | mixing ⇒ irreducible uncertainty |
| 4 | InfluenceConditionNumberTight | `condition_number_tight` | worst-case amplification `= κ`, exactly | error bars scale with `κ` |
| 5 | ConditionNumberAtLeastOne | `kappa_ge_one` | `κ ≥ 1`, `=1` iff `lo=hi` | isolated bucket ⇒ tight |
| 6 | ProvenanceSupportBound | `provenance_support_bound` | consistent posterior is 0 off used buckets | the DPI / MI bound (loose) |
| 7 | IsolatedAttributionExact | `isolated_attribution_exact` | isolated ⇒ posterior `= synt_post s` | the synthesis: Problem 2 ⇒ Problem 1 |
| 8 | FaithfulRecoversGenerative | `faithful_posterior_agreement` | faithful on U ⇒ repr label `=` generative label | (ii) recovers (i) under faithfulness |
| 9 | GenerativeUnderdeterminedOffCoverage | `generative_underdetermined_off_used` | off U, two training worlds fit the pass yet disagree | (ii) cannot reach generative provenance off-coverage |
| 10 | UncoveredForcesAbstention | `uncovered_forces_abstention` | empty candidate set ⇒ posterior all-zero | uncovered ⇒ abstain ("unknown"), never guess |

The **meta** column is deliberately not claimed as proven. E.g. theorem 4 proves the
amplification factor *equals* the condition number for a worst-case signal/noise
pair in a diagonal (eigenbasis) model — it does **not** prove anything about the
spectrum of an actual transformer Hessian.

## Honest reckonings

- **Diagonal / eigenbasis model (thm 4, 5).** The condition-number result is stated
  in the eigenbasis where `H` is diagonal. The general operator-norm bound
  `‖Δx‖/‖x‖ ≤ κ ‖Δb‖/‖b‖` (and its tightness) is the same statement coordinate-free;
  the diagonal witness is what we kernel-check. Lifting to the full operator-norm
  statement is an open target.
- **Two-point entropy (thm 3).** We prove strict positivity for the binary split.
  The general "any support-≥2 distribution has positive entropy" is a routine
  generalisation, left as a target.
- **DPI shadow (thm 6).** `provenance_support_bound` is the *set-theoretic* shadow of
  the mutual-information bound `I(R;C_j|T,a) ≤ I(buckets;C_j)`. A genuine
  information-theoretic DPI (KL/`log`-sum machinery) is not attempted here.

## Milestones / open targets

1. **(done)** The ten-theorem development above (seven-theorem dichotomy + the
   three scenario-(ii) results) — all kernel-checked under Isabelle2025-2
   (`isabelle build -D . Provenance`, exit 0, zero `sorry`).
2. Operator-norm condition-number bound (coordinate-free, with tightness).
3. General Shannon-entropy positivity for support `≥ 2`, and the `log`-sum DPI to
   replace the set-theoretic support bound with the real MI inequality.
4. Couple the bucketing model to fieldrun's `active_on` / `density_on` directly, so
   "isolated high-density bucket" is the same object fieldrun measures, not just an
   analogue.
5. **The next lever (from the discussion):** treat buckets as *causal interventions*
   and derive tighter counterfactual influence bounds inside those subgraphs. This is
   where the explicit bucketing structure should pay off most.
