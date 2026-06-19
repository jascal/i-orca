<!--
  i-orca surface for PO-T3 — the MARGIN-CERTIFIED DECODE INVARIANCE
  (fieldrun PROVABLE_OPT_PROPOSAL.md §4). A transform that perturbs each logit by
  at most δ preserves the decode (argmax) on every token whose margin exceeds 2δ.

  The proofs live in ProvableOpt_Common.thy (general) and ProvableOpt_Margin.thy
  (concrete instance + the boundary flip-witness); the i-orca table is the
  structural skeleton, each theorem discharged by `(rule <lemma>)` against its
  kernel-checked Isabelle lemma, resolved through `## imports`.

  Verification:
    - `i-orca verify` (structural, zero Isabelle): all theorems VALID.
    - `i-orca check provable_opt_margin.i.orca.md`: resolves each `(rule …)` against
      the "ProvableOpt" session automatically (auto-detected sibling ROOT) —
      formal_fraction_real = 1.000.
    - Authoritative: `isabelle build -D .` (session "ProvableOpt", parent HOL,
      NO quick_and_dirty), zero `sorry`.

  HONEST SCOPE / BOUNDEDNESS: PO-T3 is a sound LOCAL certificate. It is SILENT when
  margin ≤ 2δ — the small-margin / dense-G forge-tax tokens (bounded globally by
  LE-T2). `SmallMarginDecodeCanFlip` makes that boundary explicit: a token with
  margin = 1 where an equally-δ-bounded perturbation flips the decode.
-->

# theorem DecodeMarginCertified
> PO-T3 (general, pointwise). If a transform perturbs each logit by at most δ and every competitor of t trails it by more than 2δ under L, then t is still the strict argmax under L′ — the decode is preserved. Cites `decode_margin_certified` in ProvableOpt_Common.thy.

## imports
| Theory             |
|--------------------|
| ProvableOpt_Margin |

## goal
| Statement |
|-----------|
| (⋀v. v ∈ V ⟹ abs (L' v - L v) ≤ δ) ⟹ t ∈ V ⟹ (⋀v. v ∈ V ⟹ v ≠ t ⟹ L t - L v > 2 * δ) ⟹ decodes_to L' V t |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (⋀v. v ∈ V ⟹ abs (L' v - L v) ≤ δ) ⟹ t ∈ V ⟹ (⋀v. v ∈ V ⟹ v ≠ t ⟹ L t - L v > 2 * δ) ⟹ decodes_to L' V t | the kernel-checked margin certificate (abs bounds + linarith) | — | (rule decode_margin_certified) | method |


# theorem DecodeMarginMaxCertified
> PO-T3 (general, margin form). The same with the margin written as the gap to the best competitor (`margin L V t > 2δ`), for a finite token set. Cites `decode_margin_Max_certified`.

## imports
| Theory             |
|--------------------|
| ProvableOpt_Margin |

## goal
| Statement |
|-----------|
| finite V ⟹ V - {t} ≠ {} ⟹ t ∈ V ⟹ (⋀v. v ∈ V ⟹ abs (L' v - L v) ≤ δ) ⟹ margin L V t > 2 * δ ⟹ decodes_to L' V t |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite V ⟹ V - {t} ≠ {} ⟹ t ∈ V ⟹ (⋀v. v ∈ V ⟹ abs (L' v - L v) ≤ δ) ⟹ margin L V t > 2 * δ ⟹ decodes_to L' V t | Max_ge reduces the margin form to the pointwise certificate | — | (rule decode_margin_Max_certified) | method |


# theorem MarginDropDecodePreserved
> The concrete instance: dropping a margin-dominated neuron (perturbation ≤ δ=1) leaves the big-margin token A (margin 12 > 2δ) as the decode. Cites `margin_drop_decode_preserved`.

## imports
| Theory             |
|--------------------|
| ProvableOpt_Margin |

## goal
| Statement |
|-----------|
| decodes_to Lbase UNIV A |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | decodes_to Lbase UNIV A | instantiate the margin certificate at (Lfull, δ=1) | — | (rule margin_drop_decode_preserved) | method |


# theorem SmallMarginDecodeCanFlip
> The honest boundedness: a small-margin token (margin = 1 ≤ 2δ) where an equally-δ-bounded perturbation FLIPS the decode A→B. The 2δ guard is necessary, not cosmetic — the certificate (soundly) refuses small-margin / forge-tax tokens. Cites `small_margin_decode_can_flip`.

## imports
| Theory             |
|--------------------|
| ProvableOpt_Margin |

## goal
| Statement |
|-----------|
| margin Lsmall UNIV A = 1 ∧ (∀v. abs (Lflip v - Lsmall v) ≤ 1) ∧ decodes_to Lsmall UNIV A ∧ ¬ decodes_to Lflip UNIV A ∧ decodes_to Lflip UNIV B |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | margin Lsmall UNIV A = 1 ∧ (∀v. abs (Lflip v - Lsmall v) ≤ 1) ∧ decodes_to Lsmall UNIV A ∧ ¬ decodes_to Lflip UNIV A ∧ decodes_to Lflip UNIV B | the boundary flip-witness | — | (rule small_margin_decode_can_flip) | method |
