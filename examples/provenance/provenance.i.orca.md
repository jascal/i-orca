<!--
  i-orca surface for the PROVENANCE & INFLUENCE-ATTRIBUTION thread (see PROPOSAL.md
  and README.md). Formalises the sharp dichotomy from the design discussion:

    Problem 1 (syntactic provenance: "which bucket/corpus label produced token t_i?")
      is EXACT -- a deterministic lookup, zero uncertainty.
    Problem 2 (statistical generative influence: "what is the probability corpus C_j
      was the dominant influence on the parameters that emitted t_i?") is
      fundamentally bounded -- except where the explicit density bucketing (in the
      spirit of fieldrun's activation/firing machinery, ../complexity/Density.thy)
      buys it back inside well-isolated buckets.

  Scope: this corpus is grounded in i-orca + fieldrun only. (The original discussion
  also floated q-orca "no-cloning hard zeros"; that was stale context from unrelated
  q-orca work and is deliberately OUT of scope -- the generation pipeline here is the
  classical fieldrun transformer, where no-cloning places no constraint on
  training-data attribution. See PROPOSAL.md "Excluded".)

  As in ../complexity/complexity.i.orca.md, the heavy content lives in the
  kernel-checked Isabelle theories in this directory (Provenance.thy, CondNumber.thy,
  Attribution.thy); each theorem below is STATED in i-orca form and discharged by
  `(rule <lemma>)` against its Isabelle lemma, resolved through `## imports`. We
  deliberately do NOT list the cited lemma in `## context` (the compiler lowers
  context rows to local `assumes`, which would turn the cite into a vacuous P => P).

  Verification:
    - `i-orca verify` (structural, zero Isabelle): all theorems VALID,
      formal_fraction_static = 1.000.
    - Kernel check: the compiled `theorem T: "<goal>" by (rule <lemma>)` is
      non-vacuous and kernel-checks when built INSIDE the `Provenance` session
      (this directory's ROOT):
          ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/provenance \
            -o quick_and_dirty Provenance
      The standalone `i-orca check` builds each theorem under a plain HOL parent and
      cannot load this project-local session -- an import-resolution limit, not a
      math failure (same caveat as the complexity corpus).

  Map to the design discussion's summary table:
    PROBLEM 1 (exact)            -> SyntacticProvenanceExact, SyntacticProvenanceZeroEntropy
    PROBLEM 2 limit: mixing      -> MixedProvenancePositiveEntropy, MixedProvenancePositiveEntropyGeneral
    PROBLEM 2 limit: Hessian     -> InfluenceConditionNumberTight, ConditionNumberAtLeastOne
    density-bucket leverage      -> ProvenanceSupportBound
    synthesis (the payoff)       -> IsolatedAttributionExact
    scenario (ii) explain        -> FaithfulRecoversGenerative, GenerativeUnderdeterminedOffCoverage,
                                    UncoveredForcesAbstention
-->

# theorem SyntacticProvenanceExact
> Problem 1, existence of a clean answer. The syntactic-provenance posterior over candidate sources is the indicator at the bucket's single true source `s`; over any finite candidate set containing `s` it is a valid probability distribution (sums to 1). Deterministic lookup, no statistics. Cites `synt_post_sum_one`.

## imports
| Theory     |
|------------|
| Provenance |

## goal
| Statement |
|-----------|
| finite S ⟹ s ∈ S ⟹ (∑j∈S. synt_post s j) = 1 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite S ⟹ s ∈ S ⟹ (∑j∈S. synt_post s j) = 1 | the indicator is a point mass on the candidate set | — | (rule synt_post_sum_one) | method |


# theorem SyntacticProvenanceZeroEntropy
> Problem 1, the headline. The Shannon entropy of the syntactic posterior is exactly 0 — zero uncertainty about which bucket/corpus label produced the token. This is the part density-min bucketing + token annotations make trivial. Cites `synt_entropy_zero`.

## imports
| Theory     |
|------------|
| Provenance |

## goal
| Statement |
|-----------|
| finite S ⟹ shannon S (synt_post s) = 0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite S ⟹ shannon S (synt_post s) = 0 | every term of the entropy sum is plogp 0 or plogp 1, both zero | — | (rule synt_entropy_zero) | method |


# theorem MixedProvenancePositiveEntropy
> Problem 2, hard limit: irreversible mixing. Once a bucket is realisable from ≥ 2 corpora, gradients from both flowed into the same parameters — the map corpus→weights is many-to-one. Any two-source posterior split (q, 1−q) with 0 < q < 1 has STRICTLY POSITIVE Shannon entropy: the conditional entropy H(C | R,T,a) does not go to zero. Irreducible uncertainty no estimator removes. Cites `mixed_entropy_pos`.

## imports
| Theory     |
|------------|
| Provenance |

## goal
| Statement |
|-----------|
| 0 < q ⟹ q < 1 ⟹ 0 < plogp q + plogp (1 - q) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < q ⟹ q < 1 ⟹ 0 < plogp q + plogp (1 - q) | each interior term −x log₂ x is positive; their sum is positive | — | (rule mixed_entropy_pos) | method |


# theorem MixedProvenancePositiveEntropyGeneral
> The general form of the mixing limit. ANY provenance distribution on a finite source set S with at least two corpora of positive mass has STRICTLY POSITIVE Shannon entropy (the binary split above is the case S = {i,j}). Two distinct positive masses are each interior (each < 1, since the other is positive and the total is 1), so each contributes a positive term while every other term is non-negative. Irreducible uncertainty whenever ≥ 2 corpora genuinely mixed. Cites `mixed_entropy_pos_gen`.

## imports
| Theory     |
|------------|
| Provenance |

## goal
| Statement |
|-----------|
| finite S ⟹ i ∈ S ⟹ j ∈ S ⟹ i ≠ j ⟹ (∀k∈S. 0 ≤ p k) ⟹ (∑k∈S. p k) = 1 ⟹ 0 < p i ⟹ 0 < p j ⟹ 0 < shannon S p |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite S ⟹ i ∈ S ⟹ j ∈ S ⟹ i ≠ j ⟹ (∀k∈S. 0 ≤ p k) ⟹ (∑k∈S. p k) = 1 ⟹ 0 < p i ⟹ 0 < p j ⟹ 0 < shannon S p | two interior masses give two positive terms; the rest are non-negative | — | (rule mixed_entropy_pos_gen) | method |


# theorem InfluenceConditionNumberTight
> Problem 2, hard limit: Hessian conditioning. Influence-function attribution solves a system in the Hessian H; in the eigenbasis the relative error is amplified by the condition number κ = hi/lo. The worst case is achieved EXACTLY: signal along the largest eigenvalue, noise along the smallest, gives output-rel/input-rel = κ. So the error bars (and even the sign) of an influence score scale with κ — which in transformers is 1e6–1e10. Cites `condition_number_tight`.

## imports
| Theory    |
|-----------|
| CondNumber |

## goal
| Statement |
|-----------|
| 0 < lo ⟹ 0 < hi ⟹ 0 < eps ⟹ (((eps * hi) / lo) / 1) / ((eps * hi) / hi) = kappa lo hi |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < lo ⟹ 0 < hi ⟹ 0 < eps ⟹ (((eps * hi) / lo) / 1) / ((eps * hi) / hi) = kappa lo hi | the worst-case signal/noise pair achieves the condition-number bound | — | (rule condition_number_tight) | method |


# theorem ConditionNumberAtLeastOne
> Companion to the above: the condition number is always ≥ 1, so amplification can never help — and equals 1 exactly in the perfectly-conditioned case lo = hi. An isolated, internally-coherent high-density bucket is the lo = hi limit, where the local sub-problem has κ = 1 and the influence estimate is tight. Cites `kappa_ge_one`.

## imports
| Theory    |
|-----------|
| CondNumber |

## goal
| Statement |
|-----------|
| 0 < lo ⟹ lo ≤ hi ⟹ 1 ≤ kappa lo hi |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < lo ⟹ lo ≤ hi ⟹ 1 ≤ kappa lo hi | hi/lo ≥ 1 whenever 0 < lo ≤ hi | — | (rule kappa_ge_one) | method |


# theorem ProvenanceSupportBound
> Density-bucket leverage: the data-processing support bound. Because a response depends on the corpora ONLY through its buckets (the Markov chain C → buckets → R), any posterior consistent with the bucket provenance gives ZERO mass to every source outside the used buckets. This is the exactly-provable discrete shadow of the mutual-information bound I(R; C_j | T,a) ≤ (information through the buckets) — a sound containment, deliberately loose in general. Cites `provenance_support_bound`.

## imports
| Theory      |
|-------------|
| Attribution |

## goal
| Statement |
|-----------|
| consistent bs p ⟹ j ∉ candidates bs ⟹ p j = 0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | consistent bs p ⟹ j ∉ candidates bs ⟹ p j = 0 | no information flows to sources outside the buckets used | — | (rule provenance_support_bound) | method |


# theorem IsolatedAttributionExact
> The synthesis / the payoff. When every bucket in a response carries the same single source `s` (a perfectly isolated, high-density response), the candidate set collapses to {s} and a consistent, normalised attribution posterior is forced to be EXACTLY the syntactic indicator `synt_post s`. The hard statistical question (Problem 2) degenerates into the trivial syntactic one (Problem 1): zero uncertainty. This is "tight inside well-isolated, high-density buckets" — the best practical handle the architecture provides. Cites `isolated_attribution_exact`.

## imports
| Theory      |
|-------------|
| Attribution |

## goal
| Statement |
|-----------|
| bs ≠ [] ⟹ (∀b∈set bs. b = {s}) ⟹ consistent bs p ⟹ (∑j∈candidates bs. p j) = 1 ⟹ p = synt_post s |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | bs ≠ [] ⟹ (∀b∈set bs. b = {s}) ⟹ consistent bs p ⟹ (∑j∈candidates bs. p j) = 1 ⟹ p = synt_post s | isolated buckets ⇒ candidate set {s} ⇒ the consistent normalised posterior is the indicator | — | (rule isolated_attribution_exact) | method |


<!--
  SCENARIO (ii) — only the BUCKETING-PASS data is known, not the model's training
  data (the realistic case; scenario (i) is lab-only). The theorems above carry over
  verbatim (they are about the bucketing, which is fully known) but their REFERENT
  changes from generative/training provenance to REPRESENTATIONAL provenance. The
  three below pin what (ii) can and cannot claim about generative provenance. See
  ReprProvenance.thy and PROPOSAL.md "Two scenarios".
-->

# theorem FaithfulRecoversGenerative
> Scenario (ii), the recovery condition. The bucketing pass yields an observed label map `obs`; the (unknown in ii) training truth is a generative map `g`. Where the pass is FAITHFUL on a bucket set U (obs and g agree there), representational provenance equals generative provenance on U — so (ii) recovers (i)'s exact answer exactly under faithfulness. Cites `faithful_posterior_agreement`.

## imports
| Theory         |
|----------------|
| ReprProvenance |

## goal
| Statement |
|-----------|
| faithful U obs g ⟹ b ∈ U ⟹ synt_post (obs b) = synt_post (g b) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | faithful U obs g ⟹ b ∈ U ⟹ synt_post (obs b) = synt_post (g b) | faithfulness equates the two labels, hence the two posteriors | — | (rule faithful_posterior_agreement) | method |


# theorem GenerativeUnderdeterminedOffCoverage
> Scenario (ii), the weakening. Off the covered region the generative label is provably ambiguous: two training worlds agree with the bucketing pass on every measured bucket U yet disagree on an unmeasured bucket b. So a token that fires a bucket the pass never covered has ambiguous GENERATIVE provenance — no matter how exact its representational provenance. This is the formal limit of (ii). Cites `generative_underdetermined_off_used`.

## imports
| Theory         |
|----------------|
| ReprProvenance |

## goal
| Statement |
|-----------|
| b ∉ U ⟹ (∃g1 g2. faithful U obs g1 ∧ faithful U obs g2 ∧ g1 b ≠ g2 b) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | b ∉ U ⟹ (∃g1 g2. faithful U obs g1 ∧ faithful U obs g2 ∧ g1 b ≠ g2 b) | obs and a single-bucket edit of obs both fit U but differ at b | — | (rule generative_underdetermined_off_used) | method |


# theorem UncoveredForcesAbstention
> Scenario (ii), the honesty discipline (closed world). If a response's buckets are entirely uncovered by the bucketing pass — candidate set empty — then any consistent posterior is identically zero, so no normalised posterior exists and the only sound output is "unknown". The explain feature must abstain, never guess a source. Cites `uncovered_forces_abstention`.

## imports
| Theory         |
|----------------|
| ReprProvenance |

## goal
| Statement |
|-----------|
| consistent bs p ⟹ candidates bs = {} ⟹ p j = 0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | consistent bs p ⟹ candidates bs = {} ⟹ p j = 0 | an empty candidate set zeroes every source, so the posterior cannot normalise | — | (rule uncovered_forces_abstention) | method |
