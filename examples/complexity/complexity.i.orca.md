<!--
  i-orca surface for the COMPLEXITY-OF-IRREDUCIBILITY theory — the results that are
  NOT in the fieldrun paper (those live in ../fieldrun/fieldrun.i.orca.md). The heavy
  proofs (a recursive `function` + termination, strong inductions, an inductive
  decomposition relation, sum double-counting, bchoice) live in the Isabelle theories
  in this directory; the i-orca table DSL is a structural skeleton, so here each
  non-paper theorem is STATED in i-orca form and discharged by `(rule <lemma>)` against
  its kernel-checked Isabelle lemma, resolved through `## imports`. (We deliberately do
  NOT list the cited lemma in `## context`: the compiler lowers context rows to local
  `assumes`, which would turn the cite into a vacuous `P ⟹ P`.)

  Verification:
    - `i-orca verify` (structural, zero Isabelle): all theorems VALID,
      formal_fraction_static = 1.000.
    - Kernel check: the compiled `theorem T: "<goal>" by (rule <lemma>)` (imports the
      local theory) is non-vacuous and kernel-checks against the `Hardness` session.
      `i-orca check complexity.i.orca.md` now resolves this automatically — it
      auto-detects the sibling ROOT, declares `Hardness` as a `sessions` dependency,
      and qualifies the project-local `## imports` (incl. the transitive
      `../fieldrun/separation` chain) — so every theorem reports formal_fraction_real
      = 1.000. (Building INSIDE the `Hardness` session via `isabelle build` remains
      the authoritative path.)

  Companion file: hardness.i.orca.md — the concrete single-competitor witness.
-->

# theorem MinimalDeciderDecides
> The executable greedy `minimal_decider` (a real `function` + termination on `card S`, each step the poly single-removal test) still decides the target outcome. Cites `minimal_decider_decides` in MinimalDecider.thy.

## imports
| Theory         |
|----------------|
| MinimalDecider |

## goal
| Statement |
|-----------|
| finite S ⟹ decides c S V t ⟹ decides c (minimal_decider c t V S) V t |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite S ⟹ decides c S V t ⟹ decides c (minimal_decider c t V S) V t | the kernel-checked correctness lemma | — | (rule minimal_decider_decides) | method |


# theorem MinimalDeciderLocallyMinimal
> The greedy result is LOCALLY MINIMAL: no single source can be removed while still deciding (`all_necessary`). This is the cheap poly certificate — see the honest gap below. Cites `minimal_decider_all_necessary`.

## imports
| Theory         |
|----------------|
| MinimalDecider |

## goal
| Statement |
|-----------|
| finite S ⟹ all_necessary c (minimal_decider c t V S) V t |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite S ⟹ all_necessary c (minimal_decider c t V S) V t | the stopping condition of the greedy | — | (rule minimal_decider_all_necessary) | method |


# theorem IrreducibleCoreExists
> Every deciding finite coalition contains a GENUINELY irreducible deciding sub-coalition (an atom). This is the global object the greedy under-approximates. Cites `irreducible_core_exists`.

## imports
| Theory         |
|----------------|
| MinimalDecider |

## goal
| Statement |
|-----------|
| finite S ⟹ decides c S V t ⟹ (∃v∈V. v ≠ t) ⟹ (∃A. A ⊆ S ∧ decides c A V t ∧ irreducible c A V t) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite S ⟹ decides c S V t ⟹ (∃v∈V. v ≠ t) ⟹ (∃A. A ⊆ S ∧ decides c A V t ∧ irreducible c A V t) | strong induction on card S, descending through has_suff_sub to an atom | — | (rule irreducible_core_exists) | method |


# theorem EndToEndIrreducibleAtom
> The single-token end-to-end pipeline result: every deciding token has an irreducible atom that still decides AND fires no more neurons than the original on ANY input sample. Cites `every_deciding_token_has_firing_minimal_irreducible_atom`.

## imports
| Theory         |
|----------------|
| MinimalDecider |

## goal
| Statement |
|-----------|
| finite S ⟹ decides c S V t ⟹ (∃v∈V. v ≠ t) ⟹ (∃A. A ⊆ S ∧ decides c A V t ∧ irreducible c A V t ∧ (∀a θ Es. (∑x∈Es. card (active_on a θ x A)) ≤ (∑x∈Es. card (active_on a θ x S)))) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite S ⟹ decides c S V t ⟹ (∃v∈V. v ≠ t) ⟹ (∃A. A ⊆ S ∧ decides c A V t ∧ irreducible c A V t ∧ (∀a θ Es. (∑x∈Es. card (active_on a θ x A)) ≤ (∑x∈Es. card (active_on a θ x S)))) | irreducible core + firing-count monotonicity (total_firing_mono) | — | (rule every_deciding_token_has_firing_minimal_irreducible_atom) | method |


# theorem LocalMinimalityNotIrreducible
> The honest gap (kernel-filter of "greedy ⟹ irreducible"): local minimality (`all_necessary`) does NOT entail irreducibility. The c4 token is all_necessary yet REDUCIBLE — the pair {1,2} decides, reachable only by a two-source removal the greedy never tries. So `minimal_decider` is a sound poly UNDER-approximation. Cites `all_necessary_not_irreducible`.

## imports
| Theory         |
|----------------|
| MinimalDecider |

## goal
| Statement |
|-----------|
| all_necessary c4 {1,2,3,4} {0,1,2} 0 ∧ ¬ irreducible c4 {1,2,3,4} {0,1,2} 0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | all_necessary c4 {1,2,3,4} {0,1,2} 0 ∧ ¬ irreducible c4 {1,2,3,4} {0,1,2} 0 | the n=4 sharp counterexample from the characterisation | — | (rule all_necessary_not_irreducible) | method |


# theorem DBoundedHubBudget
> GAP #3, the realistic hub: under BOUNDED overlap (each neuron in the private part of ≤ d tokens), the naive sum of private sizes overcounts the distinct private union by at most a factor d — so the distinct neuron budget is ≥ sum/d. Cites `d_bounded_private_budget`.

## imports
| Theory |
|--------|
| Hub    |

## goal
| Statement |
|-----------|
| is_d_bounded_disentangling_hub H M Es d ⟹ finite Es ⟹ (⋀e. e ∈ Es ⟹ finite (M e)) ⟹ (∑e∈Es. card (M e - H)) ≤ d * card (⋃e∈Es. (M e - H)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | is_d_bounded_disentangling_hub H M Es d ⟹ finite Es ⟹ (⋀e. e ∈ Es ⟹ finite (M e)) ⟹ (∑e∈Es. card (M e - H)) ≤ d * card (⋃e∈Es. (M e - H)) | double-counting: sum over tokens of card = sum over neurons of multiplicity ≤ d | — | (rule d_bounded_private_budget) | method |


# theorem DecisionCarriedByFiring
> GAP #4, the model bridge: under the firing gate (a non-firing source contributes 0), the decision on any input is carried ENTIRELY by the FIRING sources `active_on` — the quantity fieldrun measures. Cites `decides_iff_active`.

## imports
| Theory       |
|--------------|
| MarginBridge |

## goal
| Statement |
|-----------|
| gated c_x a θ ⟹ finite P ⟹ (decides (c_at c_x x) P V t ⟷ decides (c_at c_x x) (active_on a θ x P) V t) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | gated c_x a θ ⟹ finite P ⟹ (decides (c_at c_x x) P V t ⟷ decides (c_at c_x x) (active_on a θ x P) V t) | non-firing members drop out at 0 (sum_active_eq) | — | (rule decides_iff_active) | method |


# theorem NoFiringNoMargin
> The physical gate in margin form: a source that does not fire on an input contributes no margin on that input. Cites `not_fires_margin_zero`.

## imports
| Theory       |
|--------------|
| MarginBridge |

## goal
| Statement |
|-----------|
| gated c_x a θ ⟹ ¬ fires a θ x j ⟹ margin_x c_x t v j x = 0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | gated c_x a θ ⟹ ¬ fires a θ x j ⟹ margin_x c_x t v j x = 0 | the gate zeroes c_x at t and v | — | (rule not_fires_margin_zero) | method |


# theorem EffectiveAtomInsideMeasuredFiring
> The bridge payoff: on a real input the decision-relevant irreducible atom sits INSIDE the measured active set `active_on a θ x S`, so the measured active count upper-bounds it. This lifts `irreducible_core_exists` onto measured activations. Cites `effective_irreducible_atom_on_input`.

## imports
| Theory       |
|--------------|
| MarginBridge |

## goal
| Statement |
|-----------|
| gated c_x a θ ⟹ finite S ⟹ decides (c_at c_x x) S V t ⟹ (∃v∈V. v ≠ t) ⟹ (∃A. A ⊆ active_on a θ x S ∧ decides (c_at c_x x) A V t ∧ irreducible (c_at c_x x) A V t ∧ card A ≤ card (active_on a θ x S)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | gated c_x a θ ⟹ finite S ⟹ decides (c_at c_x x) S V t ⟹ (∃v∈V. v ≠ t) ⟹ (∃A. A ⊆ active_on a θ x S ∧ decides (c_at c_x x) A V t ∧ irreducible (c_at c_x x) A V t ∧ card A ≤ card (active_on a θ x S)) | decides_iff_active passes the decision to the firing set, then irreducible_core_exists | — | (rule effective_irreducible_atom_on_input) | method |
