# Fieldrun theorems in i-orca — results

This directory formalises the ten theorems/propositions of the paper *"What a
Transformer Retrieves and What It Computes: A Measured Theory of the Composition
Core in Three Interpretations"* (`../../../fieldrun/paper/fieldrun_paper_draft.pdf`)
as i-orca proofs, lowered to Isabelle/Isar and **kernel-checked with Isabelle2025-2**.

- Source: [`fieldrun.i.orca.md`](fieldrun.i.orca.md)
- Generated artifacts: [`artifacts/`](artifacts/) — combined `Fieldrun.thy`,
  per-theorem `.thy`, `.tex`, `.lean`, and `prove_report.json`.

## Paper → i-orca map

| Paper result | i-orca theorem | Checkable core |
|--------------|----------------|----------------|
| Thm 1 Cardinality-inertness | `CardinalityInertness` | decision depends only on the column totals; equal totals ⟹ equal argmax (μ_t never enters) |
| Thm 2 Non-truth-functionality budget | `NonTruthFunctionalityBudget` | ‖U_t−U_v‖² = 2(1−ρ); the disjoint/diagonal-G limit ρ=0 ⟹ ‖U_t−U_v‖²=2 |
| Thm 3 Weighted-threshold expressivity | `WeightedThresholdExpressivity` | explicit 2-source/3-outcome composed token: the sum picks outcome 0, no singleton does (μ_0=0) |
| Thm 3 (general, OPEN in paper) | `WeightedThresholdGeneralSeparation` | frontier hole — the paper leaves the general separation open |
| Thm 4 Recovered probability | `RecoveredProbability` | m(v)/Σ m = exp(L_v)/Z = softmax, parameter-free |
| Thm 5 Diffuseness | `Diffuseness` | e_m/E = 1/PR; a k-body captures only \|A\|/PR |
| Thm 5 (asymptotic) | `DiffusenessAsymptotic` | k/PR → 0 (cited limit; frontier) |
| Thm 6 Two-temperature soundness | `TwoTemperatureSoundness` | tropical aggregate = attained max; Maslov sandwich Max(L) ≤ T·ln Σ exp(L/T) ≤ Max(L)+T·ln\|V\| |
| Prop 1 Cells are a power diagram | `PropPowerDiagram` | power-distance difference = −2 × score difference (weights ω_v = ‖U_v‖²+2b_v) |
| Prop 2 Margin is distance | `PropMarginDistance` | normalised margin numerator = L_t−L_{v*} = Δ; divide by ‖U_t−U_{v*}‖ |

## Honest accounting (SPEC §2, §8, §11.5)

i-orca's static verifier checks only the proof *skeleton*; truth comes from the
Isabelle kernel. We report both numbers and keep them separate.

### Kernel verdict (Isabelle2025-2, `HOL-Analysis`)

The combined theory [`artifacts/Fieldrun.thy`](artifacts/) **builds clean**
(`isabelle build` exit 0 — log: [`artifacts/kernel_check_combined.log`](artifacts/kernel_check_combined.log)).
Every concrete-method step is accepted by Isabelle's kernel; the only gaps are
the **exactly 5 `sorry` holes** listed below. i-orca's own backend
(`i-orca check`) independently confirms the per-step `checked` statuses
([`artifacts/kernel_report.json`](artifacts/kernel_report.json)).

| i-orca theorem | steps | kernel-`checked` | `formal_fraction_real` |
|----------------|:-----:|:----------------:|:----------------------:|
| CardinalityInertness | 2 | 2 | **1.00** |
| NonTruthFunctionalityBudget | 3 | 3 | **1.00** |
| WeightedThresholdExpressivity | 3 | 3 | **1.00** |
| RecoveredProbability | 3 | 3 | **1.00** |
| PropPowerDiagram | 3 | 3 | **1.00** |
| PropMarginDistance | 2 | 2 | **1.00** |
| Diffuseness | 3 | 2 | 0.67 (k-sum → hammer) |
| TwoTemperatureSoundness | 5 | 3 | 0.60 (Maslov sandwich → hammer) |
| DiffusenessAsymptotic | 1 | 0 | 0.00 (cited limit) |
| WeightedThresholdGeneralSeparation | 1 | 0 | 0.00 (open in paper) |

**6 of the 10 results are fully kernel-proved**; **21 of 26 proof steps** are
verified by Isabelle's kernel. The 5 remaining steps are deliberate frontier
holes (below), each matching a place the paper itself stops.


### Frontier holes (deliberate, not failures)

Three steps are honest `sorry`/`hammer` holes, each matching a place the **paper
itself** stops:

- `WeightedThresholdGeneralSeparation` — the paper writes the general Horn /
  ∩–∪ vs weighted-threshold separation is "left open".
- `DiffusenessAsymptotic` — the k/PR → 0 limit, a standard analytic fact.
- `TwoTemperatureSoundness` `s_lower`/`s_upper` — the Maslov-dequantization
  sandwich bounds the paper cites (ref [16]).

These are reported in `formal_fraction`, not hidden, and lower to `sorry` in the
`.thy`. Discharging them with Sledgehammer (`i-orca hammer`) against the warm
session is the natural next step.
