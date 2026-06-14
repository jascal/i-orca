# Fieldrun theorems in i-orca — results

This directory formalises the ten theorems/propositions of the paper *"What a
Transformer Retrieves and What It Computes: A Measured Theory of the Composition
Core in Three Interpretations"* (`../../../fieldrun/paper/fieldrun_paper_draft.pdf`)
as i-orca proofs, lowered to Isabelle/Isar and **kernel-checked with Isabelle2025-2**.

- Source: [`fieldrun.i.orca.md`](fieldrun.i.orca.md)
- Generated artifacts: [`artifacts/`](artifacts/) — combined `Fieldrun.thy`,
  per-theorem `.thy`, `.tex`, `.lean`, `prove_report.json`, `kernel_report.json`,
  and `kernel_check_combined.log`.
- Companion development: [`separation/Separation.thy`](separation/Separation.thy)
  (the Theorem-3 separation, see the research note below).

## Headline

**All 10 results are fully kernel-proved.** The combined theory
[`artifacts/Fieldrun.thy`](artifacts/) builds clean (`isabelle build` exit 0) with
**zero `sorry`** — every proof step is a concrete method Isabelle's kernel
accepts. The five originally-frontier steps were discharged ("hammered"): four by
real multi-step i-orca proofs (the k/PR limit, the Diffuseness k-source fraction,
both Maslov bounds), and the fifth — the Theorem-3 general separation — was
*restated faithfully* (the original was a vacuous placeholder) and proven.

## Paper → i-orca map

| Paper result | i-orca theorem | Checkable core |
|--------------|----------------|----------------|
| Thm 1 Cardinality-inertness | `CardinalityInertness` | decision depends only on the column totals; equal totals ⟹ equal argmax (μ_t never enters) |
| Thm 2 Non-truth-functionality budget | `NonTruthFunctionalityBudget` | ‖U_t−U_v‖² = 2(1−ρ); the disjoint/diagonal-G limit ρ=0 ⟹ ‖U_t−U_v‖²=2 |
| Thm 3 Weighted-threshold expressivity | `WeightedThresholdExpressivity` | explicit 2-source/3-outcome composed token: the sum picks outcome 0, no singleton does (μ_0=0) |
| Thm 3 (general half) | `MuZeroNotIrreducible` | μ_t=0 (no singleton) does NOT imply not-Horn-expressible: a μ_0=0 token whose proper subset {1,2} already decides it (see note) |
| Thm 4 Recovered probability | `RecoveredProbability` | m(v)/Σ m = exp(L_v)/Z = softmax, parameter-free |
| Thm 5 Diffuseness | `Diffuseness` | e_m/E = 1/PR; a k-body captures only \|A\|/PR |
| Thm 5 (asymptotic) | `DiffusenessAsymptotic` | k/PR → 0 (const / diverging denom) |
| Thm 6 Two-temperature soundness | `TwoTemperatureSoundness` | tropical aggregate = attained max; Maslov sandwich Max(L) ≤ T·ln Σ exp(L/T) ≤ Max(L)+T·ln\|V\| |
| Prop 1 Cells are a power diagram | `PropPowerDiagram` | power-distance difference = −2 × score difference (weights ω_v = ‖U_v‖²+2b_v) |
| Prop 2 Margin is distance | `PropMarginDistance` | normalised margin numerator = L_t−L_{v*} = Δ; divide by ‖U_t−U_{v*}‖ |

## Kernel verdict (Isabelle2025-2, `HOL-Analysis`)

Combined `Fieldrun.thy` → `isabelle build` **exit 0, zero `sorry`**
(log: [`artifacts/kernel_check_combined.log`](artifacts/kernel_check_combined.log)).
i-orca's own backend (`i-orca check`) independently confirms every step
`checked` ([`artifacts/kernel_report.json`](artifacts/kernel_report.json)):

| i-orca theorem | steps | `formal_fraction_real` |
|----------------|:-----:|:----------------------:|
| CardinalityInertness | 2 | **1.00** |
| NonTruthFunctionalityBudget | 3 | **1.00** |
| WeightedThresholdExpressivity | 3 | **1.00** |
| MuZeroNotIrreducible | 4 | **1.00** |
| RecoveredProbability | 3 | **1.00** |
| Diffuseness | 5 | **1.00** |
| DiffusenessAsymptotic | 1 | **1.00** |
| TwoTemperatureSoundness | 20 | **1.00** |
| PropPowerDiagram | 3 | **1.00** |
| PropMarginDistance | 2 | **1.00** |

## Research note — the Theorem 3 general separation

The paper leaves the *general* Horn / ∩–∪ vs weighted-threshold separation open
("proving the separation in general rather than only on the measured μ_t = 0 set
is left open"). Formalising it forced the crux into the open: **what counts as a
"sufficient sub-conjunction" / "Horn-expressible".**

The first i-orca encoding was a placeholder, `horn_expressible t ⟶ mu_t t ≠ 0`,
with *uninterpreted* predicates — vacuously refutable, hence never a faithful
statement. With explicit definitions (`separation/Separation.thy`):

- `decides c S V t` — t is the strict argmax of the S-sum over outcomes V;
- `mu0 c S V t` — *no singleton* source decides t (the paper's μ_t = 0);
- `has_suff_sub c S V t` — some *proper non-empty subset* already decides t;
- `irreducible c S V t` — `decides` ∧ ¬`has_suff_sub`.

three facts are now kernel-checked:

1. **The gap** (`MuZeroNotIrreducible`, in the i-orca file): a 3-source token with
   `mu0` (no singleton picks it) whose proper subset `{1,2}` *already decides it*.
   So **`μ_t = 0` is strictly weaker than "no sufficient sub-conjunction"** — the
   literal "COMPOSED ⟺ not-Horn-expressible" fails under the subset reading.
2. **Existence of irreducible tokens** (`irreducible_pair`): for *n = 2* sources
   the proper subsets are exactly the singletons, so the original
   `WeightedThresholdExpressivity` witness is *already irreducible*.
3. **Irreducibility needing every source** (`triple_irreducible`): an *n = 3*
   construction where each source defends a distinct threat outcome (weight 8)
   and only the full triple clears all threats on outcome 0 (3+3+3 = 9 > 8) — no
   proper subset suffices. Every source is necessary, tying directly to the
   paper's §4.4 route-ordered fragility ("knock out one circuit and it flips").

**Implication for the paper.** The clean separation needs "COMPOSED" stated as
*"no proper sufficient sub-conjunction decides t"* (irreducibility), not merely
*"no singleton"* (μ_t = 0); the two coincide at n = 2 but diverge for n ≥ 3. The
*existence* of irreducible composed tokens is settled (above); the full
expressivity *characterisation* over formula classes remains the genuine open
frontier — now well-posed rather than vacuous.
