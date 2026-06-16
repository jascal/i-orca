# Provenance corpus — verification results

Status of the `examples/provenance/` corpus under **Isabelle2025-2**. Two layers
(SPEC §2, §8): the cheap structural skeleton (`i-orca verify`, no Isabelle) and the
real kernel check (`isabelle build`).

## Commands

```bash
# Layer 1 — structural skeleton (zero Isabelle)
i-orca verify examples/provenance/provenance.i.orca.md
#   -> all 11 theorems VALID, formal_fraction_static = 1.000, 0 frontier holes

# Layer 2 — kernel check of the substrate (the load-bearing math)
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/provenance \
  -o quick_and_dirty Provenance
#   -> Finished Provenance, exit 0, zero sorry

# Layer 2 — kernel check of the SURFACE (compile, add to ROOT, build in-session)
i-orca compile examples/provenance/provenance.i.orca.md --target isar \
  --document --theory ProvenanceSurface --out examples/provenance/ProvenanceSurface.thy
#   append "ProvenanceSurface" to ROOT, rebuild  -> exit 0
#   (ProvenanceSurface.thy is a regenerable artifact; not committed)
```

## Outcome

| Layer | Tool | Result |
|-------|------|--------|
| Skeleton | `i-orca verify` | 11/11 VALID, `formal_fraction_static = 1.000` |
| Substrate | `isabelle build` (`Provenance` session) | exit 0, **zero `sorry`** |
| Surface | `isabelle build` (compiled `ProvenanceSurface` in-session) | exit 0 — every `(rule …)` non-vacuous |

## Theorems (surface → kernel-checked substrate lemma)

**Problem 1 — exact syntactic provenance**
- `SyntacticProvenanceExact` → `synt_post_sum_one`
- `SyntacticProvenanceZeroEntropy` → `synt_entropy_zero`

**Problem 2 — fundamental limits**
- `MixedProvenancePositiveEntropy` → `mixed_entropy_pos` (binary split)
- `MixedProvenancePositiveEntropyGeneral` → `mixed_entropy_pos_gen` (any finite support ≥ 2)
- `InfluenceConditionNumberTight` → `condition_number_tight`
- `ConditionNumberAtLeastOne` → `kappa_ge_one`

**Bucketing leverage / synthesis**
- `ProvenanceSupportBound` → `provenance_support_bound`
- `IsolatedAttributionExact` → `isolated_attribution_exact`

**Scenario (ii) — only the bucketing-pass data known**
- `FaithfulRecoversGenerative` → `faithful_posterior_agreement`
- `GenerativeUnderdeterminedOffCoverage` → `generative_underdetermined_off_used`
- `UncoveredForcesAbstention` → `uncovered_forces_abstention`

## Caveat

The standalone `i-orca check` cannot load this project-local session (it builds each
theorem under a plain HOL parent), so the surface is kernel-checked via
`isabelle build` rather than the batch backend — an import-resolution limit, not a
math failure (same as the `complexity` corpus).
