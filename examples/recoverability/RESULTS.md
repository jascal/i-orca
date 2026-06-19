# Recoverability — results

Backend: **Isabelle 2025-2** (HOL). Session `Recoverability` (see `ROOT`), built with
`isabelle build -D .` — **no `quick_and_dirty`**, so every step is kernel-checked and
any `sorry` fails the build. `Finished Recoverability`, exit 0. See `kernel_build.log`.

## `Recoverability.thy`

| Result | Statement | Status |
|---|---|---|
| `fisher` / `var_share` / `rd_rate` | detection SNR; between-class variance fraction; reverse-water-filling rate | defs |
| `rd_rate_nonneg` | `rd_rate λ θ ≥ 0` | ✅ kernel |
| `rd_rate_pos_iff` | `θ>0 ⟹ (rd_rate λ θ > 0 ⟷ λ > θ)` — allocation thresholds on variance | ✅ kernel |
| `rd_rate_zero_iff` | `θ>0 ⟹ (rd_rate λ θ = 0 ⟷ λ ≤ θ)` — sub-threshold modes get zero rate | ✅ kernel |
| `fisher_var_share_bridge` | `s2>0 ⟹ var_share c p V = fisher c s2 · (p(1−p)·s2/V)` — linked only via the direction variance | ✅ kernel |
| **`present_not_allocated`** | `∀ F θ p V (F,θ,V>0, 0<p<1). ∃ c s2. fisher c s2 = F ∧ var_share c p V < θ` — detectable yet below any allocation threshold | ✅ kernel |
| `arbitrarily_variance_cheap` | at FIXED detectability F, `var_share` can be made arbitrarily small but positive (`0 < var_share < ε`) — the "variance-cheap" point made sharp | ✅ kernel |
| `detectable_yet_dropped` | a feature of arbitrary detectability whose between-class variance is sub-threshold gets `rd_rate = 0` | ✅ kernel |
| `same_fisher_opposite_allocation` | two equally-detectable features on opposite sides of the water line (one dropped, one kept) | ✅ kernel |

Proofs are manual structured Isar over `Complex_Main` (real analysis: `ln`, `sqrt`,
`field_simps`); no Sledgehammer.

## i-orca surface (table → Isar → kernel)

| Surface theorem | cites | `i-orca verify` | `i-orca check` |
|---|---|---|---|
| `WaterFillingDrop` | `rd_rate_zero_iff` | VALID | ✅ |
| `FisherVarShareBridge` | `fisher_var_share_bridge` | VALID | ✅ |
| `PresentNotAllocated` | `present_not_allocated` | VALID | ✅ |
| `SameFisherOppositeAllocation` | `same_fisher_opposite_allocation` | VALID | ✅ |

`i-orca verify`: 4/4 VALID; `i-orca check`: 4/4 `formal_fraction_real = 1.000`;
`Recoverability_Surface` builds in-session (table → Isar → kernel).

## Empirical correspondence (econ-sae)

| formal | measured (econ-sae PR #15; 3 seeds) |
|---|---|
| presence = `fisher` | partial Spearman(Fisher→probe) +0.97 (var_share +0.21) |
| allocation = `var_share` | presence-controlled Spearman(var_share→SAE) +0.94 (Fisher +0.37) |
| `present_not_allocated` | `fiscal_active`: Fisher 169 / var_share 0.0006 / SAE 0.67 |

**Open / next:** the general multivariate water-filling; the SAE-nonlinearity gap; and
the structure-aware (predictive / coverage) objective that the empirical work leaves
as the only untried label-free route to close the allocation gap.
