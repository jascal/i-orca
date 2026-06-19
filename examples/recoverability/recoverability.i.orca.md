<!--
  i-orca surface for the SAE feature-recoverability model — the theory behind
  "compression is variance-greedy, meaning is variance-cheap", empirically validated
  on the econ-sae substrate (econ-sae/docs/regime_label_free_recovery.md).

  Presence (probe) is governed by DETECTION theory (Fisher SNR); allocation (does the
  unsupervised SAE surface the feature?) by RATE-DISTORTION theory (between-class
  variance thresholded by reverse water-filling); the two link only through the
  direction's variance, so a feature can be maximally detectable yet dropped.

  Proofs in Recoverability.thy; discharged here by `(rule <lemma>)`.
  Verify: `i-orca check recoverability.i.orca.md` (auto-detects the ROOT). Authoritative:
  `isabelle build -D .`, zero `sorry`, no `quick_and_dirty`.
-->

# theorem WaterFillingDrop
> ALLOCATION thresholds on VARIANCE. The reverse-water-filling rate of a Gaussian mode is zero exactly when its variance is at or below the water level — a low-variance mode gets no rate, i.e. the SAE spends nothing reconstructing it. Cites `rd_rate_zero_iff`.

## imports
| Theory         |
|----------------|
| Recoverability |

## goal
| Statement |
|-----------|
| th > 0 ⟹ (rd_rate lam th = 0) = (lam ≤ th) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | th > 0 ⟹ (rd_rate lam th = 0) = (lam ≤ th) | reverse water-filling: rate > 0 iff variance > water level | — | (rule rd_rate_zero_iff) | method |


# theorem FisherVarShareBridge
> THE BRIDGE. Reconstruction-relevance (var_share) is detectability (fisher) scaled by the direction's OWN variance — so the two functionals are linked ONLY through that variance. Cites `fisher_var_share_bridge`.

## imports
| Theory         |
|----------------|
| Recoverability |

## goal
| Statement |
|-----------|
| s2 > 0 ⟹ var_share c p V = fisher c s2 * (p * (1 - p) * s2 / V) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | s2 > 0 ⟹ var_share c p V = fisher c s2 * (p * (1 - p) * s2 / V) | algebra: var_share = p(1-p)c²/V, fisher = c²/s2 | — | (rule fisher_var_share_bridge) | method |


# theorem PresentNotAllocated
> THE DIVERGENCE — "compression is variance-greedy, meaning is variance-cheap". For ANY target detectability F and ANY reconstruction-relevance threshold th, there is a feature exactly that detectable (fisher = F, a probe reads it) whose reconstruction-relevance falls below th (var_share < th, the variance-greedy SAE drops it). Detectability does NOT imply recoverability. Cites `present_not_allocated`.

## imports
| Theory         |
|----------------|
| Recoverability |

## goal
| Statement |
|-----------|
| F > 0 ⟹ th > 0 ⟹ 0 < p ⟹ p < 1 ⟹ V > 0 ⟹ (∃c s2. s2 > 0 ∧ c > 0 ∧ fisher c s2 = F ∧ var_share c p V < th) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | F > 0 ⟹ th > 0 ⟹ 0 < p ⟹ p < 1 ⟹ V > 0 ⟹ (∃c s2. s2 > 0 ∧ c > 0 ∧ fisher c s2 = F ∧ var_share c p V < th) | place the feature in a low-variance direction: fixed fisher, var_share → 0 | — | (rule present_not_allocated) | method |


# theorem SameFisherOppositeAllocation
> The asymmetry that names the mechanism: two features with the SAME detectability can sit on OPPOSITE sides of the water line — one dropped, one kept — ordered entirely by their variance. Detectability does not order recoverability. Cites `same_fisher_opposite_allocation`.

## imports
| Theory         |
|----------------|
| Recoverability |

## goal
| Statement |
|-----------|
| th > 0 ⟹ 0 < p ⟹ p < 1 ⟹ F > 0 ⟹ (∃c1 s21 c2 s22. s21 > 0 ∧ s22 > 0 ∧ fisher c1 s21 = F ∧ fisher c2 s22 = F ∧ rd_rate (var_share c1 p 1) th = 0 ∧ rd_rate (var_share c2 p 1) th > 0) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | th > 0 ⟹ 0 < p ⟹ p < 1 ⟹ F > 0 ⟹ (∃c1 s21 c2 s22. s21 > 0 ∧ s22 > 0 ∧ fisher c1 s21 = F ∧ fisher c2 s22 = F ∧ rd_rate (var_share c1 p 1) th = 0 ∧ rd_rate (var_share c2 p 1) th > 0) | equal fisher, opposite variance → opposite side of the water level | — | (rule same_fisher_opposite_allocation) | method |
