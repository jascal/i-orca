# Recoverability — when does an SAE recover a feature? (kernel-checked)

A formal model of SAE feature **recoverability**: the theory behind *"compression is
variance-greedy, meaning is variance-cheap"*, kernel-proved here and **empirically
validated** on the econ-sae substrate
([`econ-sae/docs/regime_label_free_recovery.md`](../../../econ-sae/docs/regime_label_free_recovery.md)).

## The model

A ground-truth feature, read off a representation along one principal direction, has
two scalar functionals of its mean-shift `c` and the direction's within-class
variance `s2` (= σ²):

- **Presence** (can a linear probe / matched filter read it?) — **detection theory**:
  the Fisher SNR `fisher c s2 = c² / s2`.
- **Allocation** (does the unsupervised SAE spend a latent on it?) — **rate–distortion
  theory**: the between-class variance fraction `var_share c p V = p(1−p)c² / V`,
  which a **reverse-water-filling** coder drops below a budget-set level
  (`rd_rate λ θ = 0 ⟺ λ ≤ θ`).

The two are linked **only** through the direction's variance `s2` — so they decouple.

## What is proved (Isabelle 2025-2, zero `sorry`, no `quick_and_dirty`)

[`Recoverability.thy`](Recoverability.thy):

- **`rd_rate_pos_iff` / `rd_rate_zero_iff`** — the *water-filling drop*: a mode is
  encoded iff its variance clears the water level. **Allocation thresholds on
  variance, nothing else.**
- **`fisher_var_share_bridge`** — the bridge identity:
  `var_share = fisher · (p(1−p)·s2 / V)`. Detectability and reconstruction-relevance
  are linked *only* by the direction's variance.
- **`present_not_allocated`** — *the divergence* (the headline): for **any**
  detectability `F` and **any** threshold `θ`, there is a feature that is exactly that
  detectable (`fisher = F`, a probe reads it) yet whose reconstruction-relevance is
  below `θ` (`var_share < θ`, the variance-greedy SAE drops it). **Detectability does
  not imply recoverability.** Proof: place the feature in a low-variance direction —
  at fixed `fisher`, `var_share → 0` as the direction variance → 0.
- **`detectable_yet_dropped`** — the same against the coder: a feature of arbitrary
  detectability whose between-class variance is sub-threshold gets **zero rate**.
- **`same_fisher_opposite_allocation`** — the asymmetry that names the mechanism: two
  features with the **same** detectability sit on **opposite** sides of the water
  line, ordered entirely by their variance.

## The empirical ↔ formal correspondence

This is the program's signature move — the same claim, *measured* and *proved*:

| formal (here) | empirical (econ-sae) |
|---|---|
| presence = `fisher` | partial Spearman(Fisher → probe) = **+0.97** (vs var_share **+0.21**) |
| allocation = `var_share` | presence-controlled Spearman(var_share → SAE) = **+0.94** (vs Fisher **+0.37**) |
| `present_not_allocated` | `fiscal_active`: Fisher **169** (max), var_share **0.0006**, SAE recovery **0.67** |

## Honest scope

A scalar (single-direction, Gaussian-mode) model — the clean algebraic **core** of the
law, not the full multivariate SAE. It formalises *why* presence and allocation
decouple; the empirical work shows that they *do*, on a real substrate. The general
multivariate water-filling and the SAE's nonlinearity are not modelled here.

## Files
- [`Recoverability.thy`](Recoverability.thy) — the proofs.
- [`Recoverability_Surface.thy`](Recoverability_Surface.thy) — compiled i-orca surface.
- [`recoverability.i.orca.md`](recoverability.i.orca.md) — the i-orca table surface.
- [`ROOT`](ROOT) — the `Recoverability` Isabelle session.
- [`RESULTS.md`](RESULTS.md) — theorem-by-theorem status.

## Verify
```bash
isabelle build -D examples/recoverability                       # zero sorry, no quick_and_dirty
i-orca check examples/recoverability/recoverability.i.orca.md   # 4/4 formal_fraction_real = 1.000
```
