# Swap-score and rounding bounds (Isabelle, kernel-checked)

> **In i-orca:** copied from the (unpublished) equivalent-student study repo. Relative links to files outside this
> folder (`../../GLOSSARY.md`, `../certificate/...`) point into that repo and do not resolve here. See
> [`../README.md`](../README.md) for the corpus overview.

Written 2026-11-22 by the SCALE session at the user's request. It is separate from the parent folder's `Student_Formal`
session (code-22's), so neither build touches the other. Labels are explained in [../../GLOSSARY.md](../../GLOSSARY.md).

## Status
`proved`: Isabelle2025-2, session `Swap_Bounds`, no `sorry`, no `quick_and_dirty`. The statements are about the
definitions here. They are not a check of the training or scoring scripts.

## Statements
- **Swap_Score_Bounds.thy** (a trial = one node, input pair and position of a swap test; score = fraction of trials that agree):
  - S1 `score_triangle`: score(student, host) >= score(student, clamped host) + score(clamped host, host) - 1. With exact
    versions in `card_dis_triangle` and `exact_screen`. If the clamped host passes the swaps and the student matches the clamped
    host under the swaps, the student passes too, losing at most the two error rates. This licenses screening a clamp set on the
    host alone before training.
    - **Overlap:** this is an instance of code-22's C3 `clamp_cost_bound` (../Node_Mask_Clamp.thy), which is the same count
      bound for any three functions. Kept here only for the fraction form.
    - **How to read it:** the bound is useful only when the student is close to the clamped host. Rearranged, it says the
      student's error is at least the clamped host's error minus how far the student is from the clamped host. So the screen
      says whether a clamp set *allows* a host-faithful student that imitates the clamped host. It does not predict a trained
      student, which can compensate (c21). On case 2 s0 the student matches the clamped host under M0 swaps on only 37%, so for
      M0 the bound is vacuous.
  - S2 `noop_floor`: a student whose swap does nothing scores at least (plain agreement) - (fraction of trials where the
    swap changes the host's output). `noop_fails_changed`: that student is wrong on every changed trial where it matched the
    host before the swap. So raw swap scores are uninformative when the swap rarely changes the host. Report IIA on changed
    positions.
- **Rounding_Margin.thy**:
  - R1 `top_preserved_lipschitz`: if every logit moves by at most sum_j K_j |dx_j|, and each feature moves by at most w_j under
    rounding, then 2 * sum_j K_j w_j < margin keeps the top answer on top. **Whose margin:** the margin is the
    continuous student's own top-1 margin at the unrounded code. So the theorem says rounding keeps the *continuous
    student's* answer. It matches the host only where the continuous student already has the host's top-1, which is an
    empirical per-position fact. The bound with constants K_j is a hypothesis; the theorem does not derive the K_j. J should
    be finite: for an infinite J, Isabelle's sum is 0 and the hypothesis degenerates to f y = f x. (Wording corrected
    2026-11-23 after code-22's review.)
  - `bin_error`: if the stored level value lies in the same bin as the code, the rounding error is at most the bin's width. The
    outer bins are bounded only by the calibration sample's range.
  - This is a sufficient condition only. The necessary side is Cap1 (../Capacity_Counting.thy).
- **Feature_Node_Swaps.thy**:
  - F1 `all_features_and_remainder_is_node_swap`: for a site output = sum_j c_j d_j + remainder, swapping every feature and the
    remainder is the node swap.
  - `feature_swap_effect` / `feature_effects_add`: at the site output, feature-swap effects add.
  - F2 `small_swaps_match` / `next_size_differs`: with 2m + 2 duplicated units, a host and a student can agree on every swap
    of at most m units and differ on a swap of m + 1. This generalises P1 of ../Swap_Probe_Identifiability.thy, which is the case m = 1 (four copies; single swaps match, a two-node swap differs). A
    subset test that stops at size m certifies nothing about larger subsets.

## Not covered
- Quantile cut-offs and rare classes (plan L1): deferred. Whether a rare class gets its own bin depends on the exact quantile
  convention in the calibration code (torch.quantile interpolation, ties). That is better stated with L1's implementation.
- "Outputs match by a different route" (c21): already covered on small models by ../Swap_Probe_Identifiability.thy
  (P1 `single_swaps_not_enough`, P3 `clamp_breaks_swap_equivalence`). No new theorem.
- Whether a trained student satisfies any hypothesis here (e.g. the Lipschitz constants and margins on pythia-14m): `empirical`,
  to be measured.

## Rebuild
    cd /home/allans/code/student-lab/formal/swap_bounds
    nice -n 10 isabelle build -j 1 -o threads=1 -D .
