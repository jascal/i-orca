# ω-budget instrumentation spec — certificate-gated drop for Wyly

**For:** the `pil` agent (target: `experiments/wyly_incidence.py` and successors, `pil` PR #10 line).
**Backing theorem:** `omega_lifecycle_certificate` in
[`Lifecycle.thy`](Lifecycle.thy) (session `ConceptGrounding`, kernel-checked; see also
`lifecycle_decode_preserved`, `graded_membership_stability`, `freeze_limit`). This closes the
θ/γ-turnstile correspondence: **drop** = `pic_krein` PIC_Prune, **freeze** = C4, **finite-ω drift**
= C8, **all three composed under one margin budget** = this certificate. What follows is the exact
contract an implementation must maintain for the θ-drop to be *certified* rather than heuristic.

## The certificate (what the theorem guarantees)

For a linear decode layer — class-v score = Σ_k ⟨p_k, reader_k(v)⟩ over units k (for Wyly heads:
p_k = head weight row block, reader = rule activations; for a linear decode over memberships:
p_k = concept direction, reader = residual) — and a lifecycle step that **drops** the set D and lets
the rest **train against their ω-anchors to stationarity**:

```
if, on input r with winner v0, for every rival w:
    score(w) + 2·( Σ_{k∉D} G_k/(2λω_k)·R  +  Σ_{k∈D} β_k ) < score(v0)
then the argmax decision on r is IDENTICAL before and after the step.   [exact, kernel-proved]
```

- `λ` — the anchor strength (`LAMBDA` in `wyly_incidence.py`).
- `ω_k` — the unit's incidence importance (`imp_*`). Enters only via the drift bound `G_k/(2λω_k)`
  (from `anchored_drift_bound`): **consolidation buys stability at rate 1/ω**.
- `G_k` — a bound on the unit's task-gradient norm ‖∂L_task/∂p_k‖ at the (post-step) stationary
  point. **New tracking**: running max (or a high quantile, honestly labeled) of per-unit gradient
  norms during wake, refreshed each sleep.
- `R` — a bound on the reader norms (for heads: max ‖rule-activation vector‖ over the replay set;
  activations in [0,1] give R ≤ √(#active rules) for free).
- `β_k` — the dropped unit's **contribution majorant**: max over the replay/certification set and
  classes of |⟨p_k, reader_k(v)⟩|. **New tracking, and the load-bearing correction**: usage-derived
  ω does *not* automatically majorize this — β must be measured (a running max of |contribution|
  per unit is enough). This is the "ω as majorant" hypothesis from the review.

## The gate (replacing bare `ω < θ` drop)

```python
D = {k: imp[k] < THETA}                                   # heuristic proposes (unchanged)
delta_budget = sum(G[k] / (2*LAMBDA*imp[k]) * R for k not in D)
beta_budget  = sum(beta[k] for k in D)
Delta = delta_budget + beta_budget
certified = [margin(x) > 2*Delta for x in replay_set]      # margin = score(v0) - max rival score
# accept the drop for the certified fraction; report it; optionally shrink D until it clears
```

Soundness is decoupled from the search (as in PIC_Prune): *any* D passing the check is certified,
whatever proposed it — θ on ω, greedy on β, anything.

## What to report (the experiment this enables)

1. **Certified-stability rate** — fraction of replay inputs whose decode is certificate-preserved —
   alongside empirical retention. The gap between them measures margin slack, not correctness.
2. **Soundness check** — certified inputs must be 100% preserved post-step. Any violation falsifies
   an assumption *of the run, not of the theorem* — in practice: stationarity not reached before
   sleep (train anchored longer / lower LR), or β/G under-tracked (max vs quantile).
3. **Consolidation schedule** — to hold a unit's drift under ε: `ω_k ≥ G_k/(2λε)` (`freeze_limit`).
   Set `CONS_*` in gradient-norm units (ω_k += G_k-scaled usage), not raw usage counts; this makes
   "frozen" a certified state (ε below the smallest margin of interest) instead of a large number.

## Stated domain (do not over-claim)

- Exact for **linear** decode layers. The concept layer has its own exact certificate per concept
  (`graded_membership_stability`: margin > G/(2λω)·‖r‖ ⇒ membership preserved — for hard
  memberships, preserved concepts ⇒ unchanged rule inputs). The **soft-AND rule layer in between is
  not covered** — compose empirically (report it as `empirical`) or run the two certified layers
  end-to-end with hard memberships at certification time.
- Stationarity of the anchored objective is assumed at each sleep, not proved to be reached;
  margins are per-input (the replay-set sup is the honest global surrogate, as in PIC_Prune).
- `prot(ω)` gradient scaling is provably inert under sign-normalized optimizers
  (`sign_updates_ignore_scaling`) — remove it or exclude it from causal claims; the anchor is the
  mechanism the certificate sees.
