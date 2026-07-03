# pic_learn — kernel-checked certificates for a frame-learning loop

The first learning-side corpus for PIC: theorems about what a **frame-learning trajectory**
(a sequence of joint `(U, b)` updates, e.g. the picard loop's P3 step) provably preserves.
Everything here is `proved` over its stated domain; session is strict
(`quick_and_dirty = false`), 0 sorry.

## Contents (`PIC_Learn.thy`)

| Lemma / theorem | Statement |
|---|---|
| `step_logit_drift` | one joint update with `‖U'_v − U_v‖ ≤ ε`, `\|b'_v − b_v\| ≤ β`, `‖r‖ ≤ ρ` moves each logit by ≤ `ρε + β` (Cauchy–Schwarz + triangle) |
| `margin_transfer` | a δ-bounded logit perturbation degrades a uniform margin `m` to `m − 2δ`; **no sign condition**, so it iterates unconditionally |
| `step_margin_survives` | one joint step degrades the uniform margin to at least `m − 2(ρε + β)` — the quantity to log each iteration, not just threshold |
| `step_decode_preserved` | per-step runtime engine: current margin `> 2(ρε + β)` ⟹ the step preserves the strict argmax. β = 0 recovers `PIC_Quant.quant_decode_preserved` — the β term is what a **trained bias** adds (pil trains `bias`; a frame-only certificate is a silent-divergence trap) |
| `margin_transfer_aniso` | per-competitor transfer: pairwise gap `M_v` degrades to `M_v − D_v − D_t` under per-logit perturbation bounds `D` |
| `step_decode_preserved_aniso` | **T-aniso**, the per-row engine: with per-row budgets `ε_v, β_v`, the decision survives whenever `(ρε_t + β_t) + (ρε_v + β_v) <` the pairwise gap, for every rival `v`. Far-behind rows move freely; only near-competitors need clipping — the certificate a **directional** trust region re-arms per step (a global scalar clip pins at real ρ: pil PR #6 measured ρ ≈ 35 → α ≈ 0.005) |
| `gap_from_uniform_margin` | the special-case bridge: uniform margin `> 2(ρε + β)` implies the pairwise gap condition at constant budgets — the isotropic engine is kernel-provably a special case of T-aniso |
| `traj_decode_margin` | telescoping: after τ steps the surviving uniform margin is `≥ m − 2·Σ_{s<τ}(ρ·ε_s + β_s)` (induction on τ) |
| `traj_decode_preserved` | **T-traj**, the a-priori certificate: total budget `2·Σ_{s<T}(ρ·ε_s + β_s) < m` ⟹ every visited decision is preserved at **every** point of the trajectory |

## Scope, honestly

Local and per-context: one residual `r`, one visited target `t`, uniform margin over the stated
vocabulary `V`; silent below the budget (exact analogue of the 2δ margin certificate, whose
threshold is proved tight in `provable_opt/ProvableOpt_Margin.thy`). It proves decisions
**survive** learning; it says nothing about margins **improving** (invariant S2 /
certified-mass monotonicity — open, the next target).

Discharging the premises on a real run: `ρ` = max observed `‖r‖` over the current bank (or a
safe upper bound — real models pin `‖r‖` via the final norm layer, measured cv ≤ 0.11);
`ε_s`, `β_s` = `max_v ‖ΔU_v‖` and `max_v |Δb_v|` logged from the actual optimizer step;
`m` = minimum visited margin before the update. The per-step engine is the runtime check; the
budget theorem is the a-priori one; `step_margin_survives` is the per-iteration log line.

Known limitation (deliberate, future work): the visited set is fixed per theorem instance —
each context `r` carries its own certificate from its own initial margin. A growing visited set
(P2 adds contexts mid-trajectory) composes by instantiating the theorem at each context's
arrival step; the loop-level statement belongs to T-fix (teacher-anchored constraints), not here.

## Using T-aniso: the directional clip rule

The theorem only requires the *chosen* per-row budgets to satisfy each pairwise inequality —
there is no hidden global coupling — so the budget assignment is a choice, not part of the
certificate. The practical rule (vetted in the PR #22 review):

1. Per step, fix small target budgets `ε_t` for protected targets.
2. Clip each rival row to `ε_v = min` over the protected targets `t` it rivals of
   `(gap(t,v) − (ρε_t + β_t) − β_v)/ρ`, headroom-scaled.
3. Rows that are both rival and target take the tightest of their constraints (per-row min).
   Degenerate tight coupling reduces to a small LP, but real logit landscapes are sparse —
   most rows sit far behind most targets.

Tightness: `ρ` may be instantiated per context as the actual `‖r_x‖` (the theorem takes any
`ρ ≥ ‖r‖`), giving sharper clips at re-arm time. The remaining looseness is the triangle
inequality treating `ΔL_t` and `ΔL_v` as independent worst cases; a joint bound on
`‖ΔU_t − ΔU_v‖` would tighten further — open refinement, soundness unaffected.

A per-row *trajectory* form is deliberately absent: the active competitor sets change across
steps, so a telescoped per-row budget degenerates toward the isotropic sum. The directional
trust region re-arms per step; isotropic T-traj remains the (looser) a-priori fallback.

## Build

```
isabelle build -D examples/pic_learn
```

## Context

Motivated by the picard seam (`PICARD_GOAL.md` / `PICARD_PROOF_PLAN.md`, workspace root):
P3 widens margins on visited facets under the hard constraint that visited decisions are
inviolable (PIC_SPEC §6 invariant S1). This corpus turns that constraint into a checkable,
kernel-proved certificate. Planned successors: T-fix (active-set stabilization of the
cutting-plane loop, with teacher-anchored constraints) and T-seam-linear (identifiability of
per-source supervision up to gauge).
