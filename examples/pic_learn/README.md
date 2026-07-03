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
