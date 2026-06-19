# Provable optimization of the core — PO-T4 / PO-T1 (kernel-checked)

A machine-checked `T_P`-equivalence for the **lossless demand / dead-stratum
transform** on fieldrun's exported semiring-Datalog program `Π`. This closes the
first rung of `PROVABLE_OPT_PROPOSAL.md` PO-T4, whose status there is **open**:

> **PO-T4 (Certified pipeline).** A concrete transform on `Π` (e.g. the
> dead-stratum `lastpos` restriction) carried with a machine-checked
> `T_P`-equivalence proof. **Status: open** — the Coq/Lean Datalog [pipeline …].

`LOGIC_EXPORT.md` exports the model's next-token computation as a Datalog program
whose semantics is the **least fixpoint** of its immediate-consequence operator
`T_P`. fieldrun's Soufflé pipeline then applies demand / dead-stratum rewrites —
the headline being the **~190–200× lossless** compiled synthesis and the
`lastpos` restriction (`xf`, `ssf` computed at every position but only `lastpos`
read by `logit`). The proposal's whole point is that these are *provable*: under
least-fixpoint semantics correctness is "a theorem about the fixpoint, not a
measurement." This corpus makes that one kernel theorem.

## What is proved (Isabelle 2025-2, zero `sorry`, no `quick_and_dirty`)

[`ProvableOpt.thy`](ProvableOpt.thy):

**General (PO-T1 as a fixpoint theorem).**
- `demand_closed T D` — the producers of a demanded atom read only demanded atoms
  (the stratum-boundary / closed-demand-frontier condition).
- `demand_restrict_lfp` : `mono T ⟹ demand_closed T D ⟹`
  `lfp (restrict_op T D) = lfp T ∩ D` — running the transformed program computes
  **exactly** the demanded part of the full least model. Proved by the two
  standard fixpoint moves, `lfp_lowerbound` (least pre-fixpoint) + `lfp_unfold`
  (the fixpoint property) — i.e. by induction on `T_P`, as the proposal requires.
- `demand_restrict_query` : for any query predicate `Q ⊆ D`,
  `lfp T ∩ Q = lfp (restrict_op T D) ∩ Q` — **the decode is preserved for every
  context (EDB)**. This is the faithfulness contract: same `decide`/`logit` on
  every input.

**Concrete (the `lastpos` dead-stratum instance).** A tiny `Π` with atoms
`Res p / Acc p / Logit`, where `Logit` reads only the lastpos accumulate `Acc L`:
- `Tlm_mono`, `Tlm_demand_closed` — the lastpos demand set `{Logit, Acc L, Res L}`
  is demand-closed.
- `Tlm_demand_restrict_lfp` — the general equivalence, instantiated.
- `lastpos_transform_lossless_and_strict` : for every non-final position `p < L`,
  the **full** program derives `Acc p`, the **transformed** program drops it, and
  the decode (`Logit`) is preserved either way. A lossless transform that
  genuinely removes work — *"final-norm at one position, not all."* (Non-vacuous:
  `Logit_in_full` shows the model actually emits, so "preserved" is not "both
  false".)

[`ProvableOpt_Surface.thy`](ProvableOpt_Surface.thy) is the **compiled i-orca
surface** — `provable_opt.i.orca.md` lowered to Isar and re-deriving each result
via `(rule …)`. It builds inside the session, so the Markdown surface itself is
certified end-to-end (table → Isar → kernel), not just the hand-written theory.

## Honest scope

This certifies the **lossless demand-restriction family** (dead-stratum /
`lastpos`) — PO-T1 and the `--magic-transform` "nothing the query does not read"
guarantee. It does **not** certify the full magic-sets **adornment** transform
(binding-pattern predicate specialisation), which is a strictly heavier
equivalence and remains open. The concrete `Π` is the smallest program that
exhibits the `lastpos` saving faithfully, not a real bundle; scaling the
certificate to an emitted real-bundle `Π` (and to PO-T3's margin certificate) is
the next rung.

## Verify

```bash
# real kernel certificate (authoritative):
isabelle build -D examples/provable_opt        # zero sorry, no quick_and_dirty

# structural surface (no Isabelle):
i-orca verify examples/provable_opt/provable_opt.i.orca.md   # 5/5 VALID, formal_fraction_static=1.000
```

The standalone `i-orca check` builds each theorem under a plain HOL parent and
cannot load this directory's project-local session, so it reports
`formal_fraction_real = 0.0` for the `(rule <local lemma>)` discharges — an
import-resolution limit of the batch backend, **not** a math failure (same caveat
as [`../complexity`](../complexity)). Use the session `isabelle build`.

## Files
- [`ProvableOpt.thy`](ProvableOpt.thy) — the proofs (general + concrete instance).
- [`ProvableOpt_Surface.thy`](ProvableOpt_Surface.thy) — compiled i-orca surface.
- [`provable_opt.i.orca.md`](provable_opt.i.orca.md) — the i-orca table surface.
- [`ROOT`](ROOT) — the `ProvableOpt` Isabelle session.
- [`RESULTS.md`](RESULTS.md) — theorem-by-theorem status.
