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

## The transform, as Datalog rules (before → after)

The concrete `lastpos` instance, written as the Datalog `Π` it models (`L` =
`lastpos`; the query is `logit`):

```prolog
% --- BEFORE: the full program Π ---
res(P)  :- pos(P), P =< L.     % EDB: a residual feature at EVERY position
acc(P)  :- res(P).             % the per-position accumulate / final-norm
logit   :- acc(L).             % the output reads ONLY the lastpos accumulate

% --- AFTER: demand-restricted to D = { logit, acc(L), res(L) } ---
res(L)  :- .                   % only the lastpos residual is kept
acc(L)  :- res(L).             % only the lastpos accumulate is computed
logit   :- acc(L).             %   (unchanged)
```

The transform **drops `acc(P)` and `res(P)` for every `P < L`** — the
per-position final-norm work that no query reads. It is safe because `logit` (the
query) demands only `acc(L)`, whose single producer reads only `res(L) ∈ D`: the
demand frontier `D` is **closed** (`demand_closed`), so the dropped derivations
can never feed `logit`. That closure is the lemma `Tlm_demand_closed`; the
"drops `acc(P)` yet keeps `logit`" payoff is `lastpos_transform_lossless_and_strict`.

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
via `(rule …)`. Its sole purpose is to provide each result under the exact name
the PO-T4 / i-orca surface contract expects (`demandrestrictlfp`,
`lastpostransformlosslessandstrict`, …) and to *check that the Markdown surface
itself kernel-builds*. It builds inside the session, so the surface is certified
end-to-end (table → Isar → kernel), not just the hand-written theory.

> **This file is generated, not hand-written** — and deterministically so (the
> committed copy is byte-identical to a fresh regenerate). Do not edit it by hand;
> regenerate with:
> ```bash
> i-orca compile examples/provable_opt/provable_opt.i.orca.md \
>   --target isar --document --theory ProvableOpt_Surface \
>   --out examples/provable_opt/ProvableOpt_Surface.thy
> ```

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

# per-theorem kernel check via the CLI (auto-detects this dir's ROOT):
i-orca check examples/provable_opt/provable_opt.i.orca.md    # 5/5 formal_fraction_real = 1.000

# structural surface (no Isabelle):
i-orca verify examples/provable_opt/provable_opt.i.orca.md   # 5/5 VALID, formal_fraction_static=1.000
```

`i-orca check` resolves the `(rule <local lemma>)` discharges against this
corpus's `ProvableOpt` session automatically: when a `ROOT` sits beside the
`.i.orca.md`, the backend declares it as a `sessions` dependency and qualifies the
project-local `## imports`, so each theorem kernel-checks to
`formal_fraction_real = 1.000`. (The session `isabelle build` above remains the
authoritative, strict — no `quick_and_dirty` — certificate.)

## Roadmap (PROVABLE_OPT, formal arm)

Cross-repo progress on carrying fieldrun's PROVABLE_OPT claims as kernel theorems
(tracked here + in `fieldrun/PROVABLE_OPT_PROPOSAL.md §6`):

- [x] **PO-T4 rung 1 — lossless demand / dead-stratum (`lastpos`)** `T_P`-equivalence
      (general `demand_restrict_lfp`/`demand_restrict_query` + concrete instance). *This corpus.*
- [ ] **Shared `PO_T1` lemma extraction** — lift the general fixpoint theorems into a
      reusable theory once a second consumer exists (the PO-T3 rung below).
- [ ] **PO-T3 — margin-certified decode invariance** (`m > 2δ`) as a companion kernel
      theorem; sound locally, bounded globally by LE-T2 (so state the bound, don't overclaim).
- [ ] **Real-bundle `Π`** — discharge `demand_closed` on strata actually emitted by
      LOGIC_EXPORT + Soufflé on a small trained model (the general theorem already
      covers *any* `Π` meeting the hypotheses; this verifies the hypotheses on real strata).
- [ ] **Full magic-sets *adornment* transform** — binding-pattern predicate
      specialisation (strictly heavier than demand restriction).

## Files
- [`ProvableOpt.thy`](ProvableOpt.thy) — the proofs (general + concrete instance).
- [`ProvableOpt_Surface.thy`](ProvableOpt_Surface.thy) — compiled i-orca surface.
- [`provable_opt.i.orca.md`](provable_opt.i.orca.md) — the i-orca table surface.
- [`ROOT`](ROOT) — the `ProvableOpt` Isabelle session.
- [`RESULTS.md`](RESULTS.md) — theorem-by-theorem status.
