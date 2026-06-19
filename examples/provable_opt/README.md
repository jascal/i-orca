# Provable optimization of the core — PO-T1 + PO-T3 (kernel-checked)

The **formal arm of fieldrun's PROVABLE_OPT** (`PROVABLE_OPT_PROPOSAL.md`):
machine-checked `T_P`-equivalences and decode certificates for the transforms
fieldrun's Soufflé pipeline applies to the exported semiring-Datalog program `Π`.
Two rungs so far, on a shared general theory:

| Rung | Transform | Guarantee | fieldrun |
|------|-----------|-----------|----------|
| **PO-T1 / PO-T4** | lossless demand / dead-stratum (`lastpos`) | exact — preserves `lfp T_P` on the query | the `~190–200×` lossless `--magic-transform` synthesis |
| **PO-T3** | bounded-perturbation (e.g. drop a margin-dominated neuron) | decode-lossless on tokens with **margin > 2δ** | the certified FFN reducer's margin-gated drops |

`LOGIC_EXPORT.md` exports the next-token computation as a Datalog program whose
semantics is the **least fixpoint** of its immediate-consequence operator `T_P`.
The proposal's whole point is that the rewrites are *provable*: correctness is "a
theorem about the fixpoint, not a measurement." This corpus makes those theorems.

## Corpus structure (the shared extraction)

- **[`ProvableOpt_Common.thy`](ProvableOpt_Common.thy)** — the **reusable general
  theory**, corpus-independent: PO-T1 (`restrict_op`, `demand_closed`,
  `demand_restrict_lfp`, `demand_restrict_query`) and PO-T3 (`decodes_to`,
  `margin`, `decode_margin_certified`, `decode_margin_Max_certified`). Later rungs
  import and instantiate rather than re-prove.
- **[`ProvableOpt.thy`](ProvableOpt.thy)** — the `lastpos` PO-T1 instance.
- **[`ProvableOpt_Margin.thy`](ProvableOpt_Margin.thy)** — the PO-T3 instance + the
  boundary flip-witness.

## PO-T1: the demand / dead-stratum transform, as Datalog rules (before → after)

The `lastpos` instance, written as the Datalog `Π` it models (`L` = `lastpos`; the
query is `logit`):

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

The transform **drops `acc(P)` and `res(P)` for every `P < L`** — work no query
reads. Safe because `logit` demands only `acc(L)`, whose producer reads only
`res(L) ∈ D`: the demand frontier `D` is **closed** (`demand_closed`). The general
guarantee is `demand_restrict_lfp` (`lfp (restrict_op T D) = lfp T ∩ D`, proved by
`lfp_lowerbound` + `lfp_unfold` — induction on `T_P`) and `demand_restrict_query`
(decode preserved on **every** EDB); the instance is `Tlm_demand_closed` +
`lastpos_transform_lossless_and_strict` (drops `acc(P)` yet keeps `logit`,
non-vacuously — `Logit_in_full` shows the model emits).

## PO-T3: the margin certificate (and its honest boundary)

A transform that perturbs each logit by at most `δ` preserves the decode (argmax)
on every token whose margin exceeds `2δ`:

- `decode_margin_certified` (pointwise) / `decode_margin_Max_certified` (margin =
  gap to the best competitor, `margin L V t > 2δ`) — the general certificate.
- `margin_drop_decode_preserved` — the instance: dropping a neuron with per-token
  contribution `≤ δ=1` leaves the big-margin token (margin 12) as the decode.

**Honest boundedness (the whole point of stating PO-T3 carefully).** The
certificate is *silent* when margin `≤ 2δ` — the small-margin / dense-`G`
forge-tax tokens, bounded globally by LE-T2. Two witnesses pin the boundary down:

- `small_margin_decode_can_flip` — a token with margin `= 1` where an **equally
  δ-bounded** perturbation **flips** the decode `A → B` (the guard is *necessary*).
- `margin_guard_tight` — at margin `= 2δ` **exactly** (δ = ½) a δ-bounded
  perturbation drives the logits to a **tie**, so preservation fails. Hence the
  guard cannot be weakened from `> 2δ` to `≥ 2δ`: the strict threshold is **tight**,
  not conservative.

So PO-T3 is a sound *local* certificate with an exactly-characterised boundary —
not a global one.

## The compiled i-orca surfaces

[`ProvableOpt_Surface.thy`](ProvableOpt_Surface.thy) and
[`ProvableOpt_Margin_Surface.thy`](ProvableOpt_Margin_Surface.thy) are the
i-orca surfaces (`provable_opt*.i.orca.md`) lowered to Isar and re-deriving each
result via `(rule …)`. They build inside the session, so the Markdown surfaces are
certified **end-to-end** (table → Isar → kernel), not just the hand-written theories.

> **These `*_Surface.thy` files are generated** (and deterministically so — a fresh
> regenerate is byte-identical). Do not hand-edit; regenerate with e.g.
> ```bash
> i-orca compile examples/provable_opt/provable_opt_margin.i.orca.md \
>   --target isar --document --theory ProvableOpt_Margin_Surface \
>   --out examples/provable_opt/ProvableOpt_Margin_Surface.thy
> ```

## Honest scope

- **PO-T1** certifies the **lossless demand-restriction family** (dead-stratum /
  `lastpos`) — *not* the full magic-sets **adornment** transform (binding-pattern
  specialisation), which is strictly heavier and stays open.
- **PO-T3** is a **sound local** decode certificate, explicitly bounded at
  margin `≤ 2δ` (shown by the flip-witness), not a global one.
- Both instances are minimal faithful models, not emitted real bundles. The
  general theorems already cover **any** `Π` / logit family meeting the
  hypotheses; the open work is discharging those hypotheses on real strata.

## Verify

```bash
# authoritative kernel certificate (5 theories, zero sorry, no quick_and_dirty):
isabelle build -D examples/provable_opt

# per-theorem kernel check via the CLI (auto-detects this dir's ROOT):
i-orca check examples/provable_opt/provable_opt.i.orca.md         # 5/5 formal_fraction_real = 1.000
i-orca check examples/provable_opt/provable_opt_margin.i.orca.md  # 4/4 formal_fraction_real = 1.000

# structural surface (no Isabelle):
i-orca verify examples/provable_opt/provable_opt_margin.i.orca.md # VALID, formal_fraction_static=1.000
```

`i-orca check` resolves the `(rule <local lemma>)` discharges against this
corpus's `ProvableOpt` session automatically (sibling `ROOT` → `sessions`
dependency + qualified imports). The session `isabelle build` is the authoritative,
strict (no `quick_and_dirty`) certificate.

## Roadmap (PROVABLE_OPT, formal arm)

Cross-repo progress on carrying fieldrun's PROVABLE_OPT claims as kernel theorems
(tracked here + in `fieldrun/PROVABLE_OPT_PROPOSAL.md §6`):

- [x] **PO-T4 rung 1 — lossless demand / dead-stratum (`lastpos`)** `T_P`-equivalence
      (`demand_restrict_lfp` / `demand_restrict_query` + the `lastpos` instance).
- [x] **Shared general-theory extraction** — `ProvableOpt_Common.thy` holds the
      reusable PO-T1 + PO-T3 theorems; the two instances are thin consumers.
- [x] **PO-T3 — margin-certified decode invariance** (`margin > 2δ`) + boundary
      witnesses (sound local certificate; the `2δ` guard is proved **necessary and
      tight** — `margin_guard_tight`: `>` cannot relax to `≥`).
- [x] **Real-bundle `Π` (checker level)** — `demand_closed` discharged on a *real*
      emitted `Π`: fieldrun's `lo3a/demand_closure.py` soundly certifies the dead
      stratum on `whole_base.dl` (it's the whole final-layer post-attention cone, a
      generalisation of `xf`/`ssf`). This establishes the *premise* of
      `demand_restrict_query` on real strata; the kernel theorem supplies the
      conclusion. *(fieldrun PR #73.)*
- [ ] **Kernel bridge for the checker** — a machine-checked
      `syntactically_demand_closed rules D ⟹ demand_closed (T_P rules) D` (lift from
      the abstract operator to a modelled rule-set), so the checker's syntactic
      output plugs into the kernel proof — closing "premise certified by a tool" →
      "premise proved". *(Then a per-logit-`δ` real-bundle discharge for PO-T3.)*
- [ ] **Full magic-sets *adornment* transform** — binding-pattern predicate
      specialisation (strictly heavier than demand restriction).

## Files
- [`ProvableOpt_Common.thy`](ProvableOpt_Common.thy) — reusable general theory (PO-T1 + PO-T3).
- [`ProvableOpt.thy`](ProvableOpt.thy) — the `lastpos` PO-T1 instance.
- [`ProvableOpt_Margin.thy`](ProvableOpt_Margin.thy) — the PO-T3 instance + flip-witness.
- [`ProvableOpt_Surface.thy`](ProvableOpt_Surface.thy) / [`ProvableOpt_Margin_Surface.thy`](ProvableOpt_Margin_Surface.thy) — compiled i-orca surfaces.
- [`provable_opt.i.orca.md`](provable_opt.i.orca.md) / [`provable_opt_margin.i.orca.md`](provable_opt_margin.i.orca.md) — the i-orca table surfaces.
- [`ROOT`](ROOT) — the `ProvableOpt` Isabelle session.
- [`RESULTS.md`](RESULTS.md) — theorem-by-theorem status.
