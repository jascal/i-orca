# PROVABLE_OPT formal arm — results

Backend: **Isabelle 2025-2** (HOL / Complex_Main). Session `ProvableOpt` (see
`ROOT`), built with `isabelle build -D .` — **no `quick_and_dirty`**, so every step
is kernel-checked and any `sorry` would fail the build. Build: `Finished
ProvableOpt` (exit 0), all 5 theories at 100%. See `kernel_build.log`.

## Reusable general theory — `ProvableOpt_Common.thy`

### PO-T1 (lossless demand / dead-stratum)

| Lemma | Statement | Status |
|---|---|---|
| `mono_restrict_op` | `mono T ⟹ mono (restrict_op T D)` | ✅ kernel |
| `demand_restrict_lfp` | `mono T ⟹ demand_closed T D ⟹ lfp (restrict_op T D) = lfp T ∩ D` | ✅ kernel |
| `demand_restrict_query` | `mono T ⟹ demand_closed T D ⟹ Q ⊆ D ⟹ lfp T ∩ Q = lfp (restrict_op T D) ∩ Q` | ✅ kernel |

Proof spine: `lfp_lowerbound` + `lfp_unfold` + the `demand_closed` equation (induction on `T_P`). Manual Isar; `metis` only for the equational glue.

### PO-T3 (margin-certified decode invariance)

| Lemma | Statement | Status |
|---|---|---|
| `decode_margin_certified` | `(∀v∈V. ¦L' v − L v¦ ≤ δ) ⟹ t∈V ⟹ (∀v∈V. v≠t ⟶ L t − L v > 2δ) ⟹ decodes_to L' V t` | ✅ kernel |
| `decode_margin_Max_certified` | finite `V`, `V−{t}≠{}`, `t∈V`, δ-bounded perturbation, `margin L V t > 2δ` ⟹ `decodes_to L' V t` | ✅ kernel |

Proof: `abs_le_iff` → linear bounds → `linarith`; the Max form reduces to the pointwise one via `Max_ge`. Manual Isar, no Sledgehammer.

## Concrete instances

### `ProvableOpt.thy` — the `lastpos` PO-T1 instance

| Lemma | Statement | Status |
|---|---|---|
| `Tlm_mono` / `Tlm_demand_closed` | the `lastpos` `T_P` is monotone; `Dlm L = {Logit, Acc L, Res L}` is demand-closed | ✅ kernel |
| `Tlm_demand_restrict_lfp` | `lfp (restrict_op (Tlm L) (Dlm L)) = lfp (Tlm L) ∩ Dlm L` | ✅ kernel |
| `Logit_in_full` / `Tlm_decode_preserved` | the model emits; `Logit` derivable iff derivable after the transform | ✅ kernel |
| `lastpos_transform_lossless_and_strict` | `p < L ⟹` full derives `Acc p` ∧ transform drops `Acc p` ∧ decode preserved | ✅ kernel |

### `ProvableOpt_Margin.thy` — the PO-T3 instance + boundary

| Lemma | Statement | Status |
|---|---|---|
| `drop_neuron_pert` / `margin_full_A` | the neuron-drop perturbation is `≤ 1`; `margin Lfull UNIV A = 12 > 2δ` | ✅ kernel |
| `margin_drop_decode_preserved` | `decodes_to Lbase UNIV A` (big-margin token: decode certified preserved) | ✅ kernel |
| `small_margin_decode_can_flip` | margin `=1 ≤ 2δ` token where a δ-bounded perturbation **flips** the decode `A→B` — the `2δ` guard is necessary | ✅ kernel |
| `margin_guard_tight` | at margin `= 2δ` exactly (δ=½) a δ-bounded perturbation **ties** the logits — so `> 2δ` cannot weaken to `≥ 2δ`: the guard is **tight** | ✅ kernel |

### Kernel bridge — `ProvableOpt_Datalog.thy`

| Lemma | Statement | Status |
|---|---|---|
| `T_P_mono` | the ground Datalog immediate-consequence operator `T_P R` is monotone | ✅ kernel |
| `syn_demand_closed_imp_demand_closed` | `syn_demand_closed R D ⟹ demand_closed (T_P R) D` (the syntactic check ⟹ the semantic one) | ✅ kernel |
| `syn_demand_closed_lossless` | `syn_demand_closed R D ⟹ Q ⊆ D ⟹ lfp (T_P R) ∩ Q = lfp (restrict_op (T_P R) D) ∩ Q` | ✅ kernel |
| `dprog_syn_closed` | the `lastpos` final stratum as a ground rule-set passes the syntactic check | ✅ kernel |
| `dprog_lossless_and_strict` | the lossless-and-strict result re-derived *through the bridge* from the syntactic check | ✅ kernel |

## i-orca surfaces (table → Isar → kernel)

| Surface | Theorems | `i-orca verify` | `i-orca check` | compiled-in-session |
|---|---|---|---|---|
| `provable_opt.i.orca.md` | 5 (PO-T1) | VALID | 5/5 = 1.000 | ✅ `ProvableOpt_Surface` |
| `provable_opt_margin.i.orca.md` | 5 (PO-T3) | VALID | 5/5 = 1.000 | ✅ `ProvableOpt_Margin_Surface` |
| `provable_opt_datalog.i.orca.md` | 5 (bridge) | VALID | 5/5 = 1.000 | ✅ `ProvableOpt_Datalog_Surface` |

## Maps to fieldrun

| fieldrun claim | here |
|---|---|
| PO-T1 — lossless `T_P`-preserving rewrites keep `decide`/`logit` for every context | `demand_restrict_query` |
| PO-T4 — a concrete `Π` transform (`lastpos` dead-stratum) with a machine-checked `T_P`-equivalence | `lastpos_transform_lossless_and_strict` + surface; **rung 1 closed** |
| PO-T3 — margin-certified decode invariance (`m > 2δ`), sound **local**, bounded globally by LE-T2 | `decode_margin_Max_certified` + `small_margin_decode_can_flip` (the bound made explicit) |
| PO-T1 real-bundle — `lo3a/demand_closure.py` certifies the dead stratum on a real `Π`; that *syntactic* premise now provably entails the lossless conclusion | `syn_demand_closed_imp_demand_closed` → `syn_demand_closed_lossless` (the kernel bridge) |

**Still open (next rungs):** a reflected/verified `syn_demand_closed` decision
procedure (closes the last trust gap — parser + checker faithfulness); the
per-logit `δ` real-bundle discharge for PO-T3; the full magic-sets adornment
transform.
