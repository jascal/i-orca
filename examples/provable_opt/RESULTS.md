# PO-T4 / PO-T1 — results

Backend: **Isabelle 2025-2** (HOL). Session `ProvableOpt` (see `ROOT`), built with
`isabelle build -D .` — **no `quick_and_dirty`**, so every step is kernel-checked
and any `sorry` would fail the build. Build: `Finished ProvableOpt` (exit 0), both
theories at 100%. See `kernel_build.log`.

## General theorem (PO-T1 as a fixpoint statement)

| Lemma (`ProvableOpt.thy`) | Statement | Status |
|---|---|---|
| `mono_restrict_op` | `mono T ⟹ mono (restrict_op T D)` | ✅ kernel |
| `demand_restrict_lfp` | `mono T ⟹ demand_closed T D ⟹ lfp (restrict_op T D) = lfp T ∩ D` | ✅ kernel |
| `demand_restrict_query` | `mono T ⟹ demand_closed T D ⟹ Q ⊆ D ⟹ lfp T ∩ Q = lfp (restrict_op T D) ∩ Q` | ✅ kernel |

Proof spine: `lfp_lowerbound` (least pre-fixpoint, both inclusions) + `lfp_unfold`
(the fixpoint property) + the `demand_closed` equation — induction on `T_P`.

## Concrete instance (the `lastpos` dead-stratum restriction)

| Lemma | Statement | Status |
|---|---|---|
| `Tlm_mono` | the `lastpos` program's `T_P` is monotone | ✅ kernel |
| `Tlm_demand_closed` | `demand_closed (Tlm L) (Dlm L)`, `Dlm L = {Logit, Acc L, Res L}` | ✅ kernel |
| `Tlm_demand_restrict_lfp` | `lfp (restrict_op (Tlm L) (Dlm L)) = lfp (Tlm L) ∩ Dlm L` | ✅ kernel |
| `Logit_in_full` | `Logit ∈ lfp (Tlm L)` (model actually emits — preservation non-vacuous) | ✅ kernel |
| `Tlm_decode_preserved` | `Logit ∈ lfp (Tlm L) ⟷ Logit ∈ lfp (restrict_op (Tlm L) (Dlm L))` | ✅ kernel |
| `lastpos_transform_lossless_and_strict` | `p < L ⟹` full derives `Acc p` ∧ transform drops `Acc p` ∧ decode preserved | ✅ kernel |

## i-orca surface

| Theorem (`provable_opt.i.orca.md`) | Cites | structural | compiled-to-Isar kernel |
|---|---|---|---|
| `DemandRestrictLfp` | `demand_restrict_lfp` | VALID | ✅ (`ProvableOpt_Surface`) |
| `DemandRestrictQuery` | `demand_restrict_query` | VALID | ✅ |
| `LastposDemandClosed` | `Tlm_demand_closed` | VALID | ✅ |
| `LastposDemandRestrictLfp` | `Tlm_demand_restrict_lfp` | VALID | ✅ |
| `LastposTransformLosslessAndStrict` | `lastpos_transform_lossless_and_strict` | VALID | ✅ |

`i-orca verify`: 5/5 VALID, `formal_fraction_static = 1.000`, 0 frontier holes.
`ProvableOpt_Surface.thy` (the compiled surface) builds in-session, so the
Markdown surface is certified end-to-end (table → Isar → kernel).

## Maps to fieldrun

| fieldrun claim | here |
|---|---|
| PO-T1 — lossless `T_P`-preserving rewrites keep `decide`/`logit` for every context | `demand_restrict_query` |
| PO-T4 — a concrete `Π` transform (the `lastpos` dead-stratum restriction) carried with a machine-checked `T_P`-equivalence | `lastpos_transform_lossless_and_strict` + the surface; **first rung closed** |
| LOGIC_EXPORT — `Π`'s semantics is `lfp T_P`; "same least model" is provable by induction on `T_P` | the whole proof spine |

**Still open (next rungs):** the full magic-sets adornment transform; the
certificate on an emitted real-bundle `Π` (not the tiny model); PO-T3's
margin-certified decode invariance as a companion kernel theorem.
