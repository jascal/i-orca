<!--
  i-orca surface for PO-T4 / PO-T1 — a machine-checked T_P-equivalence for the
  LOSSLESS DEMAND / DEAD-STRATUM transform on fieldrun's exported semiring-Datalog
  program Π (see ../../../fieldrun/PROVABLE_OPT_PROPOSAL.md §5–6, and
  ../../../fieldrun/LOGIC_EXPORT.md for the export of the model as Π).

  The real proofs (a least-fixpoint argument via lfp_lowerbound / lfp_unfold, a
  datatype-modelled concrete program, and its demand-closure) live in the Isabelle
  theory ProvableOpt.thy in this directory; the i-orca table DSL is a structural
  skeleton, so each theorem is STATED in i-orca form and discharged by
  `(rule <lemma>)` against its kernel-checked Isabelle lemma, resolved through
  `## imports`. (As in the complexity corpus we deliberately do NOT list the cited
  lemma in `## context`: context rows lower to local `assumes`, which would turn the
  cite into a vacuous P ⟹ P. Genuine hypotheses like `mono T` are kept as ⟹ premises
  in the goal Statement instead.)

  Verification:
    - `i-orca verify` (structural, zero Isabelle): all theorems VALID,
      formal_fraction_static = 1.000.
    - `i-orca check provable_opt.i.orca.md` (per-theorem kernel check): resolves
      each `(rule …)` against this dir's "ProvableOpt" session automatically (it
      auto-detects the sibling ROOT, declares it as a `sessions` dependency, and
      qualifies the project-local `## imports`) — all theorems formal_fraction_real
      = 1.000.
    - Authoritative certificate: `isabelle build -D .` (ROOT session "ProvableOpt",
      parent HOL, NO quick_and_dirty) builds ProvableOpt.thy with zero `sorry`.

  What this certifies (honest scope): the LOSSLESS demand-restriction family
  (dead-stratum / `lastpos`), i.e. PO-T1 made a fixpoint theorem and PO-T4's first
  concrete instance. It does NOT certify the full magic-sets ADORNMENT transform
  (binding-pattern specialisation) — that stays open.
-->

# theorem DemandRestrictLfp
> PO-T1 (general). For a monotone immediate-consequence operator T_P and a demand-closed set D (the atoms the query transitively reads), running the demand-restricted program computes EXACTLY the demanded part of the full least model: lfp(restrict_op T D) = lfp T ∩ D. Correctness is a theorem about the fixpoint, not a measurement. Cites `demand_restrict_lfp` in ProvableOpt.thy.

## imports
| Theory      |
|-------------|
| ProvableOpt |

## goal
| Statement |
|-----------|
| mono T ⟹ demand_closed T D ⟹ lfp (restrict_op T D) = lfp T ∩ D |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | mono T ⟹ demand_closed T D ⟹ lfp (restrict_op T D) = lfp T ∩ D | the kernel-checked fixpoint equivalence (lfp_lowerbound + lfp_unfold) | — | (rule demand_restrict_lfp) | method |


# theorem DemandRestrictQuery
> PO-T1 (decode preserved for EVERY context). For any query/output predicate Q ⊆ D, the demand transform preserves the query exactly on every EDB: lfp T ∩ Q = lfp(restrict_op T D) ∩ Q. This is the contract that makes the Soufflé demand/dead-stratum rewrite faithful — same `decide`/`logit` for every input. Cites `demand_restrict_query`.

## imports
| Theory      |
|-------------|
| ProvableOpt |

## goal
| Statement |
|-----------|
| mono T ⟹ demand_closed T D ⟹ Q ⊆ D ⟹ lfp T ∩ Q = lfp (restrict_op T D) ∩ Q |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | mono T ⟹ demand_closed T D ⟹ Q ⊆ D ⟹ lfp T ∩ Q = lfp (restrict_op T D) ∩ Q | project the general equivalence onto Q ⊆ D | — | (rule demand_restrict_query) | method |


# theorem LastposDemandClosed
> The concrete `lastpos` premise. In the tiny Π where `logit` reads only the lastpos accumulate, the demanded set D = {Logit, Acc L, Res L} is demand-closed: the producers of a D-atom read only D-atoms. This is the structural fact that licenses the dead-stratum restriction. Cites `Tlm_demand_closed`.

## imports
| Theory      |
|-------------|
| ProvableOpt |

## goal
| Statement |
|-----------|
| demand_closed (Tlm L) (Dlm L) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | demand_closed (Tlm L) (Dlm L) | the rules deriving a lastpos atom mention only lastpos atoms | — | (rule Tlm_demand_closed) | method |


# theorem LastposDemandRestrictLfp
> The instance of the general T_P-equivalence on the `lastpos` program: the transformed program computes exactly the demanded slice of the full least model. Cites `Tlm_demand_restrict_lfp`.

## imports
| Theory      |
|-------------|
| ProvableOpt |

## goal
| Statement |
|-----------|
| lfp (restrict_op (Tlm L) (Dlm L)) = lfp (Tlm L) ∩ Dlm L |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | lfp (restrict_op (Tlm L) (Dlm L)) = lfp (Tlm L) ∩ Dlm L | instantiate `demand_restrict_lfp` at (Tlm L, Dlm L) | — | (rule Tlm_demand_restrict_lfp) | method |


# theorem LastposTransformLosslessAndStrict
> The payoff: for any non-final position p < L, the FULL program derives the accumulate Acc p, the TRANSFORMED program drops it, AND the decode (Logit) is preserved either way. A lossless transform that genuinely removes work — "final-norm at one position, not all". Cites `lastpos_transform_lossless_and_strict`.

## imports
| Theory      |
|-------------|
| ProvableOpt |

## goal
| Statement |
|-----------|
| p < L ⟹ Acc p ∈ lfp (Tlm L) ∧ Acc p ∉ lfp (restrict_op (Tlm L) (Dlm L)) ∧ (Logit ∈ lfp (Tlm L) ⟷ Logit ∈ lfp (restrict_op (Tlm L) (Dlm L))) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | p < L ⟹ Acc p ∈ lfp (Tlm L) ∧ Acc p ∉ lfp (restrict_op (Tlm L) (Dlm L)) ∧ (Logit ∈ lfp (Tlm L) ⟷ Logit ∈ lfp (restrict_op (Tlm L) (Dlm L))) | lossless on the decode, strict on the dropped stratum | — | (rule lastpos_transform_lossless_and_strict) | method |
