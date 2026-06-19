<!--
  i-orca surface for PO-T1, the KERNEL BRIDGE — the syntactic demand-closure check
  (the static analysis fieldrun's lo3a/demand_closure.py runs on the emitted .dl)
  implies the SEMANTIC demand-closure the lossless theorem needs. So the checker's
  output plugs into the kernel proof: "premise certified by a tool" -> "premise
  proved" (modulo the parser faithfully reading the .dl).

  Proofs in ProvableOpt_Datalog.thy (rule-level ground Datalog T_P over
  ProvableOpt_Common's abstract theorems); discharged here by `(rule <lemma>)`.

  Verification: `i-orca check provable_opt_datalog.i.orca.md` -> all 1.000
  (auto-detected ProvableOpt session). Authoritative: `isabelle build -D .`,
  zero `sorry`, no `quick_and_dirty`.
-->

# theorem TPMono
> The ground Datalog immediate-consequence operator T_P (a head fires when some rule's whole body is present) is monotone. Cites `T_P_mono`.

## imports
| Theory              |
|---------------------|
| ProvableOpt_Datalog |

## goal
| Statement |
|-----------|
| mono (T_P R) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | mono (T_P R) | a head fires for a larger interpretation whenever it fires for a smaller one | — | (rule T_P_mono) | method |


# theorem SynDemandClosedImpDemandClosed
> THE BRIDGE. The SYNTACTIC check — every rule producing a kept atom (∈ D) reads only kept atoms — implies the SEMANTIC demand-closure of T_P. This is exactly the static check the demand-closure tool performs; it now entails what the lossless theorem requires. Cites `syn_demand_closed_imp_demand_closed`.

## imports
| Theory              |
|---------------------|
| ProvableOpt_Datalog |

## goal
| Statement |
|-----------|
| syn_demand_closed R D ⟹ demand_closed (T_P R) D |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | syn_demand_closed R D ⟹ demand_closed (T_P R) D | a kept head's body is ⊆ D, so its derivations survive intersecting with D | — | (rule syn_demand_closed_imp_demand_closed) | method |


# theorem SynDemandClosedLossless
> The payoff, from the syntactic check alone: the demand-restricted program preserves every query atom Q ⊆ D for every input. Chains the bridge through ProvableOpt_Common's `demand_restrict_query`. Cites `syn_demand_closed_lossless`.

## imports
| Theory              |
|---------------------|
| ProvableOpt_Datalog |

## goal
| Statement |
|-----------|
| syn_demand_closed R D ⟹ Q ⊆ D ⟹ lfp (T_P R) ∩ Q = lfp (restrict_op (T_P R) D) ∩ Q |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | syn_demand_closed R D ⟹ Q ⊆ D ⟹ lfp (T_P R) ∩ Q = lfp (restrict_op (T_P R) D) ∩ Q | bridge to demand_closed, then demand_restrict_query | — | (rule syn_demand_closed_lossless) | method |


# theorem DprogSynClosed
> The real `lastpos` final stratum as a ground rule-set (`res p` facts, `acc p` per position, `logit` reads only `acc L`): the kept set (everything but the dead `acc p`, p<L) passes the syntactic check — the exact verdict the checker returns on `whole_base.dl`. Cites `dprog_syn_closed`.

## imports
| Theory              |
|---------------------|
| ProvableOpt_Datalog |

## goal
| Statement |
|-----------|
| syn_demand_closed (dprog L) (dkeep L) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | syn_demand_closed (dprog L) (dkeep L) | every kept head's body lies in the kept set | — | (rule dprog_syn_closed) | method |


# theorem DprogLosslessAndStrict
> End-to-end on the concrete program: for any non-final position p < L the full program derives `DAcc p`, the dead-stratum restriction drops it, and the decode `DLogit` is preserved — all obtained through the bridge from the syntactic check. Cites `dprog_lossless_and_strict`.

## imports
| Theory              |
|---------------------|
| ProvableOpt_Datalog |

## goal
| Statement |
|-----------|
| p < L ⟹ DAcc p ∈ lfp (T_P (dprog L)) ∧ DAcc p ∉ lfp (restrict_op (T_P (dprog L)) (dkeep L)) ∧ (DLogit ∈ lfp (T_P (dprog L)) ⟷ DLogit ∈ lfp (restrict_op (T_P (dprog L)) (dkeep L))) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | p < L ⟹ DAcc p ∈ lfp (T_P (dprog L)) ∧ DAcc p ∉ lfp (restrict_op (T_P (dprog L)) (dkeep L)) ∧ (DLogit ∈ lfp (T_P (dprog L)) ⟷ DLogit ∈ lfp (restrict_op (T_P (dprog L)) (dkeep L))) | the bridge applied to the concrete lastpos program | — | (rule dprog_lossless_and_strict) | method |
