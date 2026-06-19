<!--
  i-orca surface for PO-T1, the VERIFIED DECISION PROCEDURE — an executable Isabelle
  checker `echeck` for the syntactic demand-closure condition, proved FAITHFUL, with
  a capstone where the lossless guarantee is obtained by RUNNING the checker (`by
  eval`) rather than a hand proof. This shrinks the trusted base of the real-bundle
  line to a single boundary: the parser (.dl text -> rule list).

  Proofs in ProvableOpt_Checker.thy (executable `echeck` + code export, over
  ProvableOpt_Datalog's bridge); discharged here by `(rule <lemma>)`.

  Verification: `i-orca check provable_opt_checker.i.orca.md` -> all 1.000.
  Authoritative: `isabelle build -D .`, zero `sorry`, no `quick_and_dirty`.
-->

# theorem EcheckIff
> FAITHFULNESS. The executable checker `echeck` decides exactly the syntactic demand-closure condition on the abstracted program — sound AND complete. So the Python tool's check has a precise kernel meaning. Cites `echeck_iff`.

## imports
| Theory              |
|---------------------|
| ProvableOpt_Checker |

## goal
| Statement |
|-----------|
| echeck ER KD = syn_demand_closed (prog_of ER) (set KD) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | echeck ER KD = syn_demand_closed (prog_of ER) (set KD) | list_all over the rules ⟺ the Ball condition on the abstracted set | — | (rule echeck_iff) | method |


# theorem EcheckLossless
> A PASS from the executable checker yields the lossless decode guarantee directly — through the kernel bridge and ProvableOpt_Common, with no hand proof of demand-closure. Cites `echeck_lossless`.

## imports
| Theory              |
|---------------------|
| ProvableOpt_Checker |

## goal
| Statement |
|-----------|
| echeck ER KD ⟹ Q ⊆ set KD ⟹ lfp (T_P (prog_of ER)) ∩ Q = lfp (restrict_op (T_P (prog_of ER)) (set KD)) ∩ Q |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | echeck ER KD ⟹ Q ⊆ set KD ⟹ lfp (T_P (prog_of ER)) ∩ Q = lfp (restrict_op (T_P (prog_of ER)) (set KD)) ∩ Q | echeck_iff into the bridge into demand_restrict_query | — | (rule echeck_lossless) | method |


# theorem ExecutableCheckerCertifiesLossless
> THE PAYOFF. The lossless decode guarantee for the concrete `lastpos` program, obtained by EXECUTING the verified checker (`by eval` inside the proof) — the verdict is computed by kernel-trusted code, not asserted by an external tool. Cites `executable_checker_certifies_lossless`.

## imports
| Theory              |
|---------------------|
| ProvableOpt_Checker |

## goal
| Statement |
|-----------|
| lfp (T_P (dprog 5)) ∩ {DLogit} = lfp (restrict_op (T_P (dprog 5)) (dkeep 5)) ∩ {DLogit} |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | lfp (T_P (dprog 5)) ∩ {DLogit} = lfp (restrict_op (T_P (dprog 5)) (dkeep 5)) ∩ {DLogit} | run echeck (by eval), then echeck_lossless on the lastpos fragment | — | (rule executable_checker_certifies_lossless) | method |
