theory ProvableOpt_Surface
  imports ProvableOpt
begin

text \<open>PO-T1 (general). For a monotone immediate-consequence operator T_P and a demand-closed set D (the atoms the query transitively reads), running the demand-restricted program computes EXACTLY the demanded part of the full least model: lfp(restrict_op T D) = lfp T ∩ D. Correctness is a theorem about the fixpoint, not a measurement. Cites `demand_restrict_lfp` in ProvableOpt.thy.\<close>
theorem demandrestrictlfp:
  shows "mono T \<Longrightarrow> demand_closed T D \<Longrightarrow> lfp (restrict_op T D) = lfp T \<inter> D"
proof -
  show "mono T \<Longrightarrow> demand_closed T D \<Longrightarrow> lfp (restrict_op T D) = lfp T \<inter> D" by (rule demand_restrict_lfp)
qed

text \<open>PO-T1 (decode preserved for EVERY context). For any query/output predicate Q ⊆ D, the demand transform preserves the query exactly on every EDB: lfp T ∩ Q = lfp(restrict_op T D) ∩ Q. This is the contract that makes the Soufflé demand/dead-stratum rewrite faithful — same `decide`/`logit` for every input. Cites `demand_restrict_query`.\<close>
theorem demandrestrictquery:
  shows "mono T \<Longrightarrow> demand_closed T D \<Longrightarrow> Q \<subseteq> D \<Longrightarrow> lfp T \<inter> Q = lfp (restrict_op T D) \<inter> Q"
proof -
  show "mono T \<Longrightarrow> demand_closed T D \<Longrightarrow> Q \<subseteq> D \<Longrightarrow> lfp T \<inter> Q = lfp (restrict_op T D) \<inter> Q" by (rule demand_restrict_query)
qed

text \<open>The concrete `lastpos` premise. In the tiny Π where `logit` reads only the lastpos accumulate, the demanded set D = {Logit, Acc L, Res L} is demand-closed: the producers of a D-atom read only D-atoms. This is the structural fact that licenses the dead-stratum restriction. Cites `Tlm_demand_closed`.\<close>
theorem lastposdemandclosed:
  shows "demand_closed (Tlm L) (Dlm L)"
proof -
  show "demand_closed (Tlm L) (Dlm L)" by (rule Tlm_demand_closed)
qed

text \<open>The instance of the general T_P-equivalence on the `lastpos` program: the transformed program computes exactly the demanded slice of the full least model. Cites `Tlm_demand_restrict_lfp`.\<close>
theorem lastposdemandrestrictlfp:
  shows "lfp (restrict_op (Tlm L) (Dlm L)) = lfp (Tlm L) \<inter> Dlm L"
proof -
  show "lfp (restrict_op (Tlm L) (Dlm L)) = lfp (Tlm L) \<inter> Dlm L" by (rule Tlm_demand_restrict_lfp)
qed

text \<open>The payoff: for any non-final position p < L, the FULL program derives the accumulate Acc p, the TRANSFORMED program drops it, AND the decode (Logit) is preserved either way. A lossless transform that genuinely removes work — "final-norm at one position, not all". Cites `lastpos_transform_lossless_and_strict`.\<close>
theorem lastpostransformlosslessandstrict:
  shows "p < L \<Longrightarrow> Acc p \<in> lfp (Tlm L) \<and> Acc p \<notin> lfp (restrict_op (Tlm L) (Dlm L)) \<and> (Logit \<in> lfp (Tlm L) \<longleftrightarrow> Logit \<in> lfp (restrict_op (Tlm L) (Dlm L)))"
proof -
  show "p < L \<Longrightarrow> Acc p \<in> lfp (Tlm L) \<and> Acc p \<notin> lfp (restrict_op (Tlm L) (Dlm L)) \<and> (Logit \<in> lfp (Tlm L) \<longleftrightarrow> Logit \<in> lfp (restrict_op (Tlm L) (Dlm L)))" by (rule lastpos_transform_lossless_and_strict)
qed

end
