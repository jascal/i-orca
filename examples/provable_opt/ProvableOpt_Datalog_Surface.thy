theory ProvableOpt_Datalog_Surface
  imports ProvableOpt_Datalog
begin

text \<open>The ground Datalog immediate-consequence operator T_P (a head fires when some rule's whole body is present) is monotone. Cites `T_P_mono`.\<close>
theorem tpmono:
  shows "mono (T_P R)"
proof -
  show "mono (T_P R)" by (rule T_P_mono)
qed

text \<open>THE BRIDGE. The SYNTACTIC check — every rule producing a kept atom (∈ D) reads only kept atoms — implies the SEMANTIC demand-closure of T_P. This is exactly the static check the demand-closure tool performs; it now entails what the lossless theorem requires. Cites `syn_demand_closed_imp_demand_closed`.\<close>
theorem syndemandclosedimpdemandclosed:
  shows "syn_demand_closed R D \<Longrightarrow> demand_closed (T_P R) D"
proof -
  show "syn_demand_closed R D \<Longrightarrow> demand_closed (T_P R) D" by (rule syn_demand_closed_imp_demand_closed)
qed

text \<open>The payoff, from the syntactic check alone: the demand-restricted program preserves every query atom Q ⊆ D for every input. Chains the bridge through ProvableOpt_Common's `demand_restrict_query`. Cites `syn_demand_closed_lossless`.\<close>
theorem syndemandclosedlossless:
  shows "syn_demand_closed R D \<Longrightarrow> Q \<subseteq> D \<Longrightarrow> lfp (T_P R) \<inter> Q = lfp (restrict_op (T_P R) D) \<inter> Q"
proof -
  show "syn_demand_closed R D \<Longrightarrow> Q \<subseteq> D \<Longrightarrow> lfp (T_P R) \<inter> Q = lfp (restrict_op (T_P R) D) \<inter> Q" by (rule syn_demand_closed_lossless)
qed

text \<open>The real `lastpos` final stratum as a ground rule-set (`res p` facts, `acc p` per position, `logit` reads only `acc L`): the kept set (everything but the dead `acc p`, p<L) passes the syntactic check — the exact verdict the checker returns on `whole_base.dl`. Cites `dprog_syn_closed`.\<close>
theorem dprogsynclosed:
  shows "syn_demand_closed (dprog L) (dkeep L)"
proof -
  show "syn_demand_closed (dprog L) (dkeep L)" by (rule dprog_syn_closed)
qed

text \<open>End-to-end on the concrete program: for any non-final position p < L the full program derives `DAcc p`, the dead-stratum restriction drops it, and the decode `DLogit` is preserved — all obtained through the bridge from the syntactic check. Cites `dprog_lossless_and_strict`.\<close>
theorem dproglosslessandstrict:
  shows "p < L \<Longrightarrow> DAcc p \<in> lfp (T_P (dprog L)) \<and> DAcc p \<notin> lfp (restrict_op (T_P (dprog L)) (dkeep L)) \<and> (DLogit \<in> lfp (T_P (dprog L)) \<longleftrightarrow> DLogit \<in> lfp (restrict_op (T_P (dprog L)) (dkeep L)))"
proof -
  show "p < L \<Longrightarrow> DAcc p \<in> lfp (T_P (dprog L)) \<and> DAcc p \<notin> lfp (restrict_op (T_P (dprog L)) (dkeep L)) \<and> (DLogit \<in> lfp (T_P (dprog L)) \<longleftrightarrow> DLogit \<in> lfp (restrict_op (T_P (dprog L)) (dkeep L)))" by (rule dprog_lossless_and_strict)
qed

end
