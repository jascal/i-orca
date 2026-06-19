theory ProvableOpt_Datalog
  imports ProvableOpt_Common
begin

text \<open>PO-T1, the KERNEL BRIDGE. ``ProvableOpt_Common`` proves the lossless
  demand-restriction theorem for an abstract monotone operator \<open>T\<close> and a set \<open>D\<close>
  satisfying the *semantic* condition \<open>demand_closed T D\<close>. fieldrun's checker
  (``lo3a/demand_closure.py``) instead establishes a *syntactic* condition on the
  emitted Datalog program. This theory closes the gap: it models a Datalog program
  as a rule-set, defines its immediate-consequence operator \<open>T_P\<close>, and proves that
  the SYNTACTIC check the tool performs already implies the semantic
  \<open>demand_closed\<close> the lossless guarantee needs. So the checker's output \<open>D\<close>, once
  syntactically demand-closed, plugs into ``demand_restrict_query`` and the decode
  is *provably* preserved on the real \<open>\<Pi>\<close> -- upgrading "premise certified by a
  tool" to "premise proved" (modulo the parser faithfully reading the `.dl`).

  Model: a program is a set of \<open>(head, body)\<close> rules over ground atoms \<open>'a\<close>; \<open>body\<close>
  is the set of atoms that must all hold to fire the rule (EDB facts are empty-body
  rules). This is the standard ground \<open>T_P\<close> / least-fixpoint Datalog semantics.\<close>

type_synonym 'a "rule" = "'a \<times> 'a set"
type_synonym 'a program = "'a rule set"

definition T_P :: "'a program \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "T_P R S = {h. \<exists>b. (h, b) \<in> R \<and> b \<subseteq> S}"

lemma T_P_mono: "mono (T_P R)"
  by (rule monoI) (auto simp: T_P_def)

text \<open>\<open>D\<close> is SYNTACTICALLY demand-closed for \<open>R\<close> when every rule whose head is a
  kept atom (\<open>\<in> D\<close>) has its whole body inside \<open>D\<close> -- "the producers of a kept atom
  read only kept atoms". This is exactly the static check the demand-closure tool
  runs over the rules (transitive closure of demand from the query, then verify no
  kept relation is produced from a dropped one).\<close>

definition syn_demand_closed :: "'a program \<Rightarrow> 'a set \<Rightarrow> bool" where
  "syn_demand_closed R D \<longleftrightarrow> (\<forall>(h, b) \<in> R. h \<in> D \<longrightarrow> b \<subseteq> D)"

text \<open>THE BRIDGE: the syntactic check implies the semantic demand-closure.\<close>

theorem syn_demand_closed_imp_demand_closed:
  assumes syn: "syn_demand_closed R D"
  shows "demand_closed (T_P R) D"
  unfolding demand_closed_def
proof (intro allI)
  fix S
  show "T_P R S \<inter> D = T_P R (S \<inter> D) \<inter> D"
  proof
    show "T_P R S \<inter> D \<subseteq> T_P R (S \<inter> D) \<inter> D"
    proof
      fix x assume "x \<in> T_P R S \<inter> D"
      then obtain b where xb: "(x, b) \<in> R" "b \<subseteq> S" and xD: "x \<in> D"
        by (auto simp: T_P_def)
      from syn xb(1) xD have "b \<subseteq> D" by (fastforce simp: syn_demand_closed_def)
      with xb(2) have "b \<subseteq> S \<inter> D" by blast
      with xb(1) xD show "x \<in> T_P R (S \<inter> D) \<inter> D" by (auto simp: T_P_def)
    qed
    show "T_P R (S \<inter> D) \<inter> D \<subseteq> T_P R S \<inter> D"
      by (auto simp: T_P_def)
  qed
qed

text \<open>...and therefore (chaining ``ProvableOpt_Common``) the demand-restricted
  program preserves every query atom for free, from the syntactic check alone.\<close>

corollary syn_demand_closed_lossless:
  assumes "syn_demand_closed R D" and "Q \<subseteq> D"
  shows "lfp (T_P R) \<inter> Q = lfp (restrict_op (T_P R) D) \<inter> Q"
  by (rule demand_restrict_query[OF T_P_mono
        syn_demand_closed_imp_demand_closed[OF assms(1)] assms(2)])

section \<open>A concrete program mirroring the real `lastpos` structure\<close>

text \<open>The emitted \<open>\<Pi>\<close>'s final stratum (LOGIC_EXPORT / `whole_base.dl`):
  \<open>res p\<close> at every position is a fact, \<open>acc p\<close> (the final-norm \<open>xf\<close>/\<open>ssf\<close>) is
  derived per position, and \<open>logit\<close> reads only \<open>acc\<close> at \<open>lastpos = L\<close>. As a ground
  rule-set:\<close>

datatype datom = DRes nat | DAcc nat | DLogit

definition dprog :: "nat \<Rightarrow> datom program" where
  "dprog L =
     {(DRes p, {}) |p. p \<le> L}                 \<comment> \<open>residual facts at every position\<close>
   \<union> {(DAcc p, {DRes p}) |p. p \<le> L}           \<comment> \<open>accumulate per position\<close>
   \<union> {(DLogit, {DAcc L})}"                     \<comment> \<open>logit reads only lastpos L\<close>

text \<open>The kept set the checker returns: everything EXCEPT the dead stratum
  \<open>{DAcc p | p < L}\<close> (the per-position accumulate at non-final positions).\<close>

definition dkeep :: "nat \<Rightarrow> datom set" where
  "dkeep L = {DLogit} \<union> {DAcc L} \<union> {DRes p |p. p \<le> L}"

lemma dprog_syn_closed: "syn_demand_closed (dprog L) (dkeep L)"
  unfolding syn_demand_closed_def dprog_def dkeep_def by auto

text \<open>The program actually emits (\<open>DLogit\<close> is derived), so preservation is
  non-vacuous.\<close>

lemma DRes_in_lfp: "p \<le> L \<Longrightarrow> DRes p \<in> lfp (T_P (dprog L))"
  by (subst lfp_unfold[OF T_P_mono]) (auto simp: T_P_def dprog_def)

lemma DAcc_in_lfp: "p \<le> L \<Longrightarrow> DAcc p \<in> lfp (T_P (dprog L))"
proof (subst lfp_unfold[OF T_P_mono])
  assume "p \<le> L"
  hence "DRes p \<in> lfp (T_P (dprog L))" by (rule DRes_in_lfp)
  thus "DAcc p \<in> T_P (dprog L) (lfp (T_P (dprog L)))"
    using \<open>p \<le> L\<close> by (auto simp: T_P_def dprog_def)
qed

lemma DLogit_in_lfp: "DLogit \<in> lfp (T_P (dprog L))"
proof (subst lfp_unfold[OF T_P_mono])
  have "DAcc L \<in> lfp (T_P (dprog L))" by (rule DAcc_in_lfp) simp
  thus "DLogit \<in> T_P (dprog L) (lfp (T_P (dprog L)))" by (auto simp: T_P_def dprog_def)
qed

text \<open>The payoff, derived purely from the syntactic check via the bridge: the
  dead-stratum-restricted program preserves the decode \<open>DLogit\<close>.\<close>

theorem dprog_decode_preserved:
  "DLogit \<in> lfp (T_P (dprog L))
     \<longleftrightarrow> DLogit \<in> lfp (restrict_op (T_P (dprog L)) (dkeep L))"
proof -
  have "{DLogit} \<subseteq> dkeep L" by (simp add: dkeep_def)
  from syn_demand_closed_lossless[OF dprog_syn_closed this]
  have "lfp (T_P (dprog L)) \<inter> {DLogit}
          = lfp (restrict_op (T_P (dprog L)) (dkeep L)) \<inter> {DLogit}" .
  thus ?thesis by auto
qed

text \<open>...and the dropped stratum really is dropped: \<open>DAcc p\<close> for \<open>p < L\<close> is computed
  by the full program but absent from the restricted one.\<close>

lemma DAcc_dropped:
  assumes "p < L" shows "DAcc p \<notin> lfp (restrict_op (T_P (dprog L)) (dkeep L))"
proof
  assume "DAcc p \<in> lfp (restrict_op (T_P (dprog L)) (dkeep L))"
  moreover have "lfp (restrict_op (T_P (dprog L)) (dkeep L)) \<subseteq> dkeep L"
    by (rule lfp_lowerbound) (auto simp: restrict_op_def)
  ultimately have "DAcc p \<in> dkeep L" by blast
  thus False using assms by (auto simp: dkeep_def)
qed

theorem dprog_lossless_and_strict:
  assumes "p < L"
  shows "DAcc p \<in> lfp (T_P (dprog L))
       \<and> DAcc p \<notin> lfp (restrict_op (T_P (dprog L)) (dkeep L))
       \<and> (DLogit \<in> lfp (T_P (dprog L))
            \<longleftrightarrow> DLogit \<in> lfp (restrict_op (T_P (dprog L)) (dkeep L)))"
  using assms DAcc_in_lfp[of p L] DAcc_dropped[of p L] dprog_decode_preserved
  by auto

end
