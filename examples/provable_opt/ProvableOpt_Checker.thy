theory ProvableOpt_Checker
  imports ProvableOpt_Datalog
begin

text \<open>PO-T1, the VERIFIED DECISION PROCEDURE rung. ``ProvableOpt_Datalog`` proves
  that the *syntactic* condition \<open>syn_demand_closed\<close> entails the lossless guarantee,
  but \<open>syn_demand_closed\<close> is a quantified predicate over a set of rules -- the same
  thing fieldrun's ``lo3a/demand_closure.py`` decides, in Python, on trust. Here we
  give an EXECUTABLE Isabelle decision procedure \<open>echeck\<close> for it, prove it FAITHFUL
  (\<open>echeck ER KD \<longleftrightarrow> syn_demand_closed (prog_of ER) (set KD)\<close>), and show the lossless
  guarantee can be obtained by *running* it (\<open>by eval\<close>) -- so the checker's verdict
  is computed by kernel-trusted code, not asserted by an external tool.

  This shrinks the trusted base of the whole real-bundle line to a single
  irreducible boundary: the PARSER (`.dl` text \<open>\<rightarrow>\<close> the rule list). Everything from
  the rule list onward -- the demand-closure decision and its lossless consequence
  -- is now machine-checked.

  Executable representation: a rule with a LIST body, abstracted to the set-model of
  ``ProvableOpt_Datalog`` by \<open>prog_of\<close>.\<close>

type_synonym 'a lrule = "'a \<times> 'a list"

definition prog_of :: "'a lrule list \<Rightarrow> 'a program" where
  "prog_of ER = set (map (\<lambda>(h, b). (h, set b)) ER)"

text \<open>The decision procedure: every rule whose head is a kept atom has every body
  atom kept. Pure list operations -- code-generatable for any \<open>'a\<close> with equality.\<close>

definition echeck :: "'a lrule list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "echeck ER KD = list_all (\<lambda>(h, b). h \<in> set KD \<longrightarrow> list_all (\<lambda>x. x \<in> set KD) b) ER"

text \<open>FAITHFULNESS: \<open>echeck\<close> decides exactly \<open>syn_demand_closed\<close> on the abstracted
  program (sound AND complete, so the Python check has a precise kernel meaning).\<close>

theorem echeck_iff:
  "echeck ER KD \<longleftrightarrow> syn_demand_closed (prog_of ER) (set KD)"
  by (auto simp: echeck_def prog_of_def syn_demand_closed_def list_all_iff subset_eq)

text \<open>...so a PASS from the executable checker yields the lossless decode guarantee
  directly, via the ``ProvableOpt_Datalog`` bridge and ``ProvableOpt_Common``.\<close>

theorem echeck_lossless:
  assumes "echeck ER KD" and "Q \<subseteq> set KD"
  shows "lfp (T_P (prog_of ER)) \<inter> Q
           = lfp (restrict_op (T_P (prog_of ER)) (set KD)) \<inter> Q"
  using syn_demand_closed_lossless[OF echeck_iff[THEN iffD1, OF assms(1)] assms(2)] .

section \<open>Running the verified checker on the real `lastpos` fragment\<close>

text \<open>The emitted \<open>\<Pi>\<close>'s final stratum as an EXECUTABLE rule list (the same program
  ``dprog`` of ``ProvableOpt_Datalog`` modelled as a set): \<open>res p\<close> facts at every
  position \<open>0..L\<close>, \<open>acc p\<close> per position, \<open>logit\<close> from \<open>acc L\<close>. The kept set drops the
  dead stratum \<open>{acc p | p < L}\<close>.\<close>

definition dprog_e :: "nat \<Rightarrow> datom lrule list" where
  "dprog_e L = map (\<lambda>p. (DRes p, [])) [0..<Suc L]
             @ map (\<lambda>p. (DAcc p, [DRes p])) [0..<Suc L]
             @ [(DLogit, [DAcc L])]"

definition dkeep_e :: "nat \<Rightarrow> datom list" where
  "dkeep_e L = DLogit # DAcc L # map DRes [0..<Suc L]"

text \<open>\<open>prog_of (dprog_e L)\<close> is exactly the abstract ``dprog L`` and \<open>set (dkeep_e L)\<close>
  is ``dkeep L`` -- so the executable instance and the hand-modelled one coincide.\<close>

lemma prog_of_dprog_e: "prog_of (dprog_e L) = dprog L"
  by (auto simp: prog_of_def dprog_e_def dprog_def)

lemma set_dkeep_e: "set (dkeep_e L) = dkeep L"
  by (auto simp: dkeep_e_def dkeep_def)

text \<open>THE PAYOFF: the verified checker is EXECUTED by the kernel (\<open>by eval\<close>) and its
  pass is turned into the lossless decode guarantee for the concrete program -- no
  hand proof of demand-closure, and no trust in the external tool.\<close>

lemma dprog_e_checks: "echeck (dprog_e 5) (dkeep_e 5)"
  by eval

theorem executable_checker_certifies_lossless:
  "lfp (T_P (dprog 5)) \<inter> {DLogit}
     = lfp (restrict_op (T_P (dprog 5)) (dkeep 5)) \<inter> {DLogit}"
proof -
  have run: "echeck (dprog_e 5) (dkeep_e 5)" by eval
  have "{DLogit} \<subseteq> set (dkeep_e 5)" by (simp add: dkeep_e_def)
  from echeck_lossless[OF run this]
  show ?thesis by (simp add: prog_of_dprog_e set_dkeep_e)
qed

text \<open>The procedure really is extractable code (the form one would diff against the
  Python checker).\<close>

export_code echeck in SML module_name DemandClosureChecker

end
