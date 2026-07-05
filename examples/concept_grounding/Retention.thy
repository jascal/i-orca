(*
  Retention.thy -- C9: RETENTION BY COMPILATION (the self-compiling learner's central claim,
  made a theorem over its stated structure).

  Follow-on from the Wyly self-compilation arc (pil wyly_selfcompile / wyly_lm_v2..v5): sleep
  compiles a learned circuit into a GUARDED EXACT RULE and installs it with PREEMPT semantics --
  where a rule fires (inside its guard), it REPLACES the soft model's output. The experiment
  showed 1.000/1.000/1.000 curriculum retention vs 0.010/0.002/0.007 for a matched-budget
  baseline; this theory shows the retention is a property of the SEMANTICS, not of training
  dynamics:

    * COVER_SOFT_INDEPENDENT: on the covered domain (the union of installed guards), the cover's
      output does not depend on the soft function AT ALL.
    * RETENTION_BY_COMPILATION: along ANY trajectory of soft functions (any sequence of weight
      updates, any optimizer, any task), behavior on the covered domain is constant in time.
    * CERTIFIED_ACCURACY_INVARIANT: agreement with any target on any finite certified subset of
      the covered domain is invariant under training -- zero forgetting, exactly.
    * COVER_OFF_DOMAIN: off the covered domain the cover IS the soft function -- rules never
      touch the plastic remainder (the complement statement: compilation frees capacity without
      constraining it).
    * FIRED_RULE_DECIDES + COVER_ORDER_IRRELEVANT: with pairwise-disjoint guards, the firing rule
      alone determines the answer and the installation ORDER is irrelevant -- the formal
      obligation the curriculum experiment discharged empirically with disjoint token ranges.
      Without disjointness, first-match order is load-bearing (and the theorem says exactly when).

  Honest scope: rules here are arbitrary exact functions with arbitrary guard sets -- nothing is
  claimed about WHAT was compiled being correct (that is the Souffle certificate's job, over its
  own stated domain), only that once installed, certified-domain behavior cannot drift. The
  guard-disjointness premise is stated, not assumed silently.
*)
theory Retention
  imports Main
begin

section \<open>The preempting cover\<close>

text \<open>A guarded exact rule is a pair (guard set, program). The cover applies the FIRST rule
  whose guard contains the input; if none fires, the soft function answers. This is the package
  runtime's trusted-tier semantics and the learner's install semantics.\<close>

type_synonym ('x, 'y) grule = "'x set \<times> ('x \<Rightarrow> 'y)"

fun cover :: "('x, 'y) grule list \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> 'x \<Rightarrow> 'y" where
  "cover [] soft x = soft x"
| "cover (r # rs) soft x = (if x \<in> fst r then snd r x else cover rs soft x)"

definition covered :: "('x, 'y) grule list \<Rightarrow> 'x set" where
  "covered rs = (\<Union>r\<in>set rs. fst r)"

section \<open>C9(i): the covered domain is independent of the weights\<close>

lemma cover_soft_independent:
  assumes "x \<in> covered rs"
  shows "cover rs soft x = cover rs soft' x"
  using assms by (induction rs) (auto simp: covered_def)

lemma cover_off_domain:
  assumes "x \<notin> covered rs"
  shows "cover rs soft x = soft x"
  using assms by (induction rs) (auto simp: covered_def)

section \<open>C9(ii): retention along any training trajectory\<close>

theorem retention_by_compilation:
  fixes traj :: "'i \<Rightarrow> 'x \<Rightarrow> 'y"  \<comment> \<open>the soft function indexed by training time; t, s any two instants\<close>
  assumes "x \<in> covered rs"
  shows "cover rs (traj t) x = cover rs (traj s) x"
  using assms by (rule cover_soft_independent)

theorem certified_accuracy_invariant:
  fixes traj :: "'i \<Rightarrow> 'x \<Rightarrow> 'y" and tgt :: "'x \<Rightarrow> 'y"
  assumes sub: "S \<subseteq> covered rs"
  shows "{x \<in> S. cover rs (traj t) x = tgt x} = {x \<in> S. cover rs (traj s) x = tgt x}"
proof -
  have eq: "\<And>x. x \<in> S \<Longrightarrow> cover rs (traj t) x = cover rs (traj s) x"
    using sub by (blast intro: cover_soft_independent)
  show ?thesis
  proof (rule set_eqI)
    fix x
    show "x \<in> {x \<in> S. cover rs (traj t) x = tgt x}
        \<longleftrightarrow> x \<in> {x \<in> S. cover rs (traj s) x = tgt x}"
      using eq[of x] by auto
  qed
qed

corollary certified_agreement_count_invariant:
  fixes traj :: "'i \<Rightarrow> 'x \<Rightarrow> 'y" and tgt :: "'x \<Rightarrow> 'y"
  assumes "S \<subseteq> covered rs"
  shows "card {x \<in> S. cover rs (traj t) x = tgt x}
       = card {x \<in> S. cover rs (traj s) x = tgt x}"
proof -
  have "{x \<in> S. cover rs (traj t) x = tgt x} = {x \<in> S. cover rs (traj s) x = tgt x}"
    by (rule certified_accuracy_invariant[OF assms])
  then show ?thesis by (rule arg_cong)
qed

section \<open>C9(iii): disjoint guards make the firing rule sovereign and the order irrelevant\<close>

lemma fired_rule_decides:
  assumes "pairwise (\<lambda>a b. fst a \<inter> fst b = {}) (set rs)"
      and "r \<in> set rs" and "x \<in> fst r"
  shows "cover rs soft x = snd r x"
  using assms
proof (induction rs)
  case Nil
  then show ?case by simp
next
  case (Cons h rs)
  show ?case
  proof (cases "x \<in> fst h")
    case True
    have "h = r"
    proof (rule ccontr)
      assume ne: "h \<noteq> r"
      have "fst h \<inter> fst r = {}"
        using Cons.prems(1) Cons.prems(2) ne by (auto dest: pairwiseD)
      then show False using True Cons.prems(3) by auto
    qed
    then show ?thesis using True by simp
  next
    case False
    then have rin: "r \<in> set rs"
      using Cons.prems(2) Cons.prems(3) by auto
    have pw: "pairwise (\<lambda>a b. fst a \<inter> fst b = {}) (set rs)"
      using Cons.prems(1) by (auto intro: pairwise_subset)
    show ?thesis
      using False Cons.IH[OF pw rin Cons.prems(3)] by simp
  qed
qed

theorem cover_order_irrelevant:
  assumes disj: "pairwise (\<lambda>a b. fst a \<inter> fst b = {}) (set rs)"
      and same: "set rs' = set rs"
  shows "cover rs soft x = cover rs' soft x"
proof (cases "x \<in> covered rs")
  case True
  then obtain r where r1: "r \<in> set rs" and r2: "x \<in> fst r"
    by (auto simp: covered_def)
  have disj2: "pairwise (\<lambda>a b. fst a \<inter> fst b = {}) (set rs')"
    using disj same by simp
  have r1': "r \<in> set rs'"
    using r1 same by simp
  have L: "cover rs soft x = snd r x"
    using disj r1 r2 by (rule fired_rule_decides)
  have R: "cover rs' soft x = snd r x"
    using disj2 r1' r2 by (rule fired_rule_decides)
  from L R show ?thesis by simp
next
  case False
  then have "x \<notin> covered rs'" using same by (simp add: covered_def)
  with False show ?thesis by (simp add: cover_off_domain)
qed

end
