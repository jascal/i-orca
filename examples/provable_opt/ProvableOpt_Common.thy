theory ProvableOpt_Common
  imports Complex_Main
begin

text \<open>The reusable, corpus-independent core of fieldrun's PROVABLE_OPT theory
  (PROVABLE_OPT_PROPOSAL.md). Two families of general theorems, each instantiated
  by a thin concrete corpus in this directory:

  - PO-T1 (lossless): the demand / dead-stratum ``T_P``-equivalence on the exported
    Datalog program ``\<Pi>`` (instantiated by ``ProvableOpt.thy``, the `lastpos` rung).
  - PO-T3 (decode-lossless): the margin certificate — a logit perturbation bounded
    by ``\<delta>`` preserves the decode on every token with margin ``> 2\<delta>`` (instantiated by
    ``ProvableOpt_Margin.thy``).

  Keeping the general results here is the "shared `PO_T1` extraction" asked for in
  review: later rungs (real-bundle ``\<Pi>``, magic-sets adornment) import and instantiate
  rather than re-prove.\<close>

section \<open>PO-T1 — the lossless demand / dead-stratum transform\<close>

text \<open>\<open>restrict_op T D\<close> is the immediate-consequence operator of the transformed
  program \<open>\<Pi>'\<close>: derive as before, but keep only the demanded atoms \<open>D\<close>.\<close>

definition restrict_op :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "restrict_op T D = (\<lambda>S. T S \<inter> D)"

text \<open>\<open>D\<close> is DEMAND-CLOSED for \<open>T\<close> when the producers of a \<open>D\<close>-atom read only
  \<open>D\<close>-atoms: the one-step \<open>D\<close>-consequences of \<open>S\<close> depend on \<open>S\<close> only through
  \<open>S \<inter> D\<close>. This is precisely the structural fact that licenses the `lastpos`
  restriction -- the rules deriving a `lastpos` atom mention only `lastpos`
  atoms (a stratum boundary / a closed demand frontier).\<close>

definition demand_closed :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "demand_closed T D \<longleftrightarrow> (\<forall>S. T S \<inter> D = T (S \<inter> D) \<inter> D)"

lemma mono_restrict_op:
  assumes "mono T"
  shows "mono (restrict_op T D)"
  using assms by (auto simp: restrict_op_def mono_def)

text \<open>\<open>lfp (restrict_op T D) = lfp T \<inter> D\<close>: running the transformed program
  computes exactly the demanded part of the full least model. Proven by the two
  standard fixpoint moves -- \<open>lfp_lowerbound\<close> (least pre-fixpoint) and
  \<open>lfp_unfold\<close> (the fixpoint property) -- i.e. by induction on \<open>T_P\<close>, as the
  proposal says it must be.

  KEY INSIGHT (the \<open>\<supseteq>\<close> direction, where demand-closure pays). We show
  \<open>lfp T' \<union> (-D)\<close> is a pre-fixpoint of the FULL \<open>T\<close>. A newly derived atom \<open>x \<notin> D\<close>
  is absorbed by \<open>-D\<close>; a newly derived \<open>x \<in> D\<close> is produced -- by \<open>demand_closed\<close> --
  using only \<open>D\<close>-atoms, which on \<open>lfp T' \<union> (-D)\<close> are exactly \<open>lfp T'\<close>, so \<open>x\<close> is
  already in \<open>lfp T'\<close>. Hence no derivation the transform DROPS can ever feed a
  demanded atom: the dropped strata are invisible to every query in \<open>D\<close>. The proof
  is fully manual structured Isar (no Sledgehammer); \<open>metis\<close> only discharges the
  equational glue produced by the \<open>demand_closed\<close> rewrite.\<close>

theorem demand_restrict_lfp:
  assumes mono: "mono T"
      and dc:   "demand_closed T D"
  shows "lfp (restrict_op T D) = lfp T \<inter> D"
proof -
  have monoT': "mono (restrict_op T D)" using mono by (rule mono_restrict_op)
  from dc have dcS: "\<And>S. T S \<inter> D = T (S \<inter> D) \<inter> D"
    by (simp add: demand_closed_def)

  have fixR: "restrict_op T D (lfp T \<inter> D) = lfp T \<inter> D"
  proof -
    have "restrict_op T D (lfp T \<inter> D) = T (lfp T \<inter> D) \<inter> D"
      by (simp add: restrict_op_def)
    also have "\<dots> = T (lfp T) \<inter> D" by (metis dcS)
    also have "\<dots> = lfp T \<inter> D" by (metis lfp_unfold[OF mono])
    finally show ?thesis .
  qed
  have le1: "lfp (restrict_op T D) \<subseteq> lfp T \<inter> D"
    by (rule lfp_lowerbound) (simp add: fixR)

  have subD: "lfp (restrict_op T D) \<subseteq> D"
  proof -
    have "lfp (restrict_op T D) = restrict_op T D (lfp (restrict_op T D))"
      by (metis lfp_unfold[OF monoT'])
    also have "\<dots> \<subseteq> D" by (simp add: restrict_op_def)
    finally show ?thesis .
  qed

  have pre: "T (lfp (restrict_op T D) \<union> (- D)) \<subseteq> lfp (restrict_op T D) \<union> (- D)"
  proof
    fix x assume x: "x \<in> T (lfp (restrict_op T D) \<union> (- D))"
    show "x \<in> lfp (restrict_op T D) \<union> (- D)"
    proof (cases "x \<in> D")
      case False thus ?thesis by simp
    next
      case True
      have "x \<in> T (lfp (restrict_op T D) \<union> (- D)) \<inter> D" using x True by simp
      also have "T (lfp (restrict_op T D) \<union> (- D)) \<inter> D
                   = T ((lfp (restrict_op T D) \<union> (- D)) \<inter> D) \<inter> D"
        by (rule dcS)
      also have "(lfp (restrict_op T D) \<union> (- D)) \<inter> D = lfp (restrict_op T D)"
        using subD by auto
      finally have "x \<in> T (lfp (restrict_op T D)) \<inter> D" .
      hence "x \<in> restrict_op T D (lfp (restrict_op T D))"
        by (simp add: restrict_op_def)
      also have "\<dots> = lfp (restrict_op T D)" by (metis lfp_unfold[OF monoT'])
      finally show ?thesis by simp
    qed
  qed
  have "lfp T \<subseteq> lfp (restrict_op T D) \<union> (- D)"
    by (rule lfp_lowerbound) (rule pre)
  hence le2: "lfp T \<inter> D \<subseteq> lfp (restrict_op T D)" using subD by auto

  from le1 le2 show ?thesis by auto
qed

corollary demand_restrict_query:
  assumes "mono T" and "demand_closed T D" and "Q \<subseteq> D"
  shows "lfp T \<inter> Q = lfp (restrict_op T D) \<inter> Q"
proof -
  have "lfp (restrict_op T D) \<inter> Q = (lfp T \<inter> D) \<inter> Q"
    using demand_restrict_lfp[OF assms(1,2)] by simp
  also have "\<dots> = lfp T \<inter> Q" using \<open>Q \<subseteq> D\<close> by auto
  finally show ?thesis by simp
qed

section \<open>PO-T3 — the margin-certified decode invariance\<close>

text \<open>PO-T1 and PO-T3 are the two complementary faces of "provable optimization".
  PO-T1 is the EXACT / STRUCTURAL face: a demand-closed rewrite preserves the whole
  least model on the query, losslessly, for every input. PO-T3 is the APPROXIMATE /
  QUANTITATIVE face: a rewrite that only *perturbs* the logits (it changes the
  numbers, so PO-T1's exactness is gone) still preserves the DECODE, but only where
  there is enough margin to absorb the perturbation. PO-T1 covers the part of \<open>\<Pi>\<close>
  the query does not read; PO-T3 covers the part it does read but does not depend on
  sharply. Together they are the lossless and the margin-bounded halves of the same
  "optimize \<open>\<Pi>\<close>, carry a proof" program.\<close>

text \<open>A logit vector \<open>L : 'tok \<Rightarrow> real\<close> over a token set \<open>V\<close> decodes to its strict
  argmax. A transform that perturbs each logit by at most \<open>\<delta>\<close> (e.g. dropping a
  margin-dominated neuron) preserves the decode on every token whose margin
  exceeds \<open>2\<delta>\<close>.

  HONEST BOUNDEDNESS. The certificate is SILENT when the margin is \<open>\<le> 2\<delta>\<close> --
  exactly the small-margin / dense-\<open>G\<close> forge-tax tokens (fieldrun PO-T3, bounded
  globally by LE-T2). It is a sound LOCAL certificate, not a global one; the
  ``ProvableOpt_Margin`` instance exhibits a small-margin token where an
  equally-bounded perturbation flips the decode, so the \<open>2\<delta>\<close> guard is necessary.\<close>

definition decodes_to :: "('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "decodes_to L V t \<longleftrightarrow> t \<in> V \<and> (\<forall>v\<in>V. v \<noteq> t \<longrightarrow> L v < L t)"

definition margin :: "('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> real" where
  "margin L V t = L t - Max (L ` (V - {t}))"

text \<open>The certificate in pointwise form (no finiteness needed): if every competitor
  trails \<open>t\<close> by more than \<open>2\<delta>\<close> under \<open>L\<close>, a \<open>\<delta>\<close>-bounded perturbation keeps \<open>t\<close> the
  strict argmax.\<close>

theorem decode_margin_certified:
  assumes pert: "\<And>v. v \<in> V \<Longrightarrow> \<bar>L' v - L v\<bar> \<le> \<delta>"
      and tV:   "t \<in> V"
      and marg: "\<And>v. v \<in> V \<Longrightarrow> v \<noteq> t \<Longrightarrow> L t - L v > 2 * \<delta>"
  shows "decodes_to L' V t"
  unfolding decodes_to_def
proof (intro conjI ballI impI)
  show "t \<in> V" by (rule tV)
next
  fix v assume v: "v \<in> V" and ne: "v \<noteq> t"
  have b1: "L' t - L t \<le> \<delta> \<and> - \<delta> \<le> L' t - L t"
    using pert[OF tV] by (simp add: abs_le_iff)
  have b2: "L' v - L v \<le> \<delta> \<and> - \<delta> \<le> L' v - L v"
    using pert[OF v] by (simp add: abs_le_iff)
  have b3: "L t - L v > 2 * \<delta>" by (rule marg[OF v ne])
  from b1 b2 b3 show "L' v < L' t" by linarith
qed

text \<open>The same, with the margin written as the gap to the best competitor (the
  ``margin L V t > 2\<delta>`` form fieldrun states), for a finite token set. The
  \<open>finite V\<close> precondition is what lets \<open>margin\<close> use \<open>Max\<close>; it holds for any real
  vocabulary (finite) -- only an idealised infinite-vocabulary model would need the
  pointwise ``decode_margin_certified`` instead.\<close>

corollary decode_margin_Max_certified:
  assumes fin:    "finite V"          \<comment> \<open>real vocabularies are finite; needed for \<open>Max\<close>\<close>
      and nonemp: "V - {t} \<noteq> {}"
      and tV:     "t \<in> V"
      and pert:   "\<And>v. v \<in> V \<Longrightarrow> \<bar>L' v - L v\<bar> \<le> \<delta>"
      and m:      "margin L V t > 2 * \<delta>"
  shows "decodes_to L' V t"
proof (rule decode_margin_certified[OF pert tV])
  fix v assume v: "v \<in> V" and ne: "v \<noteq> t"
  have "L v \<le> Max (L ` (V - {t}))"
  proof (rule Max_ge)
    show "finite (L ` (V - {t}))" using fin by blast
    show "L v \<in> L ` (V - {t})" using v ne by blast
  qed
  thus "L t - L v > 2 * \<delta>" using m unfolding margin_def by linarith
qed

end
