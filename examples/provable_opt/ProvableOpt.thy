theory ProvableOpt
  imports Main
begin

text \<open>PO-T4 / PO-T1 (fieldrun PROVABLE_OPT_PROPOSAL.md): a machine-checked
  \<open>T_P\<close>-equivalence for the LOSSLESS DEMAND / DEAD-STRATUM transform on the
  exported semiring-Datalog program \<open>\<Pi>\<close>.

  The model's next-token computation is exported (LOGIC_EXPORT.md) as a Datalog
  program whose semantics is the least fixpoint of its immediate-consequence
  operator \<open>T_P\<close>. fieldrun's Souffle pipeline applies demand / dead-stratum
  rewrites (e.g. the `lastpos` restriction: `xf`, `ssf` are computed at every
  position but only `lastpos` is read by `logit`, so restrict them to `lastpos`).
  The proposal asks for ONE such transform carried with a kernel-checked
  \<open>T_P\<close>-equivalence proof; PO-T4 status there is "open".

  This theory closes that first rung. We model \<open>T_P\<close> as an arbitrary MONOTONE
  operator on atom-sets and the transform as restriction to a DEMAND-CLOSED set
  \<open>D\<close> (the atoms the query transitively reads). The general theorem
  (\<open>demand_restrict_lfp\<close>) proves the restricted fixpoint equals the full fixpoint
  projected onto \<open>D\<close>; the corollary (\<open>demand_restrict_query\<close>) proves the decode is
  preserved for EVERY context (EDB). Correctness is then a theorem about the
  fixpoint, not a measurement -- exactly PO-T1's claim.

  HONEST SCOPE. This certifies the LOSSLESS demand-restriction family
  (dead-stratum / `lastpos`), i.e. PO-T1 / the `--magic-transform` "nothing the
  query does not read" guarantee. It does NOT certify the full magic-sets
  ADORNMENT transform (which also specialises/reorders predicates by binding
  pattern); that is a strictly heavier equivalence and stays open. The concrete
  instance below is the smallest Datalog program that exhibits the `lastpos`
  saving faithfully, not a real bundle.\<close>

section \<open>The transformed operator and the demand-closure condition\<close>

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

section \<open>The general theorem: demand restriction preserves the fixpoint on D\<close>

text \<open>\<open>lfp (restrict_op T D) = lfp T \<inter> D\<close>: running the transformed program
  computes exactly the demanded part of the full least model. Proven by the two
  standard fixpoint moves -- \<open>lfp_lowerbound\<close> (least pre-fixpoint) and
  \<open>lfp_unfold\<close> (the fixpoint property) -- i.e. by induction on \<open>T_P\<close>, as the
  proposal says it must be.\<close>

theorem demand_restrict_lfp:
  assumes mono: "mono T"
      and dc:   "demand_closed T D"
  shows "lfp (restrict_op T D) = lfp T \<inter> D"
proof -
  have monoT': "mono (restrict_op T D)" using mono by (rule mono_restrict_op)
  from dc have dcS: "\<And>S. T S \<inter> D = T (S \<inter> D) \<inter> D"
    by (simp add: demand_closed_def)

  \<comment> \<open>(1) \<open>lfp T'\<close> is below \<open>lfp T \<inter> D\<close>, because the latter is a fixpoint of \<open>T'\<close>.\<close>
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

  \<comment> \<open>\<open>lfp T'\<close> only ever contains demanded atoms.\<close>
  have subD: "lfp (restrict_op T D) \<subseteq> D"
  proof -
    have "lfp (restrict_op T D) = restrict_op T D (lfp (restrict_op T D))"
      by (metis lfp_unfold[OF monoT'])
    also have "\<dots> \<subseteq> D" by (simp add: restrict_op_def)
    finally show ?thesis .
  qed

  \<comment> \<open>(2) \<open>lfp T \<inter> D \<subseteq> lfp T'\<close>: show \<open>lfp T' \<union> (-D)\<close> is a pre-fixpoint of \<open>T\<close>.\<close>
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

section \<open>A concrete instance: the `lastpos` dead-stratum restriction\<close>

text \<open>The smallest \<open>\<Pi>\<close> that exhibits the transform faithfully. Positions
  \<open>0..L\<close>; \<open>L\<close> is `lastpos`. \<open>Res p\<close> (a residual feature at position \<open>p\<close>) is an
  EDB fact for every \<open>p \<le> L\<close>; \<open>Acc p\<close> (the per-position accumulate / final-norm)
  is derived from \<open>Res p\<close>; the single output \<open>Logit\<close> reads only \<open>Acc L\<close>. So the
  query demands only the \<open>lastpos\<close> stratum, and the dead-stratum transform may
  drop \<open>Acc p\<close> for \<open>p \<noteq> L\<close>.\<close>

datatype atom = Res nat | Acc nat | Logit

definition Tlm :: "nat \<Rightarrow> atom set \<Rightarrow> atom set" where
  "Tlm L S =
     {a. \<exists>p\<le>L. a = Res p}                 \<comment> \<open>residual present at every position (facts)\<close>
   \<union> {a. \<exists>p. a = Acc p \<and> Res p \<in> S}      \<comment> \<open>accumulate at p from residual at p\<close>
   \<union> {a. a = Logit \<and> Acc L \<in> S}"          \<comment> \<open>logit reads only lastpos L\<close>

definition Dlm :: "nat \<Rightarrow> atom set" where
  "Dlm L = {Logit, Acc L, Res L}"          \<comment> \<open>what Logit transitively demands\<close>

lemma Tlm_mono: "mono (Tlm L)"
  by (auto simp: Tlm_def mono_def)

lemma Tlm_demand_closed: "demand_closed (Tlm L) (Dlm L)"
  unfolding demand_closed_def
proof (intro allI)
  fix S show "Tlm L S \<inter> Dlm L = Tlm L (S \<inter> Dlm L) \<inter> Dlm L"
    by (auto simp: Tlm_def Dlm_def)
qed

text \<open>The instance of the general \<open>T_P\<close>-equivalence: the transformed program
  computes exactly the demanded slice of the full least model.\<close>

theorem Tlm_demand_restrict_lfp:
  "lfp (restrict_op (Tlm L) (Dlm L)) = lfp (Tlm L) \<inter> Dlm L"
  by (rule demand_restrict_lfp[OF Tlm_mono Tlm_demand_closed])

text \<open>LOSSLESS on the decode: \<open>Logit\<close> is derivable iff it is derivable after the
  transform -- for the model itself \<open>Logit\<close> IS derivable, so this is a genuine
  (non-vacuous) preservation, not "both false".\<close>

lemma Res_in_full: "p \<le> L \<Longrightarrow> Res p \<in> lfp (Tlm L)"
  by (subst lfp_unfold[OF Tlm_mono]) (auto simp: Tlm_def)

lemma Acc_in_full: "p \<le> L \<Longrightarrow> Acc p \<in> lfp (Tlm L)"
proof (subst lfp_unfold[OF Tlm_mono])
  assume "p \<le> L"
  hence "Res p \<in> lfp (Tlm L)" by (rule Res_in_full)
  thus "Acc p \<in> Tlm L (lfp (Tlm L))" by (auto simp: Tlm_def)
qed

lemma Logit_in_full: "Logit \<in> lfp (Tlm L)"
proof (subst lfp_unfold[OF Tlm_mono])
  have "Acc L \<in> lfp (Tlm L)" by (rule Acc_in_full) simp
  thus "Logit \<in> Tlm L (lfp (Tlm L))" by (auto simp: Tlm_def)
qed

corollary Tlm_decode_preserved:
  "Logit \<in> lfp (Tlm L) \<longleftrightarrow> Logit \<in> lfp (restrict_op (Tlm L) (Dlm L))"
proof -
  have "{Logit} \<subseteq> Dlm L" by (simp add: Dlm_def)
  from demand_restrict_query[OF Tlm_mono Tlm_demand_closed this]
  have "lfp (Tlm L) \<inter> {Logit} = lfp (restrict_op (Tlm L) (Dlm L)) \<inter> {Logit}" .
  thus ?thesis by auto
qed

lemma Logit_in_restricted: "Logit \<in> lfp (restrict_op (Tlm L) (Dlm L))"
  using Logit_in_full Tlm_decode_preserved by blast

text \<open>NON-VACUOUS SAVING: the full program derives \<open>Acc p\<close> at every position, but
  the transformed program drops \<open>Acc p\<close> for every \<open>p \<noteq> L\<close> (the "final-norm at
  one position, not all" rewrite). So for any \<open>L \<ge> 1\<close> the transform removes work
  while preserving the decode.\<close>

lemma lfp_restricted_subset_D: "lfp (restrict_op (Tlm L) (Dlm L)) \<subseteq> Dlm L"
  using Tlm_demand_restrict_lfp by auto

lemma Acc_dropped:
  assumes "p \<noteq> L" shows "Acc p \<notin> lfp (restrict_op (Tlm L) (Dlm L))"
proof
  assume "Acc p \<in> lfp (restrict_op (Tlm L) (Dlm L))"
  with lfp_restricted_subset_D have "Acc p \<in> Dlm L" by blast
  thus False using assms by (auto simp: Dlm_def)
qed

theorem lastpos_transform_lossless_and_strict:
  assumes "p < L"
  shows "Acc p \<in> lfp (Tlm L)                                  \<comment> \<open>full computes it\<close>
       \<and> Acc p \<notin> lfp (restrict_op (Tlm L) (Dlm L))            \<comment> \<open>transform drops it\<close>
       \<and> (Logit \<in> lfp (Tlm L)
            \<longleftrightarrow> Logit \<in> lfp (restrict_op (Tlm L) (Dlm L)))"  \<comment> \<open>decode preserved\<close>
  using assms Acc_in_full[of p L] Acc_dropped[of p L] Tlm_decode_preserved
  by auto

end
