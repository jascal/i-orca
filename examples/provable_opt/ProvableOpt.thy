theory ProvableOpt
  imports ProvableOpt_Common
begin

text \<open>PO-T4 / PO-T1 instance: the LOSSLESS DEMAND / DEAD-STRATUM (`lastpos`)
  transform on the exported semiring-Datalog program \<open>\<Pi>\<close> (fieldrun
  PROVABLE_OPT_PROPOSAL.md §5-6; LOGIC_EXPORT.md for the export of the model as
  \<open>\<Pi>\<close>). The general \<open>T_P\<close>-equivalence lives in ``ProvableOpt_Common``
  (\<open>demand_restrict_lfp\<close> / \<open>demand_restrict_query\<close>); here we instantiate it on the
  smallest \<open>\<Pi>\<close> that exhibits the transform faithfully and exhibit the saving.

  HONEST SCOPE. This certifies the LOSSLESS demand-restriction family
  (dead-stratum / `lastpos`), i.e. PO-T1 / the `--magic-transform` "nothing the
  query does not read" guarantee. It does NOT certify the full magic-sets
  ADORNMENT transform (binding-pattern specialisation); that stays open.\<close>

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
