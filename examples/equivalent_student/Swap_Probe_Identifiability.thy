theory Swap_Probe_Identifiability
  imports Node_Mask_Clamp
begin

section \<open>What swap probes can and cannot identify\<close>

text \<open>Three facts about interchange (swap) tests, each proved on a small explicit model.

  P1. Passing every single-node swap and the plain output does not imply passing a swap of two nodes.
  P2. On a host with a redundant pair of nodes, the single-node ablation screen can clamp both members;
      each member alone is a maximal valid clamp, so the valid masks are not unique.
  P3. For a student built from the host's own mechanisms by clamping some nodes to constants, passing the
      plain output and the single-node swaps of every free node forces the clamp set to be empty on that
      redundant host. The swap criterion, not minimality, decides which nodes must stay.\<close>

subsection \<open>P1: single swaps do not imply a joint swap\<close>

datatype n4 = N0 | N1 | N2 | N3

definition ord4 :: "n4 list" where "ord4 = [N0, N1, N2, N3]"

definition copy_mech :: "(bool, n4, bool) mechanisms" where
  "copy_mech n x env = x"

definition cnt4 :: "(n4 \<Rightarrow> bool) \<Rightarrow> nat" where
  "cnt4 env = length (filter id [env N0, env N1, env N2, env N3])"

text \<open>Host: true when at least two of four duplicated copies of the input are true.
Student: true when at least three are.\<close>

definition rd_host :: "(n4 \<Rightarrow> bool) \<Rightarrow> bool" where "rd_host env = (2 \<le> cnt4 env)"
definition rd_stud :: "(n4 \<Rightarrow> bool) \<Rightarrow> bool" where "rd_stud env = (3 \<le> cnt4 env)"

abbreviation out4 :: "((n4 \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> (n4 \<Rightarrow> bool option) \<Rightarrow> bool" where
  "out4 rd x ov \<equiv> eval copy_mech ord4 rd False x ov"

abbreviation swap4 :: "((n4 \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> n4 set \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "swap4 rd S a b \<equiv> out4 rd a (swap_ov copy_mech ord4 False S b (\<lambda>_. None))"

theorem single_swaps_not_enough:
  shows "\<forall>x. out4 rd_host x (\<lambda>_. None) = out4 rd_stud x (\<lambda>_. None)"
    and "\<forall>n a b. swap4 rd_host {n} a b = swap4 rd_stud {n} a b"
    and "\<exists>a b. swap4 rd_host {N0, N1} a b \<noteq> swap4 rd_stud {N0, N1} a b"
proof -
  show "\<forall>x. out4 rd_host x (\<lambda>_. None) = out4 rd_stud x (\<lambda>_. None)"
    by (auto simp: eval_def run_env_def step_def ord4_def copy_mech_def rd_host_def rd_stud_def cnt4_def)
  show "\<forall>n a b. swap4 rd_host {n} a b = swap4 rd_stud {n} a b"
  proof (intro allI)
    fix n a b
    show "swap4 rd_host {n} a b = swap4 rd_stud {n} a b"
      by (cases n; cases a; cases b)
         (simp_all add: eval_def run_env_def step_def swap_ov_def nodeval_def ord4_def copy_mech_def
                        rd_host_def rd_stud_def cnt4_def)
  qed
  show "\<exists>a b. swap4 rd_host {N0, N1} a b \<noteq> swap4 rd_stud {N0, N1} a b"
    by (rule exI[of _ False], rule exI[of _ True])
       (simp add: eval_def run_env_def step_def swap_ov_def nodeval_def ord4_def copy_mech_def
                  rd_host_def rd_stud_def cnt4_def)
qed

subsection \<open>P2: valid clamp sets are not unique on a redundant host\<close>

text \<open>Reuses the two-duplicate model of @{text Node_Mask_Clamp}: both nodes copy the input and the
output is true if either is true. A clamp set is inert when ablating it to False leaves the output
unchanged on every input.\<close>

definition inert_dup :: "bool set \<Rightarrow> bool" where
  "inert_dup C \<longleftrightarrow> (\<forall>x. dup_eval x (ablate C) = dup_eval x (\<lambda>_. None))"

lemma bool_both_in:
  assumes "False \<in> C" and "True \<in> C"
  shows "C = {False, True}"
proof (rule set_eqI)
  fix x show "x \<in> C \<longleftrightarrow> x \<in> {False, True}" by (cases x) (simp_all add: assms)
qed

theorem valid_masks_not_unique:
  shows "inert_dup {False}" and "inert_dup {True}" and "\<not> inert_dup {False, True}"
    and "\<forall>C. {False} \<subset> C \<longrightarrow> \<not> inert_dup C" and "\<forall>C. {True} \<subset> C \<longrightarrow> \<not> inert_dup C"
    and "{False} \<noteq> {True}"
proof -
  show "inert_dup {False}" unfolding inert_dup_def by (rule single_inert_joint_not(1))
  show "inert_dup {True}" unfolding inert_dup_def by (rule single_inert_joint_not(2))
  show "\<not> inert_dup {False, True}" unfolding inert_dup_def by (rule single_inert_joint_not(3))
  show "\<forall>C. {False} \<subset> C \<longrightarrow> \<not> inert_dup C"
  proof (intro allI impI)
    fix C :: "bool set" assume pc: "{False} \<subset> C"
    from psubset_imp_ex_mem[OF pc] obtain b where bd: "b \<in> C - {False}" by (rule exE)
    have b1: "b \<in> C" by (rule DiffD1[OF bd])
    have bT: "b = True" using bd by (cases b) simp_all
    have fT: "False \<in> C" by (rule subsetD[OF psubset_imp_subset[OF pc]]) simp
    have tT: "True \<in> C" using b1 bT by simp
    from bool_both_in[OF fT tT] show "\<not> inert_dup C"
      using single_inert_joint_not(3) unfolding inert_dup_def by simp
  qed
  show "\<forall>C. {True} \<subset> C \<longrightarrow> \<not> inert_dup C"
  proof (intro allI impI)
    fix C :: "bool set" assume pc: "{True} \<subset> C"
    from psubset_imp_ex_mem[OF pc] obtain b where bd: "b \<in> C - {True}" by (rule exE)
    have b1: "b \<in> C" by (rule DiffD1[OF bd])
    have bF: "b = False" using bd by (cases b) simp_all
    have tT: "True \<in> C" by (rule subsetD[OF psubset_imp_subset[OF pc]]) simp
    have fT: "False \<in> C" using b1 bF by simp
    from bool_both_in[OF fT tT] show "\<not> inert_dup C"
      using single_inert_joint_not(3) unfolding inert_dup_def by simp
  qed
  show "{False} \<noteq> {True}" by simp
qed

corollary single_screen_mask_not_inert:
  shows "{n. inert_dup {n}} = {False, True}" and "\<not> inert_dup {n. inert_dup {n}}"
proof -
  show "{n. inert_dup {n}} = {False, True}"
    using valid_masks_not_unique(1,2) by auto
  then show "\<not> inert_dup {n. inert_dup {n}}" using valid_masks_not_unique(3) by simp
qed

subsection \<open>P3: on the redundant host, clamping any node breaks swap equivalence\<close>

abbreviation dup_swap :: "bool set \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> (bool \<Rightarrow> bool option) \<Rightarrow> bool" where
  "dup_swap S a b ov \<equiv> eval dup_mech [False, True] dup_readout False a (swap_ov dup_mech [False, True] False S b ov)"

theorem clamp_breaks_swap_equivalence:
  assumes plain: "\<forall>x. dup_eval x (clamp_ov C \<mu> (\<lambda>_. None)) = dup_eval x (\<lambda>_. None)"
      and swaps: "\<forall>n. n \<notin> C \<longrightarrow> (\<forall>a b. dup_swap {n} a b (clamp_ov C \<mu> (\<lambda>_. None)) = dup_swap {n} a b (\<lambda>_. None))"
  shows "C = {}"
proof (rule ccontr)
  assume ne: "C \<noteq> {}"
  have p0: "dup_eval False (clamp_ov C \<mu> (\<lambda>_. None)) = dup_eval False (\<lambda>_. None)" using plain by blast
  have p1: "dup_eval True (clamp_ov C \<mu> (\<lambda>_. None)) = dup_eval True (\<lambda>_. None)" using plain by blast
  have sF: "False \<notin> C \<Longrightarrow> dup_swap {False} True False (clamp_ov C \<mu> (\<lambda>_. None)) = dup_swap {False} True False (\<lambda>_. None)"
    using swaps by blast
  have sT: "True \<notin> C \<Longrightarrow> dup_swap {True} True False (clamp_ov C \<mu> (\<lambda>_. None)) = dup_swap {True} True False (\<lambda>_. None)"
    using swaps by blast
  from ne obtain x where xC: "x \<in> C" by blast
  then have "False \<in> C \<or> True \<in> C" by (cases x) simp_all
  then show False
    using p0 p1 sF sT
    by (cases "False \<in> C"; cases "True \<in> C"; cases "\<mu> False"; cases "\<mu> True")
       (simp_all add: eval_def run_env_def step_def swap_ov_def nodeval_def clamp_ov_def dup_mech_def dup_readout_def)
qed

end
