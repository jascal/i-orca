theory Characterization
  imports Separation
begin

text \<open>Toward a characterisation of WHICH composed tokens are irreducible
  (decided by the full source set S but by no proper non-empty subset).\<close>

definition all_necessary :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> bool" where
  "all_necessary c S V t \<longleftrightarrow> (\<forall>j\<in>S. \<not> decides c (S - {j}) V t)"

text \<open>The empty coalition never decides (when some competitor exists).\<close>
lemma empty_not_decides:
  assumes "\<exists>v\<in>V. v \<noteq> t" shows "\<not> decides c {} V t"
  using assms by (auto simp: decides_def)

text \<open>--- Reformulation: irreducible \<longleftrightarrow> the full set is the UNIQUE deciding set. ---\<close>
lemma irreducible_iff_unique_decider:
  assumes dS: "decides c S V t" and Vt: "\<exists>v\<in>V. v \<noteq> t"
  shows "irreducible c S V t \<longleftrightarrow> (\<forall>P. P \<subseteq> S \<longrightarrow> decides c P V t \<longrightarrow> P = S)"
proof
  assume irr: "irreducible c S V t"
  show "\<forall>P. P \<subseteq> S \<longrightarrow> decides c P V t \<longrightarrow> P = S"
  proof (intro allI impI)
    fix P assume PS: "P \<subseteq> S" and dP: "decides c P V t"
    show "P = S"
    proof (rule ccontr)
      assume "P \<noteq> S"
      hence pss: "P \<subset> S" using PS by auto
      have "P \<noteq> {}" using dP empty_not_decides[OF Vt] by auto
      hence "has_suff_sub c S V t"
        unfolding has_suff_sub_def using pss dP by (intro exI[of _ P]) simp
      thus False using irr by (simp add: irreducible_def)
    qed
  qed
next
  assume R: "\<forall>P. P \<subseteq> S \<longrightarrow> decides c P V t \<longrightarrow> P = S"
  have "\<not> has_suff_sub c S V t"
  proof (unfold has_suff_sub_def, rule notI, elim exE conjE)
    fix P assume "P \<noteq> {}" "P \<subset> S" "decides c P V t"
    hence "P = S" using R by (auto simp: psubset_imp_subset)
    thus False using \<open>P \<subset> S\<close> by auto
  qed
  thus "irreducible c S V t" by (simp add: irreducible_def dS)
qed

text \<open>--- Two necessary conditions (any S with at least two sources). ---\<close>

lemma necessary_mu0:
  assumes irr: "irreducible c S V t" and card2: "2 \<le> card S"
  shows "mu0 c S V t"
proof (unfold mu0_def, intro ballI notI)
  fix j assume jS: "j \<in> S" and dj: "decides c {j} V t"
  have "card {j} \<noteq> card S" using card2 by simp
  hence "{j} \<noteq> S" by auto
  hence w2: "{j} \<subset> S" using jS by auto
  have "has_suff_sub c S V t"
    unfolding has_suff_sub_def using w2 dj by (intro exI[of _ "{j}"]) simp
  thus False using irr by (simp add: irreducible_def)
qed

lemma necessary_all_sources:
  assumes irr: "irreducible c S V t" and card2: "2 \<le> card S"
  shows "all_necessary c S V t"
proof (unfold all_necessary_def, intro ballI notI)
  fix j assume jS: "j \<in> S" and dj: "decides c (S - {j}) V t"
  have finS: "finite S" using card2 by (cases "finite S") simp_all
  have cardd: "card (S - {j}) = card S - 1" using jS finS by (simp add: card_Diff_subset)
  have "0 < card (S - {j})" using cardd card2 by simp
  hence w1: "S - {j} \<noteq> {}" by (simp add: card_gt_0_iff)
  have w2: "S - {j} \<subset> S" using jS by auto
  have "has_suff_sub c S V t"
    unfolding has_suff_sub_def using w1 w2 dj by (intro exI[of _ "S - {j}"]) simp
  thus False using irr by (simp add: irreducible_def)
qed

text \<open>--- EXACT characterisation at n = 3: the two necessary conditions also suffice. ---\<close>

lemma proper_nonempty_card3:
  assumes card3: "card S = 3" and PS: "P \<subseteq> S" and Pne: "P \<noteq> {}" and PnS: "P \<noteq> S"
  shows "(\<exists>j\<in>S. P = {j}) \<or> (\<exists>j\<in>S. P = S - {j})"
proof -
  have finS: "finite S" using card3 card.infinite by force
  have "card P < 3" using PS PnS card3 finS by (metis psubsetI psubset_card_mono)
  moreover have "1 \<le> card P" using Pne PS finS by (simp add: Suc_leI card_gt_0_iff finite_subset)
  ultimately have "card P = 1 \<or> card P = 2" by auto
  thus ?thesis
  proof
    assume "card P = 1"
    then obtain j where "P = {j}" by (meson card_1_singletonE)
    thus ?thesis using PS by auto
  next
    assume cP: "card P = 2"
    have finP: "finite P" using PS finS finite_subset by auto
    have "card (S - P) = 1" using finP PS cP card3 by (simp add: card_Diff_subset)
    then obtain j where j: "S - P = {j}" by (meson card_1_singletonE)
    have "j \<in> S" using j by blast
    moreover have "P = S - {j}" using PS j by auto
    ultimately show ?thesis by blast
  qed
qed

lemma n3_characterization:
  assumes card3: "card S = 3" and dS: "decides c S V t" and Vt: "\<exists>v\<in>V. v \<noteq> t"
  shows "irreducible c S V t \<longleftrightarrow> (mu0 c S V t \<and> all_necessary c S V t)"
proof
  assume irr: "irreducible c S V t"
  have "2 \<le> card S" using card3 by simp
  thus "mu0 c S V t \<and> all_necessary c S V t"
    using necessary_mu0[OF irr] necessary_all_sources[OF irr] by simp
next
  assume R: "mu0 c S V t \<and> all_necessary c S V t"
  have "\<forall>P. P \<subseteq> S \<longrightarrow> decides c P V t \<longrightarrow> P = S"
  proof (intro allI impI)
    fix P assume PS: "P \<subseteq> S" and dP: "decides c P V t"
    show "P = S"
    proof (rule ccontr)
      assume PnS: "P \<noteq> S"
      have Pne: "P \<noteq> {}" using dP empty_not_decides[OF Vt] by auto
      from proper_nonempty_card3[OF card3 PS Pne PnS]
      show False
      proof
        assume "\<exists>j\<in>S. P = {j}"
        thus False using R dP by (auto simp: mu0_def)
      next
        assume "\<exists>j\<in>S. P = S - {j}"
        thus False using R dP by (auto simp: all_necessary_def)
      qed
    qed
  qed
  thus "irreducible c S V t" using irreducible_iff_unique_decider[OF dS Vt] by simp
qed

text \<open>--- The n = 3 characterisation is SHARP: it fails at n = 4. A 4-source token
  with mu0 (no singleton) AND all_necessary (every triple S-{j} fails) AND decided
  by the full set, yet REDUCIBLE — the proper pair {1,2} already decides it.
  (Margins m_j on two competitors: m1=(2,-1), m2=(-1,2), m3=(-3/2,2), m4=(2,-3/2);
  {1,2} and the full set sum into the positive quadrant, every singleton and every
  triple do not.)\<close>

definition c4 :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "c4 j v = (if v = 0 then 0
             else if j = 1 then (if v = 1 then -2 else 1)
             else if j = 2 then (if v = 1 then 1 else -2)
             else if j = 3 then (if v = 1 then 3/2 else -2)
             else (if v = 1 then -2 else 3/2))"

lemma c4_pair_decides: "decides c4 {1,2} {0,1,2} 0"
  by (simp add: decides_def c4_def)

lemma c4_full_decides: "decides c4 {1,2,3,4} {0,1,2} 0"
  by (simp add: decides_def c4_def)

lemma c4_mu0: "mu0 c4 {1,2,3,4} {0,1,2} 0"
  by (simp add: mu0_def decides_def c4_def)

lemma c4_all_necessary: "all_necessary c4 {1,2,3,4} {0,1,2} 0"
  unfolding all_necessary_def
proof (intro ballI)
  fix j :: nat assume "j \<in> {1,2,3,4}"
  then consider "j = 1" | "j = 2" | "j = 3" | "j = 4" by auto
  then show "\<not> decides c4 ({1,2,3,4} - {j}) {0,1,2} 0"
  proof cases
    case 1 hence "{1,2,3,4} - {j} = {2,3,4}" by auto
    then show ?thesis by (simp add: decides_def c4_def)
  next
    case 2 hence "{1,2,3,4} - {j} = {1,3,4}" by auto
    then show ?thesis by (simp add: decides_def c4_def)
  next
    case 3 hence "{1,2,3,4} - {j} = {1,2,4}" by auto
    then show ?thesis by (simp add: decides_def c4_def)
  next
    case 4 hence "{1,2,3,4} - {j} = {1,2,3}" by auto
    then show ?thesis by (simp add: decides_def c4_def)
  qed
qed

lemma c4_reducible: "\<not> irreducible c4 {1,2,3,4} {0,1,2} 0"
proof -
  have "has_suff_sub c4 {1,2,3,4} {0,1,2} 0"
    unfolding has_suff_sub_def using c4_pair_decides
    by (intro exI[of _ "{1,2::nat}"]) auto
  thus ?thesis by (simp add: irreducible_def)
qed

text \<open>So at n = 4, mu0 + all_necessary + decides(full) does NOT imply irreducible.\<close>
theorem n3_characterization_is_sharp:
  "mu0 c4 {1,2,3,4} {0,1,2} 0 \<and> all_necessary c4 {1,2,3,4} {0,1,2} 0
   \<and> decides c4 {1,2,3,4} {0,1,2} 0 \<and> \<not> irreducible c4 {1,2,3,4} {0,1,2} 0"
  using c4_mu0 c4_all_necessary c4_full_decides c4_reducible by blast

end
