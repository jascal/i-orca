theory Separation
  imports Complex_Main
begin

text \<open>Sources j contribute c j v to outcome v\<in>V; set S DECIDES t when t is the
  strict argmax of the S-sum over the finite outcome set V.\<close>

definition decides :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> bool" where
  "decides c S V t \<longleftrightarrow> (\<forall>v\<in>V. v \<noteq> t \<longrightarrow> (\<Sum>j\<in>S. c j v) < (\<Sum>j\<in>S. c j t))"

definition mu0 :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> bool" where
  "mu0 c S V t \<longleftrightarrow> (\<forall>j\<in>S. \<not> decides c {j} V t)"

definition has_suff_sub :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> bool" where
  "has_suff_sub c S V t \<longleftrightarrow> (\<exists>P. P \<noteq> {} \<and> P \<subset> S \<and> decides c P V t)"

definition irreducible :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> bool" where
  "irreducible c S V t \<longleftrightarrow> decides c S V t \<and> \<not> has_suff_sub c S V t"

text \<open>--- 2-source witness: an irreducible composed token (restated Theorem 3 exists). ---\<close>

definition c2 :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "c2 j v = (if j = 1 then (if v = 0 then 2 else if v = 1 then 3 else 0)
             else (if v = 0 then 2 else if v = 1 then 0 else 3))"

lemma pair_is_mu0: "mu0 c2 {1,2} {0,1,2} 0"
  by (simp add: mu0_def decides_def c2_def)

lemma irreducible_pair: "irreducible c2 {1,2} {0,1,2} 0"
proof -
  have dec: "decides c2 {1,2} {0,1,2} 0" by (simp add: decides_def c2_def)
  have nsub: "\<not> has_suff_sub c2 {1,2} {0,1,2} 0"
    unfolding has_suff_sub_def
  proof (rule notI, elim exE conjE)
    fix P assume P: "P \<noteq> {}" "P \<subset> {1,2::nat}" "decides c2 P {0,1,2} 0"
    have fin: "finite P" using P(2) by (meson finite.intros finite_subset psubset_imp_subset)
    have "card P < card {1,2::nat}" using psubset_card_mono[OF _ P(2)] by simp
    moreover have "1 \<le> card P" using P(1) fin by (simp add: Suc_leI card_gt_0_iff)
    ultimately have "card P = 1" by simp
    then obtain j where "P = {j}" by (meson card_1_singletonE)
    hence "P = {1} \<or> P = {2}" using P(2) by auto
    thus False using P(3) by (auto simp: decides_def c2_def)
  qed
  show ?thesis using dec nsub by (simp add: irreducible_def)
qed

text \<open>--- The gap: mu0 (no singleton) does NOT imply irreducible; {1,2} already suffices. ---\<close>

definition c3 :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "c3 j v = (if j = 1 then (if v = 0 then 2 else if v = 1 then 3 else 0)
             else if j = 2 then (if v = 0 then 2 else if v = 1 then 0 else 3)
             else (if v = 0 then 0 else 1/2))"

lemma mu0_not_irreducible:
  "mu0 c3 {1,2,3} {0,1,2} 0 \<and> decides c3 {1,2,3} {0,1,2} 0 \<and> has_suff_sub c3 {1,2,3} {0,1,2} 0"
proof (intro conjI)
  show "mu0 c3 {1,2,3} {0,1,2} 0" by (simp add: mu0_def decides_def c3_def)
  show "decides c3 {1,2,3} {0,1,2} 0" by (simp add: decides_def c3_def)
  show "has_suff_sub c3 {1,2,3} {0,1,2} 0"
    unfolding has_suff_sub_def by (rule exI[of _ "{1,2}"]) (auto simp: decides_def c3_def)
qed

text \<open>--- n = 3 irreducible: EVERY source necessary (ties to Section 4.4 fragility).
  Source j defends threat outcome j (weight 8); only the full triple clears all
  three threats on outcome 0 (3+3+3 = 9 > 8).\<close>

definition c3irr :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "c3irr j v = (if v = 0 then 3 else if v = j then 8 else 0)"

lemma triple_mu0: "mu0 c3irr {1,2,3} {0,1,2,3} 0"
  by (simp add: mu0_def decides_def c3irr_def)

lemma triple_decides: "decides c3irr {1,2,3} {0,1,2,3} 0"
  by (simp add: decides_def c3irr_def)

lemma triple_irreducible: "irreducible c3irr {1,2,3} {0,1,2,3} 0"
proof -
  have no_sub: "\<And>P. P \<noteq> {} \<Longrightarrow> P \<subset> {1,2,3::nat} \<Longrightarrow> \<not> decides c3irr P {0,1,2,3} 0"
  proof -
    fix P :: "nat set" assume Pne: "P \<noteq> {}" and Psub: "P \<subset> {1,2,3}"
    from Pne obtain j where jP: "j \<in> P" by auto
    have jin: "j \<in> {1,2,3}" using jP Psub by auto
    have jV: "j \<in> {0,1,2,3}" using jin by auto
    have jne0: "j \<noteq> 0" using jin by auto
    have finP: "finite P" using Psub by (meson finite.intros finite_subset psubset_imp_subset)
    have "card P < card {1,2,3::nat}" using psubset_card_mono[OF _ Psub] by simp
    hence card_le: "card P \<le> 2" by simp
    have cjj: "c3irr j j = 8" using jne0 by (simp add: c3irr_def)
    have "c3irr j j \<le> (\<Sum>i\<in>P. c3irr i j)"
      by (rule member_le_sum[OF jP _ finP]) (auto simp: c3irr_def)
    hence sumj: "(\<Sum>i\<in>P. c3irr i j) \<ge> 8" using cjj by simp
    have "(\<Sum>i\<in>P. c3irr i 0) = real (card P) * 3" by (simp add: c3irr_def)
    hence sum0: "(\<Sum>i\<in>P. c3irr i 0) \<le> 6" using card_le by simp
    show "\<not> decides c3irr P {0,1,2,3} 0"
    proof (unfold decides_def, rule notI)
      assume "\<forall>v\<in>{0,1,2,3}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>P. c3irr i v) < (\<Sum>i\<in>P. c3irr i 0)"
      hence "(\<Sum>i\<in>P. c3irr i j) < (\<Sum>i\<in>P. c3irr i 0)" using jV jne0 by blast
      thus False using sumj sum0 by simp
    qed
  qed
  have nsub: "\<not> has_suff_sub c3irr {1,2,3} {0,1,2,3} 0"
    unfolding has_suff_sub_def using no_sub by blast
  show ?thesis using triple_decides nsub by (simp add: irreducible_def)
qed

end
