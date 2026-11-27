theory Sparse_TopK
  imports Complex_Main
begin

section \<open>A sparse code keeps at most k latents\<close>

text \<open>Given pre-activations z and a chosen index set S, the code keeps z on S and is zero elsewhere.
@{text is_topk} says S has at most k elements and every kept entry is at least as large as every
dropped one.\<close>

definition keep_code :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)" where
  "keep_code S z i = (if i \<in> S then z i else 0)"

definition is_topk :: "nat \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_topk k z S \<longleftrightarrow> finite S \<and> card S \<le> k \<and> (\<forall>i\<in>S. \<forall>j. j \<notin> S \<longrightarrow> z j \<le> z i)"

lemma support_keep_code: "{i. keep_code S z i \<noteq> 0} \<subseteq> S"
  unfolding keep_code_def by auto

theorem topk_code_sparse:
  assumes "is_topk k z S"
  shows "finite {i. keep_code S z i \<noteq> 0}" and "card {i. keep_code S z i \<noteq> 0} \<le> k"
proof -
  from assms have fin: "finite S" and card: "card S \<le> k" unfolding is_topk_def by auto
  show "finite {i. keep_code S z i \<noteq> 0}" by (rule finite_subset[OF support_keep_code fin])
  show "card {i. keep_code S z i \<noteq> 0} \<le> k"
    by (rule le_trans[OF card_mono[OF fin support_keep_code] card])
qed

end
