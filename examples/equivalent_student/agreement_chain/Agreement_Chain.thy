theory Agreement_Chain
  imports Complex_Main
begin

section \<open>From the continuous student's top answer to the rounded student's, and to the host's\<close>

text \<open>Logits are functions from classes ('k) to reals. c = continuous student, s = rounded (discrete) student,
h = host, all at one position. is_top f i says i is the unique top answer of f.\<close>

definition is_top :: "('k \<Rightarrow> real) \<Rightarrow> 'k \<Rightarrow> bool" where
  "is_top f i \<longleftrightarrow> (\<forall>l. l \<noteq> i \<longrightarrow> f l < f i)"

lemma top_unique:
  assumes "is_top f i" "is_top f j" shows "i = j"
proof (rule ccontr)
  assume ne: "i \<noteq> j"
  have ne': "j \<noteq> i" using ne by simp
  have "f j < f i" using assms(1)[unfolded is_top_def, rule_format, OF ne'] .
  moreover have "f i < f j" using assms(2)[unfolded is_top_def, rule_format, OF ne] .
  ultimately show False by linarith
qed

text \<open>Rounding moves logit k by delta k = s k - c k. The "spread" bound says no two logits move apart by more than B.
A common shift of all logits (spread 0) can never change a top answer; a sup-norm bound E cannot see that.\<close>

lemma sup_implies_spread:
  fixes c s :: "'k \<Rightarrow> real" and E :: real
  assumes move: "\<And>k. \<bar>s k - c k\<bar> \<le> E"
  shows "(s k - c k) - (s l - c l) \<le> 2 * E"
proof -
  have "s k - c k \<le> E" using abs_le_D1[OF move[of k]] .
  moreover have "- (s l - c l) \<le> E" using abs_le_D2[OF move[of l]] .
  ultimately show ?thesis by linarith
qed

theorem spread_top_kept:
  fixes c s :: "'k \<Rightarrow> real" and m B :: real
  assumes pair: "\<And>k l. (s k - c k) - (s l - c l) \<le> B"
      and margin: "\<And>l. l \<noteq> i \<Longrightarrow> m \<le> c i - c l"
      and small: "B < m"
  shows "is_top s i"
  unfolding is_top_def
proof (intro allI impI)
  fix l assume li: "l \<noteq> i"
  have "(s l - c l) - (s i - c i) \<le> B" using pair[of l i] .
  moreover have "m \<le> c i - c l" using margin[OF li] .
  ultimately show "s l < s i" using small by linarith
qed

text \<open>R1 (swap_bounds, Rounding_Margin) without the Lipschitz layer: a sup-norm movement bound E with 2E < m is a
special case, because the spread is at most 2E.\<close>

corollary sup_top_kept:
  fixes c s :: "'k \<Rightarrow> real" and E m :: real
  assumes move: "\<And>k. \<bar>s k - c k\<bar> \<le> E"
      and margin: "\<And>l. l \<noteq> i \<Longrightarrow> m \<le> c i - c l"
      and small: "2 * E < m"
  shows "is_top s i"
proof -
  have pair: "\<And>k l. (s k - c k) - (s l - c l) \<le> 2 * E"
    using sup_implies_spread[OF move] .
  show ?thesis
    apply (rule spread_top_kept[where B = "2 * E" and m = m])
    apply (rule pair)
    apply (rule margin)
    apply assumption
    apply (rule small)
    done
qed

text \<open>The chain. "link 1" is the premise that the continuous student's top answer is the host's top answer i
(here: i is the host's unique top and the continuous student ranks i first by at least m). It is a fact about
trained weights at one position, not a consequence of anything in this theory.\<close>

theorem rounded_top_is_host_top:
  fixes c s h :: "'k \<Rightarrow> real" and m B :: real
  assumes host: "is_top h i"
      and link1: "\<And>l. l \<noteq> i \<Longrightarrow> m \<le> c i - c l"
      and pair: "\<And>k l. (s k - c k) - (s l - c l) \<le> B"
      and small: "B < m"
      and j: "is_top s j"
  shows "j = i"
proof -
  have "is_top s i"
    apply (rule spread_top_kept[where B = B and m = m])
    apply (rule pair)
    apply (rule link1)
    apply assumption
    apply (rule small)
    done
  then show ?thesis using top_unique[OF j] by simp
qed

text \<open>Counting form. On a finite set of positions, the positions where link 1 and the margin test both hold are all
agreements, so their count is a lower bound on the agreement count. Where the set is the whole input domain and the
tests are decided exactly, this is a proved lower bound; on a sample it is a statement about the sample only.\<close>

theorem certified_count_le_agree:
  fixes X :: "'x set" and link1 small agree :: "'x \<Rightarrow> bool"
  assumes fin: "finite X"
      and chain: "\<And>x. x \<in> X \<Longrightarrow> link1 x \<Longrightarrow> small x \<Longrightarrow> agree x"
  shows "card {x \<in> X. link1 x \<and> small x} \<le> card {x \<in> X. agree x}"
proof (rule card_mono)
  show "finite {x \<in> X. agree x}" by (rule finite_subset[OF _ fin]) auto
  show "{x \<in> X. link1 x \<and> small x} \<subseteq> {x \<in> X. agree x}" by (auto intro: chain)
qed

text \<open>The sup-norm test is not necessary, and the spread test is strictly sharper: a common shift of 5 on both
classes keeps the top (margin 1) with spread 0, while any sup-norm bound must be at least 5, so 2E >= 10 > 1.\<close>

lemma shift_example_top:
  "is_top (\<lambda>b::bool. if b then (6::real) else 5) True"
  unfolding is_top_def by simp

lemma shift_example_spread:
  "((if k then (6::real) else 5) - (if k then 1 else 0)) - ((if l then (6::real) else 5) - (if l then 1 else 0)) \<le> 0"
  by (cases k; cases l; simp)

lemma shift_example_sup_needs_5:
  assumes "\<And>k::bool. \<bar>(if k then (6::real) else 5) - (if k then 1 else 0)\<bar> \<le> E"
  shows "5 \<le> E"
  using abs_le_D1[OF assms[of True]] by simp

end
