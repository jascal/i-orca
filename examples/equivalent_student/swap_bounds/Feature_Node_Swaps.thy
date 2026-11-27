theory Feature_Node_Swaps
  imports Complex_Main
begin

section \<open>Feature swaps versus node swaps\<close>

subsection \<open>F1: a site output as feature contributions plus a remainder\<close>

text \<open>A site's output is the sum of feature j's code c j times its decoder direction d j, plus a
remainder r (what the dictionary does not reconstruct). Swapping the features in S takes their codes
from input B and keeps the rest from input A.\<close>

definition out :: "'j set \<Rightarrow> ('j \<Rightarrow> 'v::real_vector) \<Rightarrow> ('j \<Rightarrow> real) \<Rightarrow> 'v \<Rightarrow> 'v" where
  "out J d c r = (\<Sum>j\<in>J. c j *\<^sub>R d j) + r"

definition fswap :: "'j set \<Rightarrow> ('j \<Rightarrow> real) \<Rightarrow> ('j \<Rightarrow> real) \<Rightarrow> 'j \<Rightarrow> real" where
  "fswap S cA cB j = (if j \<in> S then cB j else cA j)"

theorem all_features_and_remainder_is_node_swap:
  "out J d (fswap J cA cB) rB = out J d cB rB"
  unfolding out_def fswap_def by (simp cong: sum.cong)

theorem feature_swap_effect:
  assumes "finite J" and "S \<subseteq> J"
  shows "out J d (fswap S cA cB) rA = out J d cA rA + (\<Sum>j\<in>S. (cB j - cA j) *\<^sub>R d j)"
proof -
  have "\<And>j. fswap S cA cB j *\<^sub>R d j = cA j *\<^sub>R d j + (if j \<in> S then (cB j - cA j) *\<^sub>R d j else 0)"
    by (simp add: fswap_def scaleR_diff_left)
  then have "(\<Sum>j\<in>J. fswap S cA cB j *\<^sub>R d j)
            = (\<Sum>j\<in>J. cA j *\<^sub>R d j) + (\<Sum>j\<in>J. if j \<in> S then (cB j - cA j) *\<^sub>R d j else 0)"
    by (simp add: sum.distrib)
  also have "(\<Sum>j\<in>J. if j \<in> S then (cB j - cA j) *\<^sub>R d j else 0) = (\<Sum>j\<in>S. (cB j - cA j) *\<^sub>R d j)"
    using assms by (simp add: sum.If_cases Int_absorb1)
  finally show ?thesis by (simp add: out_def algebra_simps)
qed

text \<open>At the site output, swap effects add (the site is linear in the codes); any failure of single
swaps to predict joint swaps comes from the nonlinear computation downstream (F2).\<close>

corollary feature_effects_add:
  assumes "finite J" "S \<subseteq> J" "T \<subseteq> J" "S \<inter> T = {}"
  shows "out J d (fswap (S \<union> T) cA cB) rA - out J d cA rA
       = (out J d (fswap S cA cB) rA - out J d cA rA) + (out J d (fswap T cA cB) rA - out J d cA rA)"
proof -
  have "finite S" using assms(1,2) rev_finite_subset by blast
  have "finite T" using assms(1,3) rev_finite_subset by blast
  then show ?thesis using assms \<open>finite S\<close> by (simp add: feature_swap_effect sum.union_disjoint)
qed

subsection \<open>F2: matching every swap of at most m units does not imply matching m + 1\<close>

text \<open>n = 2m + 2 units each copy one boolean input. Swapping the set S takes the units in S from
input b and the others from input a. The host outputs true when at least m + 1 units are true, the
student when at least m + 2 are. Generalises P1 (m = 1) in Swap_Probe_Identifiability.\<close>

definition cnt :: "nat \<Rightarrow> nat set \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat" where
  "cnt n S a b = card {i. i < n \<and> (if i \<in> S then b else a)}"

lemma cnt_cases:
  assumes "S \<subseteq> {..<n}"
  shows "cnt n S a b = (if a then (if b then n else n - card S) else (if b then card S else 0))"
proof -
  have fS: "finite S" using assms finite_subset by blast
  consider "a" "b" | "a" "\<not> b" | "\<not> a" "b" | "\<not> a" "\<not> b" by blast
  then show ?thesis
  proof cases
    case 1 then show ?thesis by (simp add: cnt_def)
  next
    case 2
    then have "{i. i < n \<and> (if i \<in> S then b else a)} = {..<n} - S" by auto
    then have "cnt n S a b = card ({..<n} - S)" by (simp add: cnt_def)
    also have "\<dots> = n - card S" using assms fS by (simp add: card_Diff_subset)
    finally show ?thesis using 2 by simp
  next
    case 3
    then have "{i. i < n \<and> (if i \<in> S then b else a)} = S" using assms by auto
    then have "cnt n S a b = card S" by (simp add: cnt_def)
    then show ?thesis using 3 by simp
  next
    case 4 then show ?thesis by (simp add: cnt_def)
  qed
qed

definition hostT :: "nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "hostT m n S a b = (m + 1 \<le> cnt n S a b)"
definition studT :: "nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "studT m n S a b = (m + 2 \<le> cnt n S a b)"

theorem small_swaps_match:
  assumes "S \<subseteq> {..<2 * m + 2}" and "card S \<le> m"
  shows "hostT m (2 * m + 2) S a b = studT m (2 * m + 2) S a b"
  using assms by (auto simp: hostT_def studT_def cnt_cases)

theorem next_size_differs:
  "\<exists>S. S \<subseteq> {..<2 * m + 2} \<and> card S = m + 1 \<and>
       hostT m (2 * m + 2) S False True \<noteq> studT m (2 * m + 2) S False True"
proof (intro exI conjI)
  show "{..<m + 1} \<subseteq> {..<2 * m + 2}" by auto
  show "card {..<m + 1} = m + 1" by simp
  have "cnt (2 * m + 2) {..<m + 1} False True = m + 1" by (subst cnt_cases) auto
  then show "hostT m (2 * m + 2) {..<m + 1} False True \<noteq> studT m (2 * m + 2) {..<m + 1} False True"
    by (simp add: hostT_def studT_def)
qed

end
