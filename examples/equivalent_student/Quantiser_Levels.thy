theory Quantiser_Levels
  imports Complex_Main
begin

section \<open>Level assignment and the finite-level quantiser\<close>

text \<open>A latent's value is mapped to one of finitely many levels by comparing it with a list of
thresholds. The level of a value is the number of thresholds strictly below it, which mirrors
counting how many thresholds the value exceeds.\<close>

definition level :: "real list \<Rightarrow> real \<Rightarrow> nat" where
  "level th c = length (filter (\<lambda>t. t < c) th)"

lemma length_filter_mono_pred:
  assumes "\<And>t. P t \<Longrightarrow> Q t"
  shows "length (filter P xs) \<le> length (filter Q xs)"
  using assms by (induct xs) auto

lemma length_filter_strict_mono_pred:
  assumes imp: "\<And>t. P t \<Longrightarrow> Q t" and mem: "x \<in> set xs" and np: "\<not> P x" and q: "Q x"
  shows "length (filter P xs) < length (filter Q xs)"
  using mem
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "x = y")
    case True
    have "length (filter P ys) \<le> length (filter Q ys)"
      by (rule length_filter_mono_pred[OF imp])
    with True np q show ?thesis by simp
  next
    case False
    with Cons.prems have "x \<in> set ys" by simp
    then have ih: "length (filter P ys) < length (filter Q ys)" by (rule Cons.hyps)
    show ?thesis using ih imp by (cases "P y") auto
  qed
qed

lemma level_le_length: "level th c \<le> length th"
  unfolding level_def by (rule length_filter_le)

lemma level_mono:
  assumes "c \<le> c'"
  shows "level th c \<le> level th c'"
  unfolding level_def using assms by (intro length_filter_mono_pred) auto

subsection \<open>Quantiser with finitely many output values\<close>

definition quant :: "real list \<Rightarrow> real list \<Rightarrow> real \<Rightarrow> real" where
  "quant vb th c = vb ! level th c"

theorem quant_in_values:
  assumes "length vb = Suc (length th)"
  shows "quant vb th c \<in> set vb"
proof -
  have "level th c < length vb" using assms level_le_length[of th c] by simp
  then show ?thesis unfolding quant_def by (rule nth_mem)
qed

subsection \<open>Robustness: a code far from every threshold keeps its level\<close>

theorem level_stable:
  assumes far: "\<And>t. t \<in> set th \<Longrightarrow> \<delta> \<le> \<bar>c - t\<bar>" and near: "\<bar>c' - c\<bar> < \<delta>"
  shows "level th c' = level th c"
proof -
  have "\<And>t. t \<in> set th \<Longrightarrow> (t < c') = (t < c)"
  proof -
    fix t assume t: "t \<in> set th"
    from far[OF t] near show "(t < c') = (t < c)"
      by (cases "t < c") (auto simp: abs_if split: if_splits)
  qed
  then show ?thesis unfolding level_def
    by (intro arg_cong[where f = length] filter_cong) auto
qed

subsection \<open>The margin penalty\<close>

text \<open>Distance from a value to the nearest threshold, and the hinge penalty used by the margin
term: it is positive exactly when the value lies within @{term "w * sp"} of some threshold.\<close>

definition thr_dist :: "real list \<Rightarrow> real \<Rightarrow> real" where
  "thr_dist th c = Min ((\<lambda>t. \<bar>c - t\<bar>) ` set th)"

lemma thr_dist_ge_iff:
  assumes "th \<noteq> []"
  shows "(\<delta> \<le> thr_dist th c) = (\<forall>t\<in>set th. \<delta> \<le> \<bar>c - t\<bar>)"
  using assms unfolding thr_dist_def by (simp add: Min_ge_iff)

definition margin_pen :: "real \<Rightarrow> real \<Rightarrow> real list \<Rightarrow> real \<Rightarrow> real" where
  "margin_pen w sp th c = max 0 (w - thr_dist th c / sp)"

lemma margin_pen_zero_iff:
  assumes "0 < sp"
  shows "(margin_pen w sp th c = 0) = (w * sp \<le> thr_dist th c)"
proof -
  have "(max 0 (w - thr_dist th c / sp) = 0) = (w - thr_dist th c / sp \<le> 0)"
    by (auto simp: max_def)
  also have "... = (w \<le> thr_dist th c / sp)" by simp
  also have "... = (w * sp \<le> thr_dist th c)" using assms by (simp add: le_divide_eq)
  finally show ?thesis unfolding margin_pen_def .
qed

theorem margin_prevents_level_change:
  assumes th: "th \<noteq> []" and sp: "0 < sp" and zero: "margin_pen w sp th c = 0"
      and small: "\<bar>c' - c\<bar> < w * sp"
  shows "level th c' = level th c"
proof -
  from zero sp have "w * sp \<le> thr_dist th c" by (simp add: margin_pen_zero_iff)
  with th have "\<And>t. t \<in> set th \<Longrightarrow> w * sp \<le> \<bar>c - t\<bar>" by (simp add: thr_dist_ge_iff)
  then show ?thesis using small by (rule level_stable)
qed

subsection \<open>Why the margin cannot be replaced by nothing: a code on a threshold flips at once\<close>

theorem level_jump_at_threshold:
  assumes "t \<in> set th" and "0 < \<epsilon>"
  shows "level th t < level th (t + \<epsilon>)"
  unfolding level_def using assms
  by (intro length_filter_strict_mono_pred[of "\<lambda>u. u < t" "\<lambda>u. u < t + \<epsilon>" t th]) auto

corollary arbitrarily_small_flip:
  assumes "t \<in> set th" and "0 < \<epsilon>"
  shows "\<exists>c'. \<bar>c' - t\<bar> < \<epsilon> \<and> level th c' \<noteq> level th t"
proof -
  have "level th t < level th (t + \<epsilon> / 2)" using assms by (intro level_jump_at_threshold) auto
  moreover have "\<bar>(t + \<epsilon> / 2) - t\<bar> < \<epsilon>" using assms by simp
  ultimately show ?thesis by (metis less_irrefl)
qed

end
