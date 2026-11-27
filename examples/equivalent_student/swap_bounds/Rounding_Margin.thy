theory Rounding_Margin
  imports Complex_Main
begin

section \<open>R1: a sufficient condition for rounding to keep the top answer\<close>

text \<open>f maps a code vector (features indexed by 'j) to logits (indexed by 'k). Suppose every logit
moves by at most the weighted sum of the feature changes, with weights K j (a Lipschitz-type bound
for the whole downstream map). If each feature moves by at most w j under rounding and twice the
total weighted movement is below the margin of the top answer i at x, then i is still the strict
top answer at the rounded code y. This is a sufficient condition only; it says nothing about how
many levels are necessary (that is the counting bound Cap1 elsewhere).\<close>

theorem top_preserved_uniform:
  fixes f :: "'x \<Rightarrow> 'k \<Rightarrow> real" and E m :: real
  assumes move: "\<And>k. \<bar>f y k - f x k\<bar> \<le> E"
      and margin: "\<And>l. l \<noteq> i \<Longrightarrow> m \<le> f x i - f x l"
      and small: "2 * E < m" and li: "l \<noteq> i"
  shows "f y l < f y i"
proof -
  have "f x i - E \<le> f y i" using move[of i] by (simp add: abs_diff_le_iff)
  moreover have "f y l \<le> f x l + E" using move[of l] by (simp add: abs_diff_le_iff)
  ultimately show ?thesis using margin[OF li] small by linarith
qed

theorem top_preserved_lipschitz:
  fixes x y :: "'j \<Rightarrow> real" and f :: "('j \<Rightarrow> real) \<Rightarrow> 'k \<Rightarrow> real" and m :: real
  assumes lip: "\<And>k. \<bar>f y k - f x k\<bar> \<le> (\<Sum>j\<in>J. K j * \<bar>y j - x j\<bar>)"
      and K: "\<And>j. 0 \<le> K j" and w: "\<And>j. j \<in> J \<Longrightarrow> \<bar>y j - x j\<bar> \<le> w j"
      and margin: "\<And>l. l \<noteq> i \<Longrightarrow> m \<le> f x i - f x l"
      and small: "2 * (\<Sum>j\<in>J. K j * w j) < m" and li: "l \<noteq> i"
  shows "f y l < f y i"
proof -
  have "(\<Sum>j\<in>J. K j * \<bar>y j - x j\<bar>) \<le> (\<Sum>j\<in>J. K j * w j)"
    using K w by (intro sum_mono mult_left_mono) auto
  then have bnd: "\<And>k. \<bar>f y k - f x k\<bar> \<le> (\<Sum>j\<in>J. K j * w j)" using lip order_trans by blast
  have up: "f x i - (\<Sum>j\<in>J. K j * w j) \<le> f y i" using bnd[of i] by (simp add: abs_diff_le_iff)
  have lo: "f y l \<le> f x l + (\<Sum>j\<in>J. K j * w j)" using bnd[of l] by (simp add: abs_diff_le_iff)
  show ?thesis using up lo margin[OF li] small by linarith
qed

text \<open>The rounding error of one feature is at most the width of its bin, when the stored level value
lies in the same bin as the code (true for a bin mean of in-bin values). The two outer bins are
bounded only by the calibration sample's range, so outside it no width bound holds.\<close>

lemma bin_error:
  fixes lo hi c v :: real
  assumes "lo \<le> c" "c \<le> hi" "lo \<le> v" "v \<le> hi"
  shows "\<bar>v - c\<bar> \<le> hi - lo"
  using assms by (simp add: abs_diff_le_iff)

end
