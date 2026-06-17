(*
  Unbiased.thy -- the distortion-free property of Aaronson's watermark.

  The headline guarantee: the watermark does NOT change the model's output
  distribution. Marginally (over the secret key) token k is emitted with probability
  exactly p k, so watermarked text is statistically indistinguishable in quality from
  ordinary sampling.

  The computation. Condition on the chosen token k's own PRF value r k = u. Token k
  wins iff every other token i loses, gscore (r i)(p i) < gscore (r k)(p k); by the
  pushforward CDF (GumbelSelect.gscore_le_iff) each other token loses with
  probability u powr (p i / p k), independently. Their product is

        cwin p k S u  =  PROD i in S-{k}. u powr (p i / p k)
                      =  u powr ((1 - p k) / p k)          (cwin_collapse)

  using SUM i in S-{k}. p i = 1 - p k. Marginalising over u ~ U(0,1) (density 1):

        P[k wins]  =  INT_0^1 u powr ((1 - p k)/(p k)) du  =  p k    (win_prob_integral)

  the value of the elementary integral INT_0^1 u powr c du = 1/(c+1) at c = (1-pk)/pk.

  Honest scope. cwin_collapse and win_prob_integral are the exact algebraic and
  analytic steps of the distortion-free proof. The per-coordinate CDF u powr (p i/p k)
  and the product-over-others encode independence of the PRF coordinates; assembling
  them into a single statement over the full product probability space (a Fubini
  argument in HOL-Probability) is the stated lift, not done here -- in the same spirit
  as the diagonal/eigenbasis witnesses in the provenance corpus. cwin_pos records that
  the sampler keeps FULL SUPPORT: no positive-probability token is ever excluded.
*)

theory Unbiased
  imports GumbelSelect
begin

text \<open>The elementary integral at the heart of the unbiasedness computation:
  \<open>integral {0..1} (\<lambda>x. x powr c) = 1/(c+1)\<close> for \<open>c \<ge> 0\<close> (the exponent stays
  non-negative throughout, so no improper integral arises).\<close>

lemma key_integral:
  fixes c :: real
  assumes "0 \<le> c"
  shows "((\<lambda>x. x powr c) has_integral (1/(c+1))) {0..1}"
proof -
  have "c > -1" using assms by simp
  hence "((\<lambda>x. x powr c) has_integral (1 powr (c+1) / (c+1))) {0..1}"
    using has_integral_powr_from_0[of c 1] by simp
  thus ?thesis by simp
qed

text \<open>A product of equal bases collapses to a single power of the summed exponents --
  the algebra of independent uniform CDFs combining into one.\<close>

lemma powr_prod_collapse:
  fixes u :: real and f :: "token \<Rightarrow> real" and S :: "token set"
  assumes "0 < u" "finite S"
  shows "(\<Prod>i\<in>S. u powr (f i)) = u powr (\<Sum>i\<in>S. f i)"
proof -
  have "u \<noteq> 0" using assms(1) by simp
  thus ?thesis using assms(2) by (simp add: powr_sum)
qed

text \<open>The conditional win probability given the winner's own PRF value @{term u}: the
  product over the OTHER tokens of their (independent) lose-probabilities.\<close>

definition cwin :: "(token \<Rightarrow> real) \<Rightarrow> token \<Rightarrow> token set \<Rightarrow> real \<Rightarrow> real" where
  "cwin p k S u = (\<Prod>i\<in>S - {k}. u powr (p i / p k))"

text \<open>The collapse: the conditional win probability is a single power of @{term u}
  with exponent @{term "(1 - p k)/(p k)"}, because the other tokens carry total mass
  @{term "1 - p k"}.\<close>

lemma cwin_collapse:
  fixes u :: real
  assumes "0 < u" "finite S" "k \<in> S" "(\<Sum>i\<in>S. p i) = 1" "0 < p k"
  shows "cwin p k S u = u powr ((1 - p k) / p k)"
proof -
  have fin: "finite (S - {k})" using assms(2) by simp
  have "cwin p k S u = u powr (\<Sum>i\<in>S - {k}. p i / p k)"
    unfolding cwin_def using assms(1) fin by (rule powr_prod_collapse)
  also have "(\<Sum>i\<in>S - {k}. p i / p k) = (\<Sum>i\<in>S - {k}. p i) / p k"
    by (simp add: sum_divide_distrib)
  also have "(\<Sum>i\<in>S - {k}. p i) = (\<Sum>i\<in>S. p i) - p k"
    using assms(2,3) by (simp add: sum_diff1)
  also have "(\<Sum>i\<in>S. p i) - p k = 1 - p k" using assms(4) by simp
  finally show ?thesis by simp
qed

text \<open>Distortion-free sampling. Marginalising the collapsed conditional probability
  over the winner's own uniform value gives selection probability exactly @{term p}.\<close>

lemma win_prob_integral:
  fixes p :: real
  assumes "0 < p" "p \<le> 1"
  shows "((\<lambda>u. u powr ((1 - p) / p)) has_integral p) {0..1}"
proof -
  have c0: "0 \<le> (1 - p)/p" using assms by simp
  have "(1 - p)/p + 1 = 1/p" using assms(1) by (simp add: field_simps)
  hence "1/((1 - p)/p + 1) = p" using assms(1) by simp
  thus ?thesis using key_integral[OF c0] by simp
qed

text \<open>Full support preserved: every token retains strictly positive selection
  probability on the interior, so the watermark never zeroes a feasible token.\<close>

lemma cwin_pos:
  fixes u :: real
  assumes "0 < u" "finite S"
  shows "0 < cwin p k S u"
proof -
  have "u \<noteq> 0" using assms(1) by simp
  thus ?thesis unfolding cwin_def by (intro prod_pos) simp
qed

end
