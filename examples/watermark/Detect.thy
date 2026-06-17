(*
  Detect.thy -- detectability of Aaronson's watermark.

  The flip side of distortion-freeness: although watermarked text is distributed
  exactly as the model's own samples (Unbiased.thy), a verifier holding the secret
  KEY can detect the watermark. For each emitted token the verifier recomputes the
  token's PRF value r (deterministic given key + context, GumbelSelect.selects_unique)
  and accumulates the score

        wscore r = - ln (1 - r) = ln (1 / (1 - r)).

  Null model (no watermark / wrong key). If the text was produced independently of the
  key, the chosen token's r is a fresh U(0,1) draw. Then wscore r has the EXPONENTIAL(1)
  law: P[wscore r <= t] = 1 - exp(-t) (wscore_cdf). So each token contributes mean 1,
  the sum over T tokens has mean T -- the verifier's calibrated null. (A threshold a
  few standard deviations above T controls the false-positive rate.)

  Signal (watermarked). wscore is increasing in r (wscore_mono), and under the
  watermark the winner's own value r is biased toward 1:

    chosen_r_dominates : the winner's value stochastically dominates uniform
                         (its CDF u powr (1/p) lies BELOW the uniform CDF u);
    dwin_integral_one  : (1/p) * u powr (1/p - 1) is a genuine probability density;
    chosen_r_mean      : its mean is 1/(1+p) >= 1/2, rising to 1 as p -> 0.

  So in high-entropy positions (small p per token) the emitted token's r is pushed
  toward 1, lifting each wscore above its null mean of 1 -- the sum exceeds T and the
  watermark is detected. The detector needs no access to the model's probabilities at
  verification time, only the key.

  Honest scope. wscore_cdf is the exact per-token null law; the elevation of the mean
  under watermarking is quantified by chosen_r_mean (an exact integral). Concentration
  of the T-token sum (the Chernoff / p-value bound that turns mean-separation into a
  detection guarantee) is a probabilistic lift left to HOL-Probability, as flagged in
  PROPOSAL.md.
*)

theory Detect
  imports Unbiased
begin

text \<open>The verifier's per-token score.\<close>

definition wscore :: "real \<Rightarrow> real" where
  "wscore r = - ln (1 - r)"

text \<open>Null calibration: under a uniform r the score is Exponential(1). We prove the
  exact quantile identity, whose uniform measure gives the CDF \<open>1 - exp (- t)\<close>.\<close>

lemma wscore_cdf:
  assumes "0 \<le> t" "r < 1"
  shows "wscore r \<le> t \<longleftrightarrow> r \<le> 1 - exp (- t)"
proof -
  have pos: "0 < 1 - r" using assms(2) by simp
  have "wscore r \<le> t \<longleftrightarrow> - t \<le> ln (1 - r)" unfolding wscore_def by linarith
  also have "\<dots> \<longleftrightarrow> exp (- t) \<le> 1 - r"
  proof -
    have "exp (- t) \<le> 1 - r \<longleftrightarrow> exp (- t) \<le> exp (ln (1 - r))" using pos by (simp add: exp_ln)
    also have "\<dots> \<longleftrightarrow> - t \<le> ln (1 - r)" by (simp add: exp_le_cancel_iff)
    finally show ?thesis by blast
  qed
  also have "\<dots> \<longleftrightarrow> r \<le> 1 - exp (- t)" by linarith
  finally show ?thesis .
qed

text \<open>The score is non-negative on \<open>[0,1)\<close> and strictly increasing in the PRF
  value: a token with a larger r contributes more evidence.\<close>

lemma wscore_nonneg:
  assumes "0 \<le> r" "r < 1"
  shows "0 \<le> wscore r"
  using assms by (simp add: wscore_def)

lemma wscore_mono:
  assumes "0 \<le> r1" "r1 < r2" "r2 < 1"
  shows "wscore r1 < wscore r2"
  using assms by (simp add: wscore_def)

text \<open>Under the watermark the winning token's own PRF value is biased toward 1: its
  CDF @{term "u powr (1/p)"} lies below the uniform CDF @{term u} (stochastic
  dominance), because @{term "1/p \<ge> 1"}.\<close>

lemma chosen_r_dominates:
  fixes u p :: real
  assumes "0 \<le> u" "u \<le> 1" "0 < p" "p \<le> 1"
  shows "u powr (1/p) \<le> u"
proof -
  have invp: "1 \<le> 1/p" using assms(3,4) by (simp add: pos_le_divide_eq)
  have "u powr (1/p) \<le> u powr 1" using invp assms(1,2) by (rule powr_mono')
  thus ?thesis using assms(1) by (simp add: powr_one)
qed

text \<open>The winner's value has, given that token k wins, the density
  @{term "dwin p u = (1/p) * u powr (1/p - 1)"} on @{term "(0,1)"}.\<close>

definition dwin :: "real \<Rightarrow> real \<Rightarrow> real" where
  "dwin p u = (1/p) * u powr (1/p - 1)"

text \<open>@{term dwin} is a genuine probability density: it integrates to 1.\<close>

lemma dwin_integral_one:
  fixes p :: real
  assumes "0 < p" "p \<le> 1"
  shows "((\<lambda>u. dwin p u) has_integral 1) {0..1}"
proof -
  have pnz: "p \<noteq> 0" using assms(1) by simp
  have c0: "0 \<le> 1/p - 1"
  proof -
    have "1/p - 1 = (1 - p)/p" using assms(1) by (simp add: field_simps)
    moreover have "0 \<le> (1 - p)/p" using assms by simp
    ultimately show ?thesis by simp
  qed
  have I: "((\<lambda>u. u powr (1/p - 1)) has_integral (1/((1/p - 1) + 1))) {0..1}"
    using key_integral[OF c0] by simp
  have v: "1/((1/p - 1) + 1) = p" using pnz by (simp add: field_simps)
  have "((\<lambda>u. (1/p) * u powr (1/p - 1)) has_integral ((1/p) * (1/((1/p - 1) + 1)))) {0..1}"
    by (rule has_integral_mult_right[OF I])
  moreover have "(1/p) * (1/((1/p - 1) + 1)) = 1" using pnz v by simp
  ultimately show ?thesis by (simp add: dwin_def)
qed

text \<open>The mean of the winner's value is \<open>1/(1+p)\<close> -- at least \<open>1/2\<close>, and tending
  to 1 as \<open>p \<rightarrow> 0\<close> (high-entropy positions). This positive bias over the null mean
  \<open>1/2\<close> is the detection signal.\<close>

lemma chosen_r_mean:
  fixes p :: real
  assumes "0 < p" "p \<le> 1"
  shows "((\<lambda>u. u * dwin p u) has_integral (1/(1+p))) {0..1}"
proof -
  have pnz: "p \<noteq> 0" using assms(1) by simp
  have p1nz: "1 + p \<noteq> 0" using assms(1) by simp
  have c0: "0 \<le> 1/p" using assms(1) by simp
  have I: "((\<lambda>u. u powr (1/p)) has_integral (1/((1/p) + 1))) {0..1}"
    using key_integral[OF c0] by simp
  have "((\<lambda>u. (1/p) * u powr (1/p)) has_integral ((1/p) * (1/((1/p) + 1)))) {0..1}"
    by (rule has_integral_mult_right[OF I])
  moreover have "(1/p) * (1/((1/p) + 1)) = 1/(1+p)"
    using pnz p1nz by (simp add: field_simps)
  ultimately have J: "((\<lambda>u. (1/p) * u powr (1/p)) has_integral (1/(1+p))) {0..1}" by simp
  have eq: "u * dwin p u = (1/p) * u powr (1/p)" if "u \<in> {0..1}" for u
  proof -
    have nn: "0 \<le> u" using that by simp
    have "u * dwin p u = (1/p) * (u * u powr (1/p - 1))" by (simp add: dwin_def)
    also have "u * u powr (1/p - 1) = u powr (1 + (1/p - 1))" using nn by (rule powr_mult_base)
    also have "(1::real) + (1/p - 1) = 1/p" by simp
    finally show ?thesis by simp
  qed
  have cong: "((\<lambda>u. u * dwin p u) has_integral (1/(1+p))) {0..1}
            = ((\<lambda>u. (1/p) * u powr (1/p)) has_integral (1/(1+p))) {0..1}"
    by (rule has_integral_cong) (rule eq)
  show ?thesis using cong J by simp
qed

end
