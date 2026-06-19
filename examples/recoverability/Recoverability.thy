theory Recoverability
  imports Complex_Main
begin

text \<open>A formal model of SAE feature recoverability -- the theory behind
  "compression is variance-greedy, meaning is variance-cheap", validated empirically
  on the econ-sae substrate (econ-sae/docs/regime_label_free_recovery.md).

  Each ground-truth feature, read off a representation along one principal direction,
  has TWO scalar functionals of its mean-shift c and the direction's within-class
  variance s2 (= sigma^2):

  - PRESENCE (can a linear probe / matched filter read it?) is governed by DETECTION
    theory: the Fisher SNR  fisher = c^2 / s2  (signal^2 / within-class noise variance).
  - ALLOCATION (does the unsupervised SAE spend a latent on it?) is governed by
    RATE-DISTORTION theory: the between-class variance fraction
    var_share = p(1-p) c^2 / V  (the reconstruction "cost to ignore" the feature),
    which a reverse-water-filling coder DROPS below a budget-set level.

  The two are linked only through the direction's variance s2 (the `bridge`), so a
  feature can be made arbitrarily detectable (any `fisher`) yet have arbitrarily small
  reconstruction-relevance (`var_share` below any threshold) by placing it in a
  low-variance direction (`present_not_allocated`). Detectability does NOT imply
  recoverability.

  Honest scope: a scalar (single-direction, Gaussian-mode) model -- the clean
  algebraic core of the law, not the full multivariate SAE. It formalises WHY presence
  and allocation decouple; the empirical work shows that they do, on a real substrate.\<close>

section \<open>Detection: presence = Fisher SNR\<close>

definition fisher :: "real \<Rightarrow> real \<Rightarrow> real" where
  "fisher c s2 = c\<^sup>2 / s2"

section \<open>Rate-distortion: allocation = between-class variance, thresholded\<close>

definition var_share :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "var_share c p V = p * (1 - p) * c\<^sup>2 / V"

text \<open>The reverse-water-filling rate of a Gaussian mode of variance lam at water level
  th: zero below the water line, positive above. This is what makes allocation
  variance-greedy.\<close>

definition rd_rate :: "real \<Rightarrow> real \<Rightarrow> real" where
  "rd_rate lam th = (if lam > th then ln (lam / th) / 2 else 0)"

lemma rd_rate_nonneg: "th > 0 \<Longrightarrow> rd_rate lam th \<ge> 0"
  by (auto simp: rd_rate_def)

text \<open>The water-filling drop: a mode is encoded iff its variance clears the water
  level. Allocation thresholds on VARIANCE, nothing else.\<close>

theorem rd_rate_pos_iff:
  assumes "th > 0"
  shows "rd_rate lam th > 0 \<longleftrightarrow> lam > th"
proof
  assume "rd_rate lam th > 0"
  thus "lam > th" by (auto simp: rd_rate_def split: if_splits)
next
  assume gt: "lam > th"
  hence "lam / th > 1" using assms by simp
  hence "ln (lam / th) > 0" by simp
  thus "rd_rate lam th > 0" using gt by (simp add: rd_rate_def)
qed

corollary rd_rate_zero_iff:
  assumes "th > 0"
  shows "rd_rate lam th = 0 \<longleftrightarrow> lam \<le> th"
proof -
  have nn: "rd_rate lam th \<ge> 0" using assms by (rule rd_rate_nonneg)
  have "rd_rate lam th = 0 \<longleftrightarrow> \<not> (rd_rate lam th > 0)" using nn by linarith
  also have "\<dots> \<longleftrightarrow> \<not> (lam > th)" using rd_rate_pos_iff[OF assms] by simp
  also have "\<dots> \<longleftrightarrow> lam \<le> th" by auto
  finally show ?thesis .
qed

section \<open>The bridge and the divergence\<close>

text \<open>The bridge identity: reconstruction-relevance is detectability scaled by the
  direction's own variance. So the two functionals are linked ONLY through s2.\<close>

lemma fisher_var_share_bridge:
  assumes "s2 > 0"
  shows "var_share c p V = fisher c s2 * (p * (1 - p) * s2 / V)"
  using assms by (simp add: var_share_def fisher_def power2_eq_square)

text \<open>THE DIVERGENCE -- "compression is variance-greedy, meaning is variance-cheap".
  For any target detectability F and any reconstruction-relevance threshold th, there
  is a feature that is exactly that detectable yet whose reconstruction-relevance falls
  below th -- present (a probe reads it) but not allocated (the variance-greedy coder
  drops it). Achieved by placing the feature in a low-variance direction.\<close>

theorem present_not_allocated:
  assumes F: "F > 0" and th: "th > 0" and p0: "0 < p" and p1: "p < 1" and V: "V > 0"
  shows "\<exists>c s2. s2 > 0 \<and> c > 0 \<and> fisher c s2 = F \<and> var_share c p V < th"
proof -
  define A where "A = p * (1 - p) * F"
  have A: "A > 0" unfolding A_def using p0 p1 F by simp
  define s2 where "s2 = th * V / (2 * A)"
  define c  where "c = sqrt (F * s2)"
  have s2pos: "s2 > 0" unfolding s2_def using th V A by simp
  have cpos: "c > 0" unfolding c_def using F s2pos by simp
  have csq: "c\<^sup>2 = F * s2" unfolding c_def using F s2pos by simp
  have "fisher c s2 = F" unfolding fisher_def using csq s2pos by simp
  moreover have "var_share c p V = th / 2"
  proof -
    have ne: "A \<noteq> 0" "V \<noteq> 0" using A V by auto
    have "var_share c p V = p * (1 - p) * (F * s2) / V"
      using csq by (simp add: var_share_def)
    also have "\<dots> = A * s2 / V" by (simp add: A_def)
    also have "\<dots> = th / 2" unfolding s2_def using ne by (simp add: field_simps)
    finally show ?thesis .
  qed
  ultimately show ?thesis using s2pos cpos th by force
qed

text \<open>Stated against the rate-distortion coder directly: a feature of ARBITRARY
  detectability F whose between-class variance is below the water level gets ZERO rate
  -- dropped. (Set V = 1 so var_share = between-class variance = the mode the coder
  sees.)\<close>

corollary detectable_yet_dropped:
  assumes "F > 0" and "th > 0" and "0 < p" and "p < 1"
  shows "\<exists>c s2. s2 > 0 \<and> c > 0 \<and> fisher c s2 = F \<and> rd_rate (var_share c p 1) th = 0"
proof -
  from present_not_allocated[OF assms, of 1]
  obtain c s2 where cs: "s2 > 0" "c > 0" "fisher c s2 = F" "var_share c p 1 < th" by auto
  have "rd_rate (var_share c p 1) th = 0"
    using cs(4) rd_rate_zero_iff[OF \<open>th > 0\<close>] by simp
  thus ?thesis using cs by blast
qed

text \<open>And the asymmetry that names the mechanism: allocation depends ONLY on var_share
  (not fisher), presence ONLY on fisher (not var_share) -- so two features with the
  SAME detectability can sit on opposite sides of the water line, ordered entirely by
  their variance. Detectability does not order recoverability.\<close>

theorem same_fisher_opposite_allocation:
  assumes "th > 0" and "0 < p" and "p < 1" and "F > 0"
  shows "\<exists>c1 s21 c2 s22.
           s21 > 0 \<and> s22 > 0 \<and>
           fisher c1 s21 = F \<and> fisher c2 s22 = F \<and>           \<comment> \<open>equally detectable\<close>
           rd_rate (var_share c1 p 1) th = 0 \<and>                \<comment> \<open>one dropped\<close>
           rd_rate (var_share c2 p 1) th > 0"                  \<comment> \<open>one kept\<close>
proof -
  define A where "A = p * (1 - p) * F"
  have A: "A > 0" unfolding A_def using assms by simp
  \<comment> \<open>dropped: var_share = th/2 < th\<close>
  from detectable_yet_dropped[OF assms(4,1,2,3)]
  obtain c1 s21 where d1: "s21 > 0" "fisher c1 s21 = F" "rd_rate (var_share c1 p 1) th = 0"
    by auto
  \<comment> \<open>kept: a high-variance direction so var_share = 2*th > th\<close>
  define s22 where "s22 = 2 * th / A"
  define c2 where "c2 = sqrt (F * s22)"
  have s2: "s22 > 0" unfolding s22_def using assms(1) A by simp
  have csq: "c2\<^sup>2 = F * s22" unfolding c2_def using assms(4) s2 by simp
  have f2: "fisher c2 s22 = F" unfolding fisher_def using csq s2 by simp
  have "var_share c2 p 1 = 2 * th"
  proof -
    have ne: "A \<noteq> 0" using A by simp
    have "var_share c2 p 1 = p * (1 - p) * (F * s22)"
      using csq by (simp add: var_share_def)
    also have "\<dots> = A * s22" by (simp add: A_def)
    also have "\<dots> = 2 * th" unfolding s22_def using ne by (simp add: field_simps)
    finally show ?thesis .
  qed
  hence "rd_rate (var_share c2 p 1) th > 0"
    using rd_rate_pos_iff[OF assms(1)] assms(1) by simp
  thus ?thesis using d1 s2 f2 by blast
qed

end
