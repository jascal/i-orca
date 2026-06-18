(*
  DistortionRate.thy -- TurboQuant's distortion-rate bounds and near-optimality.

  TurboQuant (Zandieh, Daliri, Hadian & Mirrokni, "TurboQuant: Online Vector Quantization
  with Near-optimal Distortion Rate", Google / NYU, arXiv:2504.19874, 2025) is a vector
  quantizer that, for any worst-case unit vector x and bit-width b, achieves:

    Theorem 1 (MSE):        D_mse  <=  (sqrt 3 * pi / 2) * (1/4^b)
    Theorem 2 (inner-prod): D_prod <=  (sqrt 3 * pi^2 * ||y||^2 / d) * (1/4^b)

  while Theorem 3 (the information-theoretic lower bound, via Shannon + Yao's minimax)
  shows that ANY b-bit randomized quantizer is forced to suffer

    D_mse  >=  1/4^b           D_prod >=  (||y||^2 / d) * (1/4^b).

  We model these four bounds as functions and kernel-check the QUANTITATIVE STRUCTURE the
  paper highlights -- this is honest about scope: the achievability of the upper bounds
  (random rotation -> Beta coordinates -> Lloyd-Max scalar quantizers) and the lower bound
  itself are the meta inputs; what is proved here is the rate arithmetic that those bounds
  imply. The headline facts:

    near-optimality : upper/lower is the CONSTANT sqrt3*pi/2 (MSE) resp. sqrt3*pi^2 (prod),
                      independent of bit-width, dimension, and ||y|| -- the 4^b/d/||y||^2
                      all cancel (mse_ratio_const, prod_ratio_const);
    the constant    : sqrt3*pi/2 is between 2.7 and 2.73 (mse_const_approx);
    geometric rate  : each extra bit quarters the distortion bound (mse_decay, prod_decay);
    consistency     : the achievable upper bound sits above the lower bound (mse_achievable);
    high-d benefit  : the inner-product bound shrinks as the dimension grows (prod_dim_decay).
*)

theory DistortionRate
  imports "HOL-Analysis.Complex_Transcendental"
    \<comment> \<open>imported only for pi_approx (the rational bounds on pi used in
        mse_const_approx); the rest is Complex_Main. sqrt 3 bounds come from NthRoot.\<close>
begin

definition mse_ub :: "nat \<Rightarrow> real" where "mse_ub b = (sqrt 3 * pi / 2) / 4 ^ b"
definition mse_lb :: "nat \<Rightarrow> real" where "mse_lb b = 1 / 4 ^ b"
definition prod_ub :: "nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "prod_ub d ny b = (sqrt 3 * pi\<^sup>2 * ny / real d) / 4 ^ b"
definition prod_lb :: "nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "prod_lb d ny b = (ny / real d) / 4 ^ b"

text \<open>Near-optimality (MSE): the upper bound (paper Thm 1) is a fixed constant multiple of
  the lower bound (paper Thm 3), the same multiple for every bit-width -- the 4^b cancels.\<close>

theorem mse_ratio_const: "mse_ub b = (sqrt 3 * pi / 2) * mse_lb b"
  by (simp add: mse_ub_def mse_lb_def)

theorem mse_ratio_eq: "mse_ub b / mse_lb b = sqrt 3 * pi / 2"
  by (simp add: mse_ub_def mse_lb_def)

text \<open>Near-optimality (inner product, paper Thm 2 vs Thm 3): the ratio is the constant
  sqrt3*pi^2, the same for every dimension d, norm ||y||^2, and bit-width b.\<close>

theorem prod_ratio_const: "prod_ub d ny b = (sqrt 3 * pi\<^sup>2) * prod_lb d ny b"
  by (simp add: prod_ub_def prod_lb_def)

text \<open>Geometric rate (the 1/4^b factor of paper Thm 1 / Thm 2): each extra bit quarters
  the distortion bound.\<close>

theorem mse_decay: "mse_ub (Suc b) = mse_ub b / 4"
  by (simp add: mse_ub_def)

theorem prod_decay: "prod_ub d ny (Suc b) = prod_ub d ny b / 4"
  by (simp add: prod_ub_def)

text \<open>The near-optimality constant sqrt3*pi/2 (paper Thm 1 upper bound over Thm 3 lower
  bound) is approximately 2.7.\<close>

lemma sqrt3_bounds: "1.7320 < sqrt 3 \<and> sqrt 3 < 1.7321"
proof
  show "1.7320 < sqrt 3" by (rule real_less_rsqrt) (simp add: power2_eq_square)
next
  have "sqrt 3 < sqrt (1.7321\<^sup>2)" by (rule real_sqrt_less_mono) (simp add: power2_eq_square)
  also have "\<dots> = 1.7321" by simp
  finally show "sqrt 3 < 1.7321" .
qed

theorem mse_const_approx: "2.7 < sqrt 3 * pi / 2 \<and> sqrt 3 * pi / 2 < 2.73"
proof
  have s: "1.7320 < sqrt 3" using sqrt3_bounds by auto
  have p: "3.141592653588 \<le> pi" using pi_approx by auto
  have "(2.7::real) < 1.7320 * 3.141592653588 / 2" by simp
  also have "\<dots> \<le> sqrt 3 * pi / 2" using s p by (intro divide_right_mono mult_mono) auto
  finally show "2.7 < sqrt 3 * pi / 2" .
next
  have s': "sqrt 3 < 1.7321" using sqrt3_bounds by auto
  have p': "pi \<le> 3.1415926535899" using pi_approx by auto
  have "sqrt 3 * pi / 2 \<le> 1.7321 * 3.1415926535899 / 2"
    using s' p' by (intro divide_right_mono mult_mono) auto
  also have "\<dots> < 2.73" by simp
  finally show "sqrt 3 * pi / 2 < 2.73" .
qed

text \<open>Consistency: TurboQuant's MSE upper bound sits above the information-theoretic
  lower bound (the near-optimality factor is at least 1).\<close>

theorem mse_achievable: "mse_lb b \<le> mse_ub b"
proof -
  have "1 \<le> sqrt 3 * pi / 2" using mse_const_approx by simp
  hence "1 * mse_lb b \<le> (sqrt 3 * pi / 2) * mse_lb b"
    by (intro mult_right_mono) (auto simp: mse_lb_def)
  thus ?thesis by (simp add: mse_ratio_const)
qed

text \<open>High-dimensional advantage (the 1/d factor of paper Thm 2): the inner-product
  distortion bound shrinks as the embedding dimension grows.\<close>

theorem prod_dim_decay:
  assumes "0 < d" and "d \<le> d'" and "0 \<le> ny"
  shows "prod_ub d' ny b \<le> prod_ub d ny b"
  using assms unfolding prod_ub_def
  by (intro divide_right_mono mult_left_mono frac_le) auto

end
