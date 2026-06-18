(*
  JLDimension.thy -- the logarithmic target dimension.

  The famous quantitative content of Johnson-Lindenstrauss: a target dimension of order
  log(n)/eps^2 is enough. The mechanism is a union bound over the pairs. If each of N
  constraints fails with probability at most exp(-c k) -- the Gaussian concentration of
  the random projection, with c proportional to eps^2 -- then the total failure
  probability N * exp(-c k) drops below 1 as soon as

        k  >  ln N / c.

  jl_dimension is that elementary real-analysis fact. With N = n^2 pairs (an overcount of
  n-choose-2) and c = eps^2/8, jl_log_dimension reads off the bound k > 16 ln(n)/eps^2 --
  the O(log n / eps^2) target dimension (the constant is schematic: it tracks the
  concentration constant c, not pinned here).
*)

theory JLDimension
  imports Complex_Main
begin

text \<open>The union-bound dimension inequality: once k exceeds ln N / c, the total failure
  bound is below 1.\<close>

theorem jl_dimension:
  fixes N c k :: real
  assumes "0 < N" and "0 < c" and "ln N / c < k"
  shows "N * exp (- c * k) < 1"
proof -
  have "ln N < c * k" using assms by (simp add: pos_divide_less_eq mult.commute)
  hence "N < exp (c * k)" using assms(1) by (metis exp_less_cancel_iff exp_ln)
  hence "N * exp (- c * k) < exp (c * k) * exp (- c * k)"
    by (simp add: mult_strict_right_mono)
  also have "\<dots> = 1" by (simp add: mult_exp_exp)
  finally show ?thesis .
qed

text \<open>The logarithmic target dimension: k > 16 ln(n)/eps^2 drives the n^2-term union
  bound below 1 (with the per-pair concentration constant c = eps^2/8).\<close>

corollary jl_log_dimension:
  fixes n :: nat and eps k :: real
  assumes n2: "2 \<le> n" and eps: "0 < eps"
      and k: "(16 * ln (real n)) / eps\<^sup>2 < k"
  shows "real (n * n) * exp (- (eps\<^sup>2 / 8) * k) < 1"
proof -
  have rn: "1 < real n" using n2 by simp
  have Npos: "0 < real (n * n)" using n2 by simp
  have cpos: "0 < eps\<^sup>2 / 8" using eps by simp
  have lnNN: "ln (real (n * n)) = 2 * ln (real n)"
  proof -
    have "real (n * n) = real n * real n" by simp
    thus ?thesis using rn by (simp add: ln_mult)
  qed
  have ekey: "eps\<^sup>2 \<noteq> 0" using eps by simp
  have eq: "ln (real (n * n)) / (eps\<^sup>2 / 8) = (16 * ln (real n)) / eps\<^sup>2"
    using lnNN ekey by (simp add: field_simps)
  have lt: "ln (real (n * n)) / (eps\<^sup>2 / 8) < k" by (simp only: eq) (rule k)
  show ?thesis using Npos cpos lt by (rule jl_dimension)
qed

end
