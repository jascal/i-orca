theory RecoveredProbability
  imports Complex_Main
begin

text \<open>Theorem 4. With a uniform base measure M_0 reweighted by exp(c_j^v) per source, the normalised mass m(v)/Σ_w m(w) = exp(L_v)/Z is exactly the softmax — the Gibbs measure recovered as a PIC incidence frequency, parameter-free.\<close>
theorem recoveredprobability:
  assumes
    M0pos: "(M0::real) > 0"
  shows "(M0 * exp (L v)) / (\<Sum>w\<in>V. M0 * exp (L w)) = exp (L v) / (\<Sum>w\<in>V. exp (L w))"
proof -
  have s1: "(\<Sum>w\<in>V. M0 * exp (L w)) = M0 * (\<Sum>w\<in>V. exp (L w))" by (simp add: sum_distrib_left)
  have s2: "M0 \<noteq> 0" using M0pos by (metis less_irrefl)
  show "(M0 * exp (L v)) / (\<Sum>w\<in>V. M0 * exp (L w)) = exp (L v) / (\<Sum>w\<in>V. exp (L w))" using s1 s2 by (simp add: mult_divide_mult_cancel_left)
qed

end
