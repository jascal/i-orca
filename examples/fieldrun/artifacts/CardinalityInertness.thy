theory CardinalityInertness
  imports Main
begin

text \<open>Theorem 1. Under the projective pairing the decision depends only on the totals (hence on {Δ, D_j}) and is invariant to the readout multiplicity μ_t: two source tensors c, c′ with equal column sums induce the same argmax even when their per-source argmax counts μ_t differ.\<close>
theorem cardinalityinertness:
  assumes
    eqtot: "\<And>v. (\<Sum>j\<in>J. c j v) = (\<Sum>j\<in>J. c' j v)"
  shows "(\<forall>w\<in>V. (\<Sum>j\<in>J. c j w) \<le> (\<Sum>j\<in>J. c j t)) = (\<forall>w\<in>V. (\<Sum>j\<in>J. c' j w) \<le> (\<Sum>j\<in>J. c' j t))"
proof -
  have s_tot: "\<And>w. (\<Sum>j\<in>J. c j w) = (\<Sum>j\<in>J. c' j w)" using eqtot by (simp add: eqtot)
  show "(\<forall>w\<in>V. (\<Sum>j\<in>J. c j w) \<le> (\<Sum>j\<in>J. c j t)) = (\<forall>w\<in>V. (\<Sum>j\<in>J. c' j w) \<le> (\<Sum>j\<in>J. c' j t))" using s_tot by (simp add: s_tot)
qed

end
