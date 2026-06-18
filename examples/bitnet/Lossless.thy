(*
  Lossless.thy -- the lossless ternary realization.

  This is the affirmative answer to "can a finite-precision network be transformed into a
  ternary (BitNet-style) one without loss?". Per-weight ternarization is lossy
  (Ternary.roundclip_not_injective), but a LOSSLESS realization exists by EXPANSION:

    lossless_realization : an integer-weight dot product equals a power-of-3 weighted sum
                           of ternary dot products -- distributing each weight's
                           balanced-ternary digits through the matmul. The real (integer)
                           layer's exact output is recovered from ternary matmuls.

    lossless_weight      : the unconditional single-weight form -- every integer weight w,
                           acting on x, equals SUM_j 3^j * (t_j * x) with each t_j ternary
                           (each t_j * x is +x, 0, or -x, i.e. multiplication-free).

  The price of losslessness is the expansion factor (the number of ternary digits K ~
  precision / log2 3); minimising it -- the sparsest behaviourally-equivalent ternary net,
  exactly or within epsilon on a dataset -- is the genuine optimisation problem (NP-hard in
  general), well-posed over a relational / Datalog encoding of the network.
*)

theory Lossless
  imports BalancedTernary
begin

text \<open>The lossless realization: distribute the balanced-ternary digits through the matmul.
  An integer-weight dot product equals a power-of-3 weighted sum of ternary dot products.\<close>

theorem lossless_realization:
  fixes t :: "'i \<Rightarrow> nat \<Rightarrow> int" and x :: "'i \<Rightarrow> int" and K :: nat
  assumes "finite I"
  shows "(\<Sum>i\<in>I. (\<Sum>j<K. t i j * 3 ^ j) * x i)
       = (\<Sum>j<K. 3 ^ j * (\<Sum>i\<in>I. t i j * x i))"
proof -
  have "(\<Sum>i\<in>I. (\<Sum>j<K. t i j * 3 ^ j) * x i)
      = (\<Sum>i\<in>I. \<Sum>j<K. (3 ^ j * (t i j * x i)))"
    by (simp add: sum_distrib_right sum_distrib_left mult_ac)
  also have "\<dots> = (\<Sum>j<K. \<Sum>i\<in>I. (3 ^ j * (t i j * x i)))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>j<K. 3 ^ j * (\<Sum>i\<in>I. t i j * x i))"
    by (simp add: sum_distrib_left)
  finally show ?thesis .
qed

text \<open>The unconditional single-weight form: every integer weight, acting on x, is exactly a
  power-of-3 weighted sum of ternary products (each t_j * x is +x, 0, or -x).\<close>

corollary lossless_weight:
  fixes w x :: int
  shows "\<exists>ts. (\<forall>d\<in>set ts. d \<in> {-1, 0, 1}) \<and> w * x = (\<Sum>j<length ts. 3 ^ j * (ts ! j * x))"
proof -
  obtain ts where ts: "\<forall>d\<in>set ts. d \<in> {-1, 0, 1}" "w = (\<Sum>j<length ts. ts ! j * 3 ^ j)"
    using balanced_ternary_exists by blast
  have "w * x = (\<Sum>j<length ts. ts ! j * 3 ^ j) * x" using ts(2) by simp
  also have "\<dots> = (\<Sum>j<length ts. 3 ^ j * (ts ! j * x))"
    by (simp add: sum_distrib_right sum_distrib_left mult_ac)
  finally show ?thesis using ts(1) by blast
qed

end
