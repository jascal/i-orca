(*
  Ternary.thy -- the multiplication-free ternary matmul, and the absmean quantizer.

  BitNet b1.58 (Ma, Wang, Ma, Wang, Wang, Huang, Dong, Wang, Xue & Wei, "The Era of 1-bit
  LLMs: All Large Language Models are in 1.58 Bits", Microsoft Research, arXiv:2402.17764,
  2024) replaces every weight of a Transformer with a ternary value in {-1, 0, 1}. The
  central computational payoff: a matrix multiply by a ternary weight matrix needs NO
  multiplications -- it is a signed sum (additions and subtractions only). The weights are
  produced from a real matrix by an "absmean" RoundClip quantizer.

  This theory pins:
    tprod / tprod_is_mult     : a ternary weight times x is +x, 0, or -x (no real multiply);
    ternary_dot_signed_sum    : the ternary dot product is (sum over the +1 weights of x_i)
                                minus (sum over the -1 weights), i.e. additions only;
    roundclip / roundclip_ternary : the absmean quantizer maps into {-1, 0, 1};
    roundclip_not_injective   : that quantizer is non-injective -- per-weight ternarization
                                is necessarily LOSSY (the honest counterpoint to the
                                lossless-by-expansion result in Lossless.thy).
*)

theory Ternary
  imports Complex_Main
begin

text \<open>A ternary weight acts on x without multiplication: +x, -x, or 0.\<close>

definition tprod :: "int \<Rightarrow> 'a::ring_1 \<Rightarrow> 'a" where
  "tprod w x = (if w = 1 then x else if w = - 1 then - x else 0)"

lemma tprod_is_mult: "w \<in> {-1, 0, 1} \<Longrightarrow> tprod w x = of_int w * x"
  by (auto simp: tprod_def)

text \<open>The ternary dot product is a signed sum: the sum of x over the +1 weights minus the
  sum over the -1 weights. No multiplications -- additions and subtractions only.\<close>

theorem ternary_dot_signed_sum:
  fixes w :: "'i \<Rightarrow> int" and x :: "'i \<Rightarrow> 'a::ring_1"
  assumes "finite I" and "\<forall>i\<in>I. w i \<in> {-1, 0, 1}"
  shows "(\<Sum>i\<in>I. tprod (w i) (x i))
       = (\<Sum>i\<in>{i\<in>I. w i = 1}. x i) - (\<Sum>i\<in>{i\<in>I. w i = - 1}. x i)"
proof -
  have "(\<Sum>i\<in>I. tprod (w i) (x i))
      = (\<Sum>i\<in>{i\<in>I. w i = 1}. tprod (w i) (x i)) + (\<Sum>i\<in>{i\<in>I. w i \<noteq> 1}. tprod (w i) (x i))"
    using assms(1) by (subst sum.union_disjoint[symmetric]) (auto intro: sum.cong)
  also have "(\<Sum>i\<in>{i\<in>I. w i = 1}. tprod (w i) (x i)) = (\<Sum>i\<in>{i\<in>I. w i = 1}. x i)"
    by (simp add: tprod_def)
  also have "(\<Sum>i\<in>{i\<in>I. w i \<noteq> 1}. tprod (w i) (x i)) = - (\<Sum>i\<in>{i\<in>I. w i = - 1}. x i)"
  proof -
    have "(\<Sum>i\<in>{i\<in>I. w i \<noteq> 1}. tprod (w i) (x i))
        = (\<Sum>i\<in>{i\<in>I. w i = - 1}. tprod (w i) (x i)) + (\<Sum>i\<in>{i\<in>I. w i \<noteq> 1 \<and> w i \<noteq> - 1}. tprod (w i) (x i))"
      using assms(1) by (subst sum.union_disjoint[symmetric]) (auto intro: sum.cong)
    moreover have "(\<Sum>i\<in>{i\<in>I. w i = - 1}. tprod (w i) (x i)) = - (\<Sum>i\<in>{i\<in>I. w i = - 1}. x i)"
      by (simp add: tprod_def sum_negf)
    moreover have "(\<Sum>i\<in>{i\<in>I. w i \<noteq> 1 \<and> w i \<noteq> - 1}. tprod (w i) (x i)) = 0"
      using assms(2) by (auto simp: tprod_def intro!: sum.neutral)
    ultimately show ?thesis by simp
  qed
  finally show ?thesis by simp
qed

text \<open>The absmean RoundClip quantizer: round to nearest, then clip into [-1, 1] (after
  scaling by the mean absolute value). It maps any real into the ternary set.\<close>

definition roundclip :: "real \<Rightarrow> int" where
  "roundclip x = max (- 1) (min 1 (round x))"

theorem roundclip_ternary: "roundclip x \<in> {-1, 0, 1}"
  by (auto simp: roundclip_def)

text \<open>The quantizer is non-injective: distinct weights collapse to the same ternary value,
  so per-weight ternarization cannot be inverted -- it is necessarily lossy.\<close>

theorem roundclip_not_injective: "\<exists>a b. a \<noteq> b \<and> roundclip a = roundclip b"
proof -
  have "(0.3::real) \<noteq> 0.4" by simp
  moreover have "roundclip 0.3 = roundclip 0.4" by (simp add: roundclip_def round_def)
  ultimately show ?thesis by blast
qed

end
