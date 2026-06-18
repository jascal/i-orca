(*
  Unbiased.thy -- TurboQuant's unbiased inner-product estimator (Theorem 2).

  MSE-optimal quantizers are biased for inner-product estimation; TurboQuant fixes this
  with a two-stage scheme -- an MSE quantizer followed by a 1-bit Quantized-JL transform
  on the residual -- yielding an UNBIASED inner-product estimator:

        E[ <y, dequant(x)> ]  =  <y, x>.

  The unbiasedness reduces to: if the dequantized vector is COORDINATEWISE unbiased
  (E[dq_j] = x_j) and the expectation is linear, then by linearity the inner product
  <y, dq> is unbiased. We model the expectation abstractly by its linearity (lin_exp),
  exactly as in the Johnson-Lindenstrauss corpus; the QJL construction that delivers the
  per-coordinate unbiasedness is the meta input.
*)

theory Unbiased
  imports Complex_Main
begin

definition lin_exp :: "(('s \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> bool" where
  "lin_exp Exp \<longleftrightarrow> (\<forall>f h. Exp (\<lambda>s. f s + h s) = Exp f + Exp h)
                  \<and> Exp (\<lambda>s. 0) = 0
                  \<and> (\<forall>a f. Exp (\<lambda>s. a * f s) = a * Exp f)"

text \<open>A linear expectation functional commutes with finite sums.\<close>

lemma expectation_sum:
  fixes Exp :: "('s \<Rightarrow> real) \<Rightarrow> real"
  assumes lin_add: "\<And>f h. Exp (\<lambda>s. f s + h s) = Exp f + Exp h"
      and lin0: "Exp (\<lambda>s. 0) = 0"
      and finA: "finite A"
  shows "Exp (\<lambda>s. \<Sum>a\<in>A. F a s) = (\<Sum>a\<in>A. Exp (F a))"
  using finA
proof (induction A rule: finite_induct)
  case empty thus ?case by (simp add: lin0)
next
  case (insert a A)
  have "Exp (\<lambda>s. \<Sum>x\<in>insert a A. F x s) = Exp (\<lambda>s. F a s + (\<Sum>x\<in>A. F x s))"
    using insert.hyps by (simp add: sum.insert)
  also have "\<dots> = Exp (F a) + Exp (\<lambda>s. \<Sum>x\<in>A. F x s)" by (rule lin_add)
  also have "\<dots> = (\<Sum>x\<in>insert a A. Exp (F x))" using insert by (simp add: sum.insert)
  finally show ?case .
qed

corollary expectation_sum':
  fixes Exp :: "('s \<Rightarrow> real) \<Rightarrow> real"
  assumes "lin_exp Exp" and "finite A"
  shows "Exp (\<lambda>s. \<Sum>a\<in>A. F a s) = (\<Sum>a\<in>A. Exp (F a))"
  using assms unfolding lin_exp_def by (intro expectation_sum) auto

text \<open>The inner-product estimator is unbiased (the unbiasedness claim of paper Thm 2):
  from coordinatewise unbiasedness of the dequantized residual and linearity,
  E[<y, dq>] = <y, x>.\<close>

theorem inner_product_unbiased:
  fixes Exp :: "('s \<Rightarrow> real) \<Rightarrow> real" and dq :: "'j \<Rightarrow> 's \<Rightarrow> real" and x y :: "'j \<Rightarrow> real"
  assumes finJ: "finite J"
      and lin_add: "\<And>f h. Exp (\<lambda>s. f s + h s) = Exp f + Exp h"
      and lin0: "Exp (\<lambda>s. 0) = 0"
      and lin_scale: "\<And>a f. Exp (\<lambda>s. a * f s) = a * Exp f"
      and unbiased: "\<And>j. j \<in> J \<Longrightarrow> Exp (dq j) = x j"
  shows "Exp (\<lambda>s. \<Sum>j\<in>J. y j * dq j s) = (\<Sum>j\<in>J. y j * x j)"
proof -
  have "Exp (\<lambda>s. \<Sum>j\<in>J. y j * dq j s) = (\<Sum>j\<in>J. Exp (\<lambda>s. y j * dq j s))"
    using lin_add lin0 finJ by (rule expectation_sum)
  also have "\<dots> = (\<Sum>j\<in>J. y j * Exp (dq j))" by (simp add: lin_scale)
  also have "\<dots> = (\<Sum>j\<in>J. y j * x j)" using unbiased by simp
  finally show ?thesis .
qed

corollary inner_product_unbiased':
  fixes Exp :: "('s \<Rightarrow> real) \<Rightarrow> real" and dq :: "'j \<Rightarrow> 's \<Rightarrow> real" and x y :: "'j \<Rightarrow> real"
  assumes "finite J" and "lin_exp Exp"
      and "\<forall>j\<in>J. Exp (dq j) = x j"
  shows "Exp (\<lambda>s. \<Sum>j\<in>J. y j * dq j s) = (\<Sum>j\<in>J. y j * x j)"
  using assms unfolding lin_exp_def by (intro inner_product_unbiased) auto

end
