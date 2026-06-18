(*
  JLProjection.thy -- a random projection preserves squared norm in expectation.

  The Johnson-Lindenstrauss lemma (Johnson & Lindenstrauss, "Extensions of Lipschitz
  mappings into a Hilbert space", 1984): n points in a high-dimensional Euclidean space
  can be mapped into O(log n / eps^2) dimensions with all pairwise distances preserved up
  to a factor 1 +/- eps. The standard proof projects with a random matrix R and scales by
  1/sqrt(k); the crux is that the projection preserves each vector's squared length on
  average and concentrates around that average.

  This theory proves the EXPECTATION half (the "distortion-free in expectation" core,
  analogous to the watermark's unbiasedness): for any expectation functional Exp that is
  linear with orthonormal coordinate variables g_j (mean-square 1, uncorrelated),

        Exp[ (SUM_j x_j g_j)^2 ]  =  SUM_j x_j^2  =  ||x||^2.

  We model Exp abstractly by its defining properties (linearity + the second-moment
  identity Exp[g_j g_l] = [j = l]); this is exactly the elementary second-moment
  computation, with the Gaussian concentration around the mean left to JLExistence.thy /
  the meta layer.
*)

theory JLProjection
  imports Complex_Main
begin

text \<open>An expectation functional is linear: additive, zero-preserving, and homogeneous.\<close>

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
  case empty
  show ?case by (simp add: lin0)
next
  case (insert a A)
  have "Exp (\<lambda>s. \<Sum>x\<in>insert a A. F x s) = Exp (\<lambda>s. F a s + (\<Sum>x\<in>A. F x s))"
    using insert.hyps by (simp add: sum.insert)
  also have "\<dots> = Exp (F a) + Exp (\<lambda>s. \<Sum>x\<in>A. F x s)" by (rule lin_add)
  also have "\<dots> = Exp (F a) + (\<Sum>x\<in>A. Exp (F x))" using insert.IH by simp
  also have "\<dots> = (\<Sum>x\<in>insert a A. Exp (F x))" using insert.hyps by (simp add: sum.insert)
  finally show ?case .
qed

corollary expectation_sum':
  fixes Exp :: "('s \<Rightarrow> real) \<Rightarrow> real"
  assumes "lin_exp Exp" and "finite A"
  shows "Exp (\<lambda>s. \<Sum>a\<in>A. F a s) = (\<Sum>a\<in>A. Exp (F a))"
  using assms unfolding lin_exp_def by (intro expectation_sum) auto

text \<open>The unbiasedness identity: the expected squared length of the random projection
  of x equals the squared length of x.\<close>

theorem projection_unbiased:
  fixes Exp :: "('s \<Rightarrow> real) \<Rightarrow> real" and g :: "'j \<Rightarrow> 's \<Rightarrow> real" and x :: "'j \<Rightarrow> real"
  assumes finJ: "finite J"
      and lin_add: "\<And>f h. Exp (\<lambda>s. f s + h s) = Exp f + Exp h"
      and lin0: "Exp (\<lambda>s. 0) = 0"
      and lin_scale: "\<And>a f. Exp (\<lambda>s. a * f s) = a * Exp f"
      and orthonormal: "\<And>j l. j \<in> J \<Longrightarrow> l \<in> J \<Longrightarrow> Exp (\<lambda>s. g j s * g l s) = (if j = l then 1 else 0)"
  shows "Exp (\<lambda>s. (\<Sum>j\<in>J. x j * g j s)\<^sup>2) = (\<Sum>j\<in>J. (x j)\<^sup>2)"
proof -
  have "Exp (\<lambda>s. (\<Sum>j\<in>J. x j * g j s)\<^sup>2)
      = Exp (\<lambda>s. \<Sum>j\<in>J. \<Sum>l\<in>J. (x j * x l) * (g j s * g l s))"
  proof -
    have "(\<Sum>j\<in>J. x j * g j s)\<^sup>2 = (\<Sum>j\<in>J. \<Sum>l\<in>J. (x j * x l) * (g j s * g l s))" for s
      by (simp add: power2_eq_square sum_product) (simp add: mult.commute mult.left_commute)
    thus ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>j\<in>J. Exp (\<lambda>s. \<Sum>l\<in>J. (x j * x l) * (g j s * g l s)))"
    using lin_add lin0 finJ by (rule expectation_sum)
  also have "\<dots> = (\<Sum>j\<in>J. \<Sum>l\<in>J. Exp (\<lambda>s. (x j * x l) * (g j s * g l s)))"
  proof (rule sum.cong[OF refl])
    fix j assume "j \<in> J"
    show "Exp (\<lambda>s. \<Sum>l\<in>J. (x j * x l) * (g j s * g l s))
        = (\<Sum>l\<in>J. Exp (\<lambda>s. (x j * x l) * (g j s * g l s)))"
      using lin_add lin0 finJ by (rule expectation_sum)
  qed
  also have "\<dots> = (\<Sum>j\<in>J. \<Sum>l\<in>J. (x j * x l) * Exp (\<lambda>s. g j s * g l s))"
    by (simp add: lin_scale)
  also have "\<dots> = (\<Sum>j\<in>J. \<Sum>l\<in>J. (x j * x l) * (if j = l then 1 else 0))"
    using orthonormal by simp
  also have "\<dots> = (\<Sum>j\<in>J. (x j)\<^sup>2)"
  proof (rule sum.cong[OF refl])
    fix j assume j: "j \<in> J"
    have "(\<Sum>l\<in>J. x j * x l * (if j = l then 1 else 0)) = (\<Sum>l\<in>J. if l = j then x j * x j else 0)"
      by (rule sum.cong[OF refl]) auto
    also have "\<dots> = x j * x j" using j finJ by (simp add: sum.delta)
    finally show "(\<Sum>l\<in>J. x j * x l * (if j = l then 1 else 0)) = (x j)\<^sup>2"
      by (simp add: power2_eq_square)
  qed
  finally show ?thesis .
qed

text \<open>Bounded-quantifier surface form, with linearity bundled into @{const lin_exp}.\<close>

corollary projection_unbiased':
  fixes Exp :: "('s \<Rightarrow> real) \<Rightarrow> real" and g :: "'j \<Rightarrow> 's \<Rightarrow> real" and x :: "'j \<Rightarrow> real"
  assumes "finite J" and "lin_exp Exp"
      and "\<forall>j\<in>J. \<forall>l\<in>J. Exp (\<lambda>s. g j s * g l s) = (if j = l then 1 else 0)"
  shows "Exp (\<lambda>s. (\<Sum>j\<in>J. x j * g j s)\<^sup>2) = (\<Sum>j\<in>J. (x j)\<^sup>2)"
  using assms unfolding lin_exp_def by (intro projection_unbiased) auto

end
