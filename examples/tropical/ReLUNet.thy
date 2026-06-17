(*
  ReLUNet.thy -- ReLU networks are tropical rational functions (Zhang-Naitzat-Lim
  Theorem 5.4, the representational core).

  ReLU is tropical: relu x = max x 0 = x oplus 0, a tropical polynomial. An affine
  map is a tropical monomial. The class of tropical rational functions (TropicalPoly.
  troprat) contains affine maps and ReLU-of-affine, and is closed under the operations
  a feedforward ReLU network performs -- addition, real scaling, finite sums, and ReLU
  post-composition. Hence every scalar function a ReLU network computes is a tropical
  rational function.

  We make this concrete with troprat_one_hidden_layer: a one-hidden-layer ReLU network
  with scalar output,

        x  |->  (SUM k in K. v k * relu (<a k, x> + b k)) + c,

  is a tropical rational function -- a worked instance of Theorem 5.4. We also record
  that every tropical rational function is continuous (troprat_continuous): these are
  the continuous piecewise-linear functions.
*)

theory ReLUNet
  imports TropicalPoly
begin

definition relu :: "real \<Rightarrow> real" where "relu x = max x 0"

text \<open>Closure of the tropical-rational class under the network operations.\<close>

lemma troprat_add:
  assumes "troprat f" "troprat g" shows "troprat (\<lambda>x. f x + g x)"
proof -
  from assms obtain gf hf gg hg where
    "troppoly gf" "troppoly hf" "\<forall>x. f x = gf x - hf x"
    "troppoly gg" "troppoly hg" "\<forall>x. g x = gg x - hg x"
    unfolding troprat_def by blast
  thus ?thesis unfolding troprat_def
    by (intro exI[of _ "\<lambda>x. gf x + gg x"] exI[of _ "\<lambda>x. hf x + hg x"])
       (auto simp: troppoly.add)
qed

lemma troprat_scale:
  assumes "troprat f" shows "troprat (\<lambda>x. c * f x)"
proof -
  from assms obtain g h where g: "troppoly g" and h: "troppoly h" and fx: "\<forall>x. f x = g x - h x"
    unfolding troprat_def by blast
  show ?thesis
  proof (cases "0 \<le> c")
    case True
    have "troppoly (\<lambda>x. c * g x)" and "troppoly (\<lambda>x. c * h x)"
      using troppoly_scale_nonneg[OF g True] troppoly_scale_nonneg[OF h True] by auto
    moreover have "\<forall>x. c * f x = c * g x - c * h x" by (simp add: fx algebra_simps)
    ultimately show ?thesis unfolding troprat_def by blast
  next
    case False
    hence c0: "0 \<le> - c" by simp
    have "troppoly (\<lambda>x. (- c) * h x)" and "troppoly (\<lambda>x. (- c) * g x)"
      using troppoly_scale_nonneg[OF h c0] troppoly_scale_nonneg[OF g c0] by auto
    moreover have "\<forall>x. c * f x = (- c) * h x - (- c) * g x" by (simp add: fx algebra_simps)
    ultimately show ?thesis unfolding troprat_def by blast
  qed
qed

lemma troprat_sum:
  assumes "finite K" "\<And>k. k \<in> K \<Longrightarrow> troprat (f k)"
  shows "troprat (\<lambda>x. \<Sum>k\<in>K. f k x)"
  using assms
proof (induction K rule: finite_induct)
  case empty
  show ?case using troprat_const[of 0] by simp
next
  case (insert k K)
  have eq: "(\<lambda>x. \<Sum>j\<in>insert k K. f j x) = (\<lambda>x. f k x + (\<Sum>j\<in>K. f j x))"
    using insert.hyps by (simp add: fun_eq_iff)
  have "troprat (\<lambda>x. f k x + (\<Sum>j\<in>K. f j x))"
    using insert.prems insert.IH by (intro troprat_add) auto
  thus ?case unfolding eq .
qed

text \<open>ReLU is a tropical polynomial, hence ReLU of a tropical rational function is
  tropical rational: relu (g - h) = max g h - h.\<close>

lemma troprat_relu:
  assumes "troprat f" shows "troprat (\<lambda>x. relu (f x))"
proof -
  from assms obtain g h where g: "troppoly g" and h: "troppoly h" and fx: "\<forall>x. f x = g x - h x"
    unfolding troprat_def by blast
  have "\<forall>x. relu (f x) = max (g x) (h x) - h x"
    using fx by (simp add: relu_def max_def)
  moreover have "troppoly (\<lambda>x. max (g x) (h x))" using g h by (rule troppoly.maxp)
  ultimately show ?thesis unfolding troprat_def using h by blast
qed

lemma troprat_relu_affine: "troprat (\<lambda>x. relu (inner a x + c))"
  by (rule troprat_relu[OF troprat_affine])

text \<open>Theorem 5.4, worked instance: a one-hidden-layer scalar ReLU network is a
  tropical rational function.\<close>

theorem troprat_one_hidden_layer:
  assumes "finite K"
  shows "troprat (\<lambda>x. (\<Sum>k\<in>K. v k * relu (inner (a k) x + b k)) + c)"
proof -
  have "troprat (\<lambda>x. v k * relu (inner (a k) x + b k))" for k
    using troprat_relu_affine by (rule troprat_scale)
  hence "troprat (\<lambda>x. \<Sum>k\<in>K. v k * relu (inner (a k) x + b k))"
    using assms by (intro troprat_sum) auto
  moreover have "troprat (\<lambda>x. c)" by (rule troprat_const)
  ultimately show ?thesis by (rule troprat_add)
qed

text \<open>Every tropical rational function is continuous (it is continuous
  piecewise-linear).\<close>

theorem troprat_continuous:
  "troprat f \<Longrightarrow> continuous_on UNIV (f :: 'a::real_inner \<Rightarrow> real)"
proof -
  assume "troprat f"
  then obtain g h where g: "troppoly g" and h: "troppoly h" and fx: "\<forall>x. f x = g x - h x"
    unfolding troprat_def by blast
  have cont: "continuous_on UNIV p" if "troppoly p" for p :: "'a \<Rightarrow> real"
    using that by (induction rule: troppoly.induct)
       (auto intro!: continuous_intros continuous_on_max)
  have "continuous_on UNIV (\<lambda>x. g x - h x)"
    using cont[OF g] cont[OF h] by (auto intro!: continuous_intros)
  thus ?thesis using fx by (simp cong: continuous_on_cong)
qed

end
