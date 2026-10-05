(*
  PIC_Cleanup.thy -- T6(b): the constants of clean-up (unbind -> nearest filler -> rebind)
  (examples/pic_binding/PROPOSAL.md, T6).

  Code points x(sigma) = W (structure_tpr f r sigma D) + b0; host residual u = x(sigma) + n.

    nearest_point_cleanup / nearest_point_selects : in any metric space, a gamma-separated code and a query within
                                    gamma/2 of a code point: that point is the UNIQUE nearest one;
    nearest_point_radius_tight    : gamma/2 cannot be enlarged (the midpoint is equidistant);
    unbind_norm_le                : |unbind e w| <= |e| * |w| (Frobenius norm on real^'m^'n);
    role_cleanup_close            : with <r s, w> = 1, the role-s readout is within
                                    crosstalk_s + |e| |w| of the true filler f (sigma s);
    role_cleanup                  : that distance < gamma_s / 2  ==>  the nearest filler is sigma s;
    cleanup_exact                 : every role correct  ==>  the rebound tensor equals structure_tpr f r sigma D;
    left_inverse_noise            : P linear with P (W T) = T and |P y| <= K |y|  ==>  |P (u - b0) - T| <= K |n|;
    agreement_ball                : |n| |U t - U v| < m_v(x) for every rival  ==>  the host x + n decides t;
    cleanup_certified             : the composition -- clean-up returns x(sigma) exactly AND the host decides
                                    the code point's decision t.

  HONEST SCOPE. Clean-up does not change the HOST's margin. It makes the substitute exactly a code point, so the
  certificate is issued from the CODE's margin (agreement_ball) over a whole ball of residuals. Whether host
  residuals lie within min(rho, beta) of their code points is empirical. Self-contained over PIC_Binding;
  0 sorry, quick_and_dirty = false.
*)
theory PIC_Cleanup
  imports PIC_Binding
begin

section \<open>Nearest-point clean-up in a metric space\<close>

theorem nearest_point_cleanup:
  fixes c :: "'a \<Rightarrow> 'x::metric_space"
  assumes sep: "\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<gamma> \<le> dist (c a) (c a')"
      and a: "a \<in> A" and close: "dist g (c a) < \<gamma> / 2"
  shows "\<forall>a'\<in>A. a' \<noteq> a \<longrightarrow> dist g (c a) < dist g (c a')"
proof (intro ballI impI)
  fix a' assume a': "a' \<in> A" and ne: "a' \<noteq> a"
  have "\<gamma> \<le> dist (c a) (c a')" using sep a a' ne by auto
  also have "\<dots> \<le> dist (c a) g + dist g (c a')" by (rule dist_triangle)
  finally have "\<gamma> \<le> dist g (c a) + dist g (c a')" by (simp add: dist_commute)
  thus "dist g (c a) < dist g (c a')" using close by linarith
qed

corollary nearest_point_selects:
  fixes c :: "'a \<Rightarrow> 'x::metric_space"
  assumes sep: "\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<gamma> \<le> dist (c a) (c a')"
      and a: "a \<in> A" and close: "dist g (c a) < \<gamma> / 2"
      and ah: "ah \<in> A" and near: "\<forall>a'\<in>A. dist g (c ah) \<le> dist g (c a')"
  shows "ah = a"
proof (rule ccontr)
  assume ne: "ah \<noteq> a"
  have "dist g (c a) < dist g (c ah)" using nearest_point_cleanup[OF sep a close] ah ne by blast
  moreover have "dist g (c ah) \<le> dist g (c a)" using near a by blast
  ultimately show False by linarith
qed

text \<open>gamma/2 is tight: two code points gamma apart, and the midpoint is equidistant from both.\<close>
lemma nearest_point_radius_tight:
  fixes \<gamma> :: real
  shows "dist (\<gamma> / 2) 0 = \<bar>\<gamma>\<bar> / 2 \<and> dist (\<gamma> / 2) \<gamma> = \<bar>\<gamma>\<bar> / 2"
  by (simp add: dist_real_def)

section \<open>Unbinding is bounded\<close>

lemma unbind_add: "unbind (A + B) w = unbind A w + unbind B w"
  by (simp add: unbind_def vec_eq_iff inner_add_left)

lemma unbind_norm_le: "norm (unbind e w) \<le> norm e * norm w"
proof -
  have comp: "norm (unbind e w $ i) \<le> norm w * norm (e $ i)" for i
    using Cauchy_Schwarz_ineq2[of "e $ i" w] by (simp add: unbind_def mult.commute)
  have "norm (unbind e w) = L2_set (\<lambda>i. norm (unbind e w $ i)) UNIV" by (simp add: norm_vec_def)
  also have "\<dots> \<le> L2_set (\<lambda>i. norm w * norm (e $ i)) UNIV"
    by (rule L2_set_mono) (use comp in auto)
  also have "\<dots> = norm w * L2_set (\<lambda>i. norm (e $ i)) UNIV"
    by (simp add: L2_set_right_distrib)
  also have "\<dots> = norm e * norm w" by (simp add: norm_vec_def mult.commute)
  finally show ?thesis .
qed

section \<open>Role clean-up\<close>

lemma unbind_structure:
  assumes "finite D"
  shows "unbind (structure_tpr f r \<sigma> D) w = (\<Sum>t\<in>D. inner (r t) w *\<^sub>R f (\<sigma> t))"
  by (simp add: structure_tpr_def unbind_sum unbind_tprod)

theorem role_cleanup_close:
  assumes finD: "finite D" and s: "s \<in> D" and one: "inner (r s) w = 1"
  shows "norm (unbind (structure_tpr f r \<sigma> D + e) w - f (\<sigma> s))
         \<le> norm (\<Sum>t\<in>D - {s}. inner (r t) w *\<^sub>R f (\<sigma> t)) + norm e * norm w"
proof -
  have split: "(\<Sum>t\<in>D. inner (r t) w *\<^sub>R f (\<sigma> t))
               = f (\<sigma> s) + (\<Sum>t\<in>D - {s}. inner (r t) w *\<^sub>R f (\<sigma> t))"
    using sum.remove[OF finD s, of "\<lambda>t. inner (r t) w *\<^sub>R f (\<sigma> t)"] one by simp
  have "unbind (structure_tpr f r \<sigma> D + e) w - f (\<sigma> s)
        = (\<Sum>t\<in>D - {s}. inner (r t) w *\<^sub>R f (\<sigma> t)) + unbind e w"
    by (simp add: unbind_add unbind_structure[OF finD] split)
  also have "norm \<dots> \<le> norm (\<Sum>t\<in>D - {s}. inner (r t) w *\<^sub>R f (\<sigma> t)) + norm (unbind e w)"
    by (rule norm_triangle_ineq)
  also have "\<dots> \<le> norm (\<Sum>t\<in>D - {s}. inner (r t) w *\<^sub>R f (\<sigma> t)) + norm e * norm w"
    using unbind_norm_le by simp
  finally show ?thesis .
qed

theorem role_cleanup:
  fixes f :: "'b \<Rightarrow> real^'n"
  assumes finD: "finite D" and s: "s \<in> D" and one: "inner (r s) w = 1"
      and sep: "\<forall>a\<in>F. \<forall>a'\<in>F. a \<noteq> a' \<longrightarrow> \<gamma> \<le> dist (f a) (f a')"
      and inF: "\<sigma> s \<in> F"
      and budget: "norm (\<Sum>t\<in>D - {s}. inner (r t) w *\<^sub>R f (\<sigma> t)) + norm e * norm w < \<gamma> / 2"
      and ah: "ah \<in> F"
      and near: "\<forall>a'\<in>F. dist (unbind (structure_tpr f r \<sigma> D + e) w) (f ah)
                         \<le> dist (unbind (structure_tpr f r \<sigma> D + e) w) (f a')"
  shows "ah = \<sigma> s"
proof (rule nearest_point_selects[OF sep inF _ ah near])
  show "dist (unbind (structure_tpr f r \<sigma> D + e) w) (f (\<sigma> s)) < \<gamma> / 2"
    using role_cleanup_close[where D = D and s = s and r = r and w = w and f = f and \<sigma> = \<sigma> and e = e,
                             OF finD s one] budget by (simp add: dist_norm)
qed

theorem cleanup_exact:
  assumes allroles: "\<forall>s\<in>D. \<sigma>h s = \<sigma> s"
  shows "structure_tpr f r \<sigma>h D = structure_tpr f r \<sigma> D"
  unfolding structure_tpr_def using allroles by (intro sum.cong) auto

section \<open>Residual-space noise through a left inverse\<close>

lemma left_inverse_noise:
  assumes lin: "linear P" and inv: "\<forall>T. P (W T) = T" and K: "\<forall>y. norm (P y) \<le> K * norm y"
  shows "norm (P (u - b0) - T) \<le> K * norm (u - (W T + b0))"
proof -
  have "P (u - b0) - T = P (u - b0) - P (W T)" using inv by simp
  also have "\<dots> = P (u - (W T + b0))" by (simp add: linear_diff[OF lin, symmetric] algebra_simps)
  finally show ?thesis using K by simp
qed

section \<open>The agreement ball: certify from the code point's margin\<close>

theorem agreement_ball:
  fixes U :: "'v \<Rightarrow> 'a::real_inner"
  assumes tV: "t \<in> V"
      and ball: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow>
                   norm n * norm (U t - U v) < (inner x (U t) + bias t) - (inner x (U v) + bias v)"
  shows "decodes_to (\<lambda>v. inner (x + n) (U v) + bias v) V t"
proof (rule substitution_certified_pairwise[where r = x, OF tV], intro ballI impI)
  fix v assume v: "v \<in> V" and ne: "v \<noteq> t"
  have "inner (x - (x + n)) (U t - U v) = - inner n (U t - U v)" by (simp add: inner_minus_left)
  also have "\<dots> \<le> norm n * norm (U t - U v)"
    using Cauchy_Schwarz_ineq2[of n "U t - U v"] by linarith
  finally show "(inner x (U t) + bias t) - (inner x (U v) + bias v) > inner (x - (x + n)) (U t - U v)"
    using ball v ne by fastforce
qed

section \<open>The T6(b) certificate\<close>

theorem cleanup_certified:
  fixes f :: "'b \<Rightarrow> real^'n" and U :: "'v \<Rightarrow> 'd::real_inner"
    and W :: "real^'m^'n \<Rightarrow> 'd" and P :: "'d \<Rightarrow> real^'m^'n"
  assumes finD: "finite D"
      and lin: "linear P" and inv: "\<forall>T. P (W T) = T" and K: "\<forall>y. norm (P y) \<le> K * norm y"
      and one: "\<forall>s\<in>D. inner (r s) (w s) = 1"
      and sep: "\<forall>s\<in>D. \<forall>a\<in>F s. \<forall>a'\<in>F s. a \<noteq> a' \<longrightarrow> \<gamma> s \<le> dist (f a) (f a')"
      and inF: "\<forall>s\<in>D. \<sigma> s \<in> F s"
      and rho: "\<forall>s\<in>D. norm (\<Sum>t\<in>D - {s}. inner (r t) (w s) *\<^sub>R f (\<sigma> t))
                        + K * norm (u - x) * norm (w s) < \<gamma> s / 2"
      and xdef: "x = W (structure_tpr f r \<sigma> D) + b0"
      and ah: "\<forall>s\<in>D. \<sigma>h s \<in> F s"
      and near: "\<forall>s\<in>D. \<forall>a'\<in>F s. dist (unbind (P (u - b0)) (w s)) (f (\<sigma>h s))
                                   \<le> dist (unbind (P (u - b0)) (w s)) (f a')"
      and tV: "t \<in> V"
      and beta: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow>
                   norm (u - x) * norm (U t - U v) < (inner x (U t) + bias t) - (inner x (U v) + bias v)"
  shows "W (structure_tpr f r \<sigma>h D) + b0 = x"
    and "decodes_to (\<lambda>v. inner u (U v) + bias v) V t"
proof -
  define e where "e = P (u - b0) - structure_tpr f r \<sigma> D"
  have Pu: "P (u - b0) = structure_tpr f r \<sigma> D + e" by (simp add: e_def)
  have ne: "norm e \<le> K * norm (u - x)"
    unfolding e_def xdef by (rule left_inverse_noise[OF lin inv K])
  have roles: "\<forall>s\<in>D. \<sigma>h s = \<sigma> s"
  proof
    fix s assume s: "s \<in> D"
    have "norm e * norm (w s) \<le> K * norm (u - x) * norm (w s)"
      using ne by (simp add: mult_right_mono)
    hence b: "norm (\<Sum>t\<in>D - {s}. inner (r t) (w s) *\<^sub>R f (\<sigma> t)) + norm e * norm (w s) < \<gamma> s / 2"
      using rho s by fastforce
    show "\<sigma>h s = \<sigma> s"
    proof (rule role_cleanup[where D = D and s = s and r = r and w = "w s" and f = f and \<sigma> = \<sigma> and e = e
                                 and F = "F s" and \<gamma> = "\<gamma> s" and ah = "\<sigma>h s"])
    qed (use finD s one sep inF ah near Pu b in auto)
  qed
  have "structure_tpr f r \<sigma>h D = structure_tpr f r \<sigma> D" by (rule cleanup_exact[OF roles])
  thus "W (structure_tpr f r \<sigma>h D) + b0 = x" using xdef by simp
  have "decodes_to (\<lambda>v. inner (x + (u - x)) (U v) + bias v) V t"
    by (rule agreement_ball[OF tV beta])
  thus "decodes_to (\<lambda>v. inner u (U v) + bias v) V t" by simp
qed

end
