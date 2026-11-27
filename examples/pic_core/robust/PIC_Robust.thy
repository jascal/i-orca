(*
  PIC_Robust.thy -- correlation-aware decision certificates (spec/PIC_SPEC.md S5.5a (a), (b)).

  The margin certificate (PIC_Logic.decode_margin_certified) bounds every logit separately, so the winner
  may fall by delta while a rival rises by delta. When both moves come from ONE perturbation of the
  residual, or from one set of sources, they are linked. Two exact statements keep the link:

    (a) gram_radius_sound / gram_radius_tight / gram_radius_exact
        A residual perturbation r -> r + Delta changes the margin to rival w by exactly
        <Delta, U t - U w>. So t stays the strict argmax for every ||Delta|| <= rho  IFF
        rho * ||U t - U w|| < m_tw for every rival w (rho >= 0). The radius is set by Gram distances,
        ||U t - U w||^2 = G(t,t) + G(w,w) - 2 G(t,w).
        gram_radius_imp_margin_bound: it is never weaker than the per-token 2*rho*K bound
        (K bounds every ||U v||).

    (b) all_coalitions_certified (locale pic) / zonotope_all_coalitions / zonotope_cube
        Head H, tail T (disjoint, finite). Every coalition H u P, P a subset of T, decides t  IFF
        for every rival w:  m_tw(H) + sum_{j in T} min 0 (c_j(t) - c_j(w)) > 0.
        The same condition is exact for fractional ablation weights lambda in [0,1]^T (a zonotope of
        residuals): the corners of the cube are the Boolean coalitions.
        interval_imp_zonotope: the per-token interval check implies it (sound, weaker).

  Imports PIC_Core only; 0 sorry; quick_and_dirty = false.
*)
theory PIC_Robust
  imports PIC_Core.PIC_Core
begin

section \<open>(a) The Gram-distance radius\<close>

context pic_frame
begin

text \<open>The logit read at residual @{term r}, and the decision at @{term r} over candidates @{term Vs}.\<close>
definition Lr :: "'a \<Rightarrow> 'v \<Rightarrow> real" where
  "Lr r v = inner r (U v) + b v"

definition rdecides :: "'a \<Rightarrow> 'v set \<Rightarrow> 'v \<Rightarrow> bool" where
  "rdecides r Vs t \<longleftrightarrow> (\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow> Lr r w < Lr r t)"

text \<open>A residual perturbation moves the pairwise margin by exactly the inner product with the frame
  difference: the shared part of the two logit moves cancels.\<close>
lemma Lr_shift:
  "Lr (r + \<Delta>) t - Lr (r + \<Delta>) w = (Lr r t - Lr r w) + inner \<Delta> (U t - U w)"
  unfolding Lr_def by (simp add: inner_add_left inner_diff_right)

theorem gram_radius_sound:
  assumes marg: "\<And>w. w \<in> Vs \<Longrightarrow> w \<noteq> t \<Longrightarrow> \<rho> * norm (U t - U w) < Lr r t - Lr r w"
      and small: "norm \<Delta> \<le> \<rho>"
  shows "rdecides (r + \<Delta>) Vs t"
  unfolding rdecides_def
proof (intro ballI impI)
  fix w assume w: "w \<in> Vs" "w \<noteq> t"
  have cs: "\<bar>inner \<Delta> (U t - U w)\<bar> \<le> norm \<Delta> * norm (U t - U w)"
    by (rule Cauchy_Schwarz_ineq2)
  have lo: "- \<bar>inner \<Delta> (U t - U w)\<bar> \<le> inner \<Delta> (U t - U w)" by simp
  have "norm \<Delta> * norm (U t - U w) \<le> \<rho> * norm (U t - U w)"
    using small by (simp add: mult_right_mono)
  hence "0 < (Lr r t - Lr r w) + inner \<Delta> (U t - U w)" using cs lo marg[OF w] by linarith
  thus "Lr (r + \<Delta>) w < Lr (r + \<Delta>) t" using Lr_shift[of r \<Delta> t w] by linarith
qed

text \<open>Tight: if some rival's margin is at most @{term "\<rho> * norm (U t - U w)"}, a perturbation of norm
  @{term \<rho>} along @{term "-(U t - U w)"} removes the strict win.\<close>
theorem gram_radius_tight:
  assumes rho: "0 \<le> \<rho>" and w: "w \<in> Vs" "w \<noteq> t"
      and wide: "Lr r t - Lr r w \<le> \<rho> * norm (U t - U w)"
  shows "\<exists>\<Delta>. norm \<Delta> \<le> \<rho> \<and> \<not> rdecides (r + \<Delta>) Vs t"
proof (cases "U t = U w")
  case True
  hence "Lr r t - Lr r w \<le> 0" using wide by simp
  hence "\<not> rdecides (r + 0) Vs t" using w unfolding rdecides_def by auto
  thus ?thesis using rho by (intro exI[of _ 0]) simp
next
  case False
  define n where "n = norm (U t - U w)"
  have n: "0 < n" using False unfolding n_def by simp
  define \<Delta> where "\<Delta> = (- (\<rho> / n)) *\<^sub>R (U t - U w)"
  have nd: "norm \<Delta> = \<rho>"
    using rho n unfolding \<Delta>_def n_def by (simp add: abs_of_nonneg)
  have "inner \<Delta> (U t - U w) = - (\<rho> / n) * (inner (U t - U w) (U t - U w))"
    unfolding \<Delta>_def by simp
  also have "inner (U t - U w) (U t - U w) = n * n"
    unfolding n_def by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
  finally have ip: "inner \<Delta> (U t - U w) = - (\<rho> * n)" using n by simp
  have "Lr (r + \<Delta>) t - Lr (r + \<Delta>) w \<le> 0"
    using Lr_shift[of r \<Delta> t w] ip wide unfolding n_def by linarith
  hence "\<not> rdecides (r + \<Delta>) Vs t" using w unfolding rdecides_def by auto
  thus ?thesis using nd by auto
qed

text \<open>EXACT radius: the decision survives the whole @{term \<rho>}-ball iff every rival's margin exceeds
  @{term \<rho>} times its Gram distance.\<close>
corollary gram_radius_exact:
  assumes rho: "0 \<le> \<rho>"
  shows "(\<forall>\<Delta>. norm \<Delta> \<le> \<rho> \<longrightarrow> rdecides (r + \<Delta>) Vs t)
         \<longleftrightarrow> (\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow> \<rho> * norm (U t - U w) < Lr r t - Lr r w)"
proof
  assume all: "\<forall>\<Delta>. norm \<Delta> \<le> \<rho> \<longrightarrow> rdecides (r + \<Delta>) Vs t"
  show "\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow> \<rho> * norm (U t - U w) < Lr r t - Lr r w"
  proof (intro ballI impI)
    fix w assume w: "w \<in> Vs" "w \<noteq> t"
    show "\<rho> * norm (U t - U w) < Lr r t - Lr r w"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "Lr r t - Lr r w \<le> \<rho> * norm (U t - U w)" by simp
      then obtain \<Delta> where "norm \<Delta> \<le> \<rho>" "\<not> rdecides (r + \<Delta>) Vs t"
        using gram_radius_tight[OF rho w] by blast
      thus False using all by blast
    qed
  qed
next
  assume "\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow> \<rho> * norm (U t - U w) < Lr r t - Lr r w"
  thus "\<forall>\<Delta>. norm \<Delta> \<le> \<rho> \<longrightarrow> rdecides (r + \<Delta>) Vs t"
    using gram_radius_sound by blast
qed

text \<open>Never weaker than the per-token certificate: with @{term K} bounding every frame norm, a margin
  above @{term "2 * \<rho> * K"} already clears the Gram-distance condition (triangle inequality).\<close>
corollary gram_radius_imp_margin_bound:
  assumes K: "\<And>v. v \<in> Vs \<Longrightarrow> norm (U v) \<le> K" and tV: "t \<in> Vs" and rho: "0 \<le> \<rho>"
      and w: "w \<in> Vs" "w \<noteq> t"
      and marg: "2 * \<rho> * K < Lr r t - Lr r w"
  shows "\<rho> * norm (U t - U w) < Lr r t - Lr r w"
proof -
  have "norm (U t - U w) \<le> norm (U t) + norm (U w)" by (rule norm_triangle_ineq4)
  also have "\<dots> \<le> 2 * K" using K[OF tV] K[OF w(1)] by linarith
  finally have "\<rho> * norm (U t - U w) \<le> \<rho> * (2 * K)" using rho by (simp add: mult_left_mono)
  thus ?thesis using marg by linarith
qed

end


section \<open>(b) All coalitions containing a head, without enumeration\<close>

lemma min0_as_filter:
  assumes "finite T"
  shows "(\<Sum>j\<in>T. min 0 (g j)) = (\<Sum>j\<in>{j\<in>T. g j < 0}. g j)"
proof -
  have "(\<Sum>j\<in>T. min 0 (g j)) = (\<Sum>j\<in>T. if g j < 0 then g j else 0)"
    by (rule sum.cong) (auto simp: min_def)
  also have "\<dots> = (\<Sum>j\<in>{j\<in>T. g j < 0}. g j)"
    using assms by (simp add: sum.inter_filter)
  finally show ?thesis .
qed

lemma min0_le_subset_sum:
  assumes T: "finite T" and P: "P \<subseteq> T"
  shows "(\<Sum>j\<in>T. min 0 (g j)) \<le> (\<Sum>j\<in>P. (g j :: real))"
proof -
  have fP: "finite P" using T P by (rule rev_finite_subset)
  have "(\<Sum>j\<in>T. min 0 (g j)) = (\<Sum>j\<in>T - P. min 0 (g j)) + (\<Sum>j\<in>P. min 0 (g j))"
    using T P by (rule sum.subset_diff)
  also have "(\<Sum>j\<in>T - P. min 0 (g j)) \<le> 0" by (rule sum_nonpos) simp
  also have "(\<Sum>j\<in>P. min 0 (g j)) \<le> (\<Sum>j\<in>P. g j)" by (rule sum_mono) simp
  finally show ?thesis by simp
qed

lemma min0_le_cube_sum:
  assumes lam: "\<And>j. j \<in> T \<Longrightarrow> 0 \<le> \<lambda> j \<and> \<lambda> j \<le> 1"
  shows "(\<Sum>j\<in>T. min 0 (g j)) \<le> (\<Sum>j\<in>T. \<lambda> j * (g j :: real))"
proof (rule sum_mono)
  fix j assume j: "j \<in> T"
  show "min 0 (g j) \<le> \<lambda> j * g j"
  proof (cases "0 \<le> g j")
    case True thus ?thesis using lam[OF j] by simp
  next
    case False
    have "0 \<le> (\<lambda> j - 1) * g j" using lam[OF j] False by (intro mult_nonpos_nonpos) auto
    thus ?thesis using False by (simp add: algebra_simps)
  qed
qed

text \<open>The exact all-coalitions check on a free contribution table (the turnstile of PIC_Core).\<close>
theorem zonotope_all_coalitions:
  fixes c :: "'s \<Rightarrow> 'v \<Rightarrow> real"
  assumes fH: "finite H" and fT: "finite T" and disj: "H \<inter> T = {}"
  shows "(\<forall>P\<subseteq>T. pdecides c (H \<union> P) Vs t)
         \<longleftrightarrow> (\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow>
                0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>T. min 0 (c j t - c j w)))"
proof -
  have split: "(\<Sum>j\<in>H \<union> P. c j t) - (\<Sum>j\<in>H \<union> P. c j w)
               = (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>P. c j t - c j w)" if P: "P \<subseteq> T" for P w
  proof -
    have fP: "finite P" using fT P by (rule rev_finite_subset)
    have dj: "H \<inter> P = {}" using disj P by blast
    show ?thesis using fH fP dj by (simp add: sum.union_disjoint sum_subtractf)
  qed
  have dec: "pdecides c (H \<union> P) Vs t \<longleftrightarrow>
             (\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow> 0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>P. c j t - c j w))"
    if P: "P \<subseteq> T" for P
    unfolding pdecides_def using split[OF P] by (smt (verit))
  show ?thesis
  proof
    assume all: "\<forall>P\<subseteq>T. pdecides c (H \<union> P) Vs t"
    show "\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow> 0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>T. min 0 (c j t - c j w))"
    proof (intro ballI impI)
      fix w assume w: "w \<in> Vs" "w \<noteq> t"
      let ?P = "{j\<in>T. c j t - c j w < 0}"
      have "?P \<subseteq> T" by blast
      hence "0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>?P. c j t - c j w)"
        using all dec w by blast
      thus "0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>T. min 0 (c j t - c j w))"
        using min0_as_filter[OF fT, of "\<lambda>j. c j t - c j w"] by simp
    qed
  next
    assume cond: "\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow> 0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>T. min 0 (c j t - c j w))"
    show "\<forall>P\<subseteq>T. pdecides c (H \<union> P) Vs t"
    proof (intro allI impI)
      fix P assume P: "P \<subseteq> T"
      have "\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow> 0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>P. c j t - c j w)"
      proof (intro ballI impI)
        fix w assume "w \<in> Vs" "w \<noteq> t"
        thus "0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>P. c j t - c j w)"
          using cond min0_le_subset_sum[OF fT P, of "\<lambda>j. c j t - c j w"] by fastforce
      qed
      thus "pdecides c (H \<union> P) Vs t" using dec[OF P] by blast
    qed
  qed
qed

text \<open>Fractional ablation: each tail source enters with a weight in [0,1] (a zonotope of residuals).
  The same condition is exact, because the margin is affine in the weights and the cube's corners are
  the Boolean coalitions.\<close>
theorem zonotope_cube:
  fixes c :: "'s \<Rightarrow> 'v \<Rightarrow> real"
  assumes fT: "finite T"
  shows "(\<forall>\<lambda>. (\<forall>j\<in>T. 0 \<le> \<lambda> j \<and> \<lambda> j \<le> 1) \<longrightarrow> (\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow>
            0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>T. \<lambda> j * (c j t - c j w))))
         \<longleftrightarrow> (\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow>
                0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>T. min 0 (c j t - c j w)))"
proof
  assume all: "\<forall>\<lambda>. (\<forall>j\<in>T. 0 \<le> \<lambda> j \<and> \<lambda> j \<le> 1) \<longrightarrow> (\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow>
                 0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>T. \<lambda> j * (c j t - c j w)))"
  show "\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow> 0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>T. min 0 (c j t - c j w))"
  proof (intro ballI impI)
    fix w assume w: "w \<in> Vs" "w \<noteq> t"
    define \<lambda> where "\<lambda> j = (if c j t - c j w < 0 then 1 else (0::real))" for j
    have box: "\<forall>j\<in>T. 0 \<le> \<lambda> j \<and> \<lambda> j \<le> 1" unfolding \<lambda>_def by simp
    have eq: "(\<Sum>j\<in>T. \<lambda> j * (c j t - c j w)) = (\<Sum>j\<in>T. min 0 (c j t - c j w))"
      by (rule sum.cong) (auto simp: \<lambda>_def min_def)
    show "0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>T. min 0 (c j t - c j w))"
      using all box w eq by metis
  qed
next
  assume cond: "\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow> 0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>T. min 0 (c j t - c j w))"
  show "\<forall>\<lambda>. (\<forall>j\<in>T. 0 \<le> \<lambda> j \<and> \<lambda> j \<le> 1) \<longrightarrow> (\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow>
          0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>T. \<lambda> j * (c j t - c j w)))"
  proof (intro allI impI ballI)
    fix \<lambda> w assume box: "\<forall>j\<in>T. 0 \<le> \<lambda> j \<and> \<lambda> j \<le> 1" and w: "w \<in> Vs" "w \<noteq> t"
    have "(\<Sum>j\<in>T. min 0 (c j t - c j w)) \<le> (\<Sum>j\<in>T. \<lambda> j * (c j t - c j w))"
      using box by (intro min0_le_cube_sum) blast
    thus "0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>T. \<lambda> j * (c j t - c j w))"
      using cond w by fastforce
  qed
qed

text \<open>The interval check (each token's tail bounded on its own) implies the exact one: sound, weaker.\<close>
theorem interval_imp_zonotope:
  fixes c :: "'s \<Rightarrow> 'v \<Rightarrow> real"
  assumes "0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>T. min 0 (c j t)) - (\<Sum>j\<in>T. max 0 (c j w))"
  shows "0 < (\<Sum>j\<in>H. c j t - c j w) + (\<Sum>j\<in>T. min 0 (c j t - c j w))"
proof -
  have "(\<Sum>j\<in>T. min 0 (c j t)) - (\<Sum>j\<in>T. max 0 (c j w)) = (\<Sum>j\<in>T. min 0 (c j t) - max 0 (c j w))"
    by (simp add: sum_subtractf)
  also have "\<dots> \<le> (\<Sum>j\<in>T. min 0 (c j t - c j w))"
    by (rule sum_mono) (auto simp: min_def max_def)
  finally show ?thesis using assms by linarith
qed

text \<open>In the PIC vocabulary: the head's coalition margin plus the tail's negative pairwise incidences.\<close>
theorem (in pic) all_coalitions_certified:
  assumes "finite H" "finite T" "H \<inter> T = {}"
  shows "(\<forall>P\<subseteq>T. decides (H \<union> P) Vs t)
         \<longleftrightarrow> (\<forall>w\<in>Vs. w \<noteq> t \<longrightarrow>
                0 < (Lc H t - Lc H w) + (\<Sum>j\<in>T. min 0 (incid j t - incid j w)))"
  using zonotope_all_coalitions[OF assms, of incid Vs t]
  unfolding decides_eq_pdecides Lc_def by (simp add: sum_subtractf)

end
