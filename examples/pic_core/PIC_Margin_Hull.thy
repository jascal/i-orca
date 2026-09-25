(*
  PIC_Margin_Hull.thy -- the OPTIMAL decode margin is the distance to the rivals' convex hull.

  PIC_Interference pins the MATCHED-FILTER margin (steer by the target itself) and leaves the OPTIMAL margin
  (the best unit-norm residual) open. This theory computes the optimal margin exactly for a bias-free frame:

    hull_margin_upper    : no unit residual beats the hull distance -- for every r with |r| <= 1 some rival v
                           has <r, U t - U v> <= infdist (U t) (convex hull (U ` C));
    hull_margin_attained : the direction from the closest hull point to U t attains it -- one unit r beats every
                           rival by at least the hull distance (the separating-hyperplane half);
    optimal_margin_hull  : the two together:  Sup_{|r|<=1} Min_{v in C} <r, U t - U v>
                                              = infdist (U t) (convex hull (U ` C)).
  Corollaries:
    gdecodable_iff_hull_dist : (PIC_Core link) with zero biases, t is gamma-decodable iff its distance to the
                               convex hull of every other token is >= gamma;
    hull_dist_le_pair        : the hull distance is at most the distance to any single rival;
    hull_dist_ge_coherence   : for a unit target, the hull distance is >= 1 - (largest <U t, U v>), so the
                               OPTIMAL margin is never below the matched-filter one;
    optimal_margin_coherence_sandwich : for a unit-norm frame, with mu = the largest cross inner product of t,
                               1 - mu  <=  optimal margin  <=  sqrt (2 - 2 mu).

  HONEST SCOPE. Bias-free (b = 0) and a finite rival set. The sandwich bounds the optimal margin by the SIGNED
  cross-coherence of t: a large NEGATIVE inner product costs nothing. So Welch's bound on |coherence| does not by
  itself force any named token's optimal margin down; turning the Welch regime into a margin bound needs a bound
  on the signed coherence and stays OPEN.

  Self-contained over PIC_Core (+ HOL-Analysis); 0 sorry, quick_and_dirty = false.
*)
theory PIC_Margin_Hull
  imports PIC_Core
begin

section \<open>The hull distance\<close>

context
  fixes U :: "'v \<Rightarrow> 'a::euclidean_space" and t :: 'v and C :: "'v set"
  assumes finC: "finite C" and neC: "C \<noteq> {}"
begin

abbreviation Hull :: "'a set" where "Hull \<equiv> convex hull (U ` C)"

abbreviation hdist :: real where "hdist \<equiv> infdist (U t) Hull"

lemma H_compact: "compact Hull"
  using finC by (simp add: finite_imp_compact_convex_hull)

lemma H_nonempty: "Hull \<noteq> {}"
  using neC by simp

lemma closest: obtains p where "p \<in> Hull" "hdist = dist (U t) p" "\<And>y. y \<in> Hull \<Longrightarrow> dist (U t) p \<le> dist (U t) y"
proof -
  obtain p where p: "p \<in> Hull" "hdist = dist (U t) p"
    using infdist_attains_inf[OF compact_imp_closed[OF H_compact] H_nonempty] by blast
  have "\<And>y. y \<in> Hull \<Longrightarrow> dist (U t) p \<le> dist (U t) y"
    using p(2) infdist_le by metis
  with p that show ?thesis by blast
qed

text \<open>A point of the hull of a finite set is a convex combination of its points.\<close>
lemma hull_combination:
  assumes "y \<in> Hull"
  obtains u where "\<forall>x\<in>U ` C. 0 \<le> u x" "sum u (U ` C) = 1" "(\<Sum>x\<in>U ` C. u x *\<^sub>R x) = y"
  using assms finC by (auto simp: convex_hull_finite)

text \<open>If every point of a finite set scores above \<open>c\<close> under a linear functional, so does every convex
  combination; contrapositively some point scores at most the combination's score.\<close>
lemma combination_le:
  fixes f :: "'a \<Rightarrow> real"
  assumes lin: "\<And>x y. f (x + y) = f x + f y" "\<And>a x. f (a *\<^sub>R x) = a * f x"
      and u: "\<forall>x\<in>U ` C. 0 \<le> u x" "sum u (U ` C) = 1"
  shows "\<exists>x\<in>U ` C. f x \<le> f (\<Sum>x\<in>U ` C. u x *\<^sub>R x)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence gt: "\<forall>x\<in>U ` C. f (\<Sum>x\<in>U ` C. u x *\<^sub>R x) < f x" by (auto simp: not_le)
  have fin: "finite (U ` C)" using finC by simp
  have fsum: "f (\<Sum>x\<in>U ` C. u x *\<^sub>R x) = (\<Sum>x\<in>U ` C. u x * f x)"
  proof -
    have add0: "f 0 = 0" using lin(2)[of 0 0] by simp
    show ?thesis using fin
      by (induct rule: finite_induct) (simp_all add: add0 lin)
  qed
  define m where "m = f (\<Sum>x\<in>U ` C. u x *\<^sub>R x)"
  obtain x0 where x0: "x0 \<in> U ` C" "0 < u x0"
  proof -
    have "\<exists>x\<in>U ` C. 0 < u x"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "\<forall>x\<in>U ` C. u x = 0" using u(1) by force
      hence "sum u (U ` C) = 0" by (rule sum.neutral)
      thus False using u(2) by simp
    qed
    thus ?thesis using that by blast
  qed
  have "(\<Sum>x\<in>U ` C. u x * m) < (\<Sum>x\<in>U ` C. u x * f x)"
  proof (rule sum_strict_mono_ex1[OF fin])
    show "\<forall>x\<in>U ` C. u x * m \<le> u x * f x"
      using gt u(1) m_def by (simp add: mult_left_mono less_imp_le)
    show "\<exists>x\<in>U ` C. u x * m < u x * f x"
      using x0 gt m_def by (intro bexI[of _ x0]) auto
  qed
  moreover have "(\<Sum>x\<in>U ` C. u x * m) = m" using u(2) by (simp add: sum_distrib_right[symmetric])
  ultimately show False using fsum m_def by simp
qed

section \<open>The two halves\<close>

theorem hull_margin_upper:
  assumes r: "norm r \<le> 1"
  shows "\<exists>v\<in>C. inner r (U t - U v) \<le> hdist"
proof -
  obtain p where p: "p \<in> Hull" "hdist = dist (U t) p" using closest by blast
  obtain u where u: "\<forall>x\<in>U ` C. 0 \<le> u x" "sum u (U ` C) = 1" "(\<Sum>x\<in>U ` C. u x *\<^sub>R x) = p"
    by (rule hull_combination[OF p(1)])
  define f where "f x = inner r (U t) - inner r x" for x
  have "\<exists>x\<in>U ` C. (- inner r x) \<le> (- inner r (\<Sum>x\<in>U ` C. u x *\<^sub>R x))"
    by (rule combination_le) (auto simp: inner_add_right u)
  then obtain v where v: "v \<in> C" "- inner r (U v) \<le> - inner r p" using u(3) by auto
  have "inner r (U t - U v) \<le> inner r (U t - p)" using v(2) by (simp add: inner_diff_right)
  also have "\<dots> \<le> norm r * norm (U t - p)" by (rule norm_cauchy_schwarz)
  also have "\<dots> \<le> norm (U t - p)" using r by (simp add: mult_left_le_one_le)
  also have "\<dots> = hdist" using p(2) by (simp add: dist_norm)
  finally show ?thesis using v(1) by blast
qed

theorem hull_margin_attained:
  "\<exists>r. norm r \<le> 1 \<and> (\<forall>v\<in>C. hdist \<le> inner r (U t - U v))"
proof -
  obtain p where p: "p \<in> Hull" "hdist = dist (U t) p" "\<And>y. y \<in> Hull \<Longrightarrow> dist (U t) p \<le> dist (U t) y"
    using closest by blast
  show ?thesis
  proof (cases "hdist = 0")
    case True
    thus ?thesis by (intro exI[of _ 0]) simp
  next
    case False
    have pos: "0 < hdist" using False infdist_nonneg[of "U t" Hull] by linarith
    define r where "r = (1 / hdist) *\<^sub>R (U t - p)"
    have nr: "norm r = 1"
      using pos p(2) by (simp add: r_def dist_norm)
    have "\<forall>v\<in>C. hdist \<le> inner r (U t - U v)"
    proof
      fix v assume v: "v \<in> C"
      have yH: "U v \<in> Hull" using v by (simp add: hull_inc)
      have obtuse: "inner (U t - p) (U v - p) \<le> 0"
        by (rule any_closest_point_dot[OF convex_convex_hull compact_imp_closed[OF H_compact] p(1) yH])
           (use p(3) in auto)
      have "inner (U t - p) (U t - U v) = inner (U t - p) (U t - p) - inner (U t - p) (U v - p)"
        by (simp add: inner_diff_right)
      hence "hdist * hdist \<le> inner (U t - p) (U t - U v)"
        using obtuse p(2) by (simp add: dist_norm power2_norm_eq_inner[symmetric] power2_eq_square)
      hence "hdist \<le> (1 / hdist) * inner (U t - p) (U t - U v)"
        using pos by (simp add: field_simps)
      thus "hdist \<le> inner r (U t - U v)" by (simp add: r_def)
    qed
    with nr show ?thesis by (intro exI[of _ r]) simp
  qed
qed

text \<open>The optimal (best unit-residual) worst-rival margin, and the headline identity.\<close>
definition optmargin :: real where
  "optmargin = Sup ((\<lambda>r. Min ((\<lambda>v. inner r (U t - U v)) ` C)) ` {r. norm r \<le> 1})"

theorem optimal_margin_hull: "optmargin = hdist"
proof -
  let ?m = "\<lambda>r. Min ((\<lambda>v. inner r (U t - U v)) ` C)"
  have fin: "finite ((\<lambda>v. inner r (U t - U v)) ` C)" for r using finC by simp
  have ne: "(\<lambda>v. inner r (U t - U v)) ` C \<noteq> {}" for r using neC by simp
  have le: "?m r \<le> hdist" if nr: "norm r \<le> 1" for r
  proof -
    obtain v where "v \<in> C" "inner r (U t - U v) \<le> hdist" using hull_margin_upper[OF nr] by blast
    thus ?thesis using Min_le[OF fin] by (meson dual_order.trans image_eqI)
  qed
  obtain r0 where r0: "norm r0 \<le> 1" "\<forall>v\<in>C. hdist \<le> inner r0 (U t - U v)"
    using hull_margin_attained by blast
  have "hdist \<le> ?m r0" using r0(2) by (simp add: Min_ge_iff[OF fin ne])
  hence eq: "?m r0 = hdist" using le[OF r0(1)] by simp
  show ?thesis unfolding optmargin_def
  proof (rule cSup_eq_maximum)
    show "hdist \<in> ?m ` {r. norm r \<le> 1}"
      by (rule image_eqI[of _ _ r0]) (use eq r0(1) in auto)
  next
    fix x assume "x \<in> ?m ` {r. norm r \<le> 1}"
    thus "x \<le> hdist" using le by auto
  qed
qed

section \<open>Corollaries: pairs, coherence\<close>

corollary hull_dist_le_pair:
  assumes "v \<in> C" shows "hdist \<le> dist (U t) (U v)"
  using assms by (intro infdist_le) (simp add: hull_inc)

corollary hull_dist_ge_coherence:
  assumes unit: "norm (U t) = 1"
  shows "1 - Max ((\<lambda>v. inner (U t) (U v)) ` C) \<le> hdist"
proof -
  obtain p where p: "p \<in> Hull" "hdist = dist (U t) p" using closest by blast
  obtain u where u: "\<forall>x\<in>U ` C. 0 \<le> u x" "sum u (U ` C) = 1" "(\<Sum>x\<in>U ` C. u x *\<^sub>R x) = p"
    by (rule hull_combination[OF p(1)])
  have "\<exists>x\<in>U ` C. (- inner (U t) x) \<le> (- inner (U t) (\<Sum>x\<in>U ` C. u x *\<^sub>R x))"
    by (rule combination_le) (auto simp: inner_add_right u)
  then obtain v where v: "v \<in> C" "inner (U t) p \<le> inner (U t) (U v)" using u(3) by auto
  have fin: "finite ((\<lambda>v. inner (U t) (U v)) ` C)" using finC by simp
  have "inner (U t) (U v) \<le> Max ((\<lambda>v. inner (U t) (U v)) ` C)" using v(1) fin by simp
  hence "1 - Max ((\<lambda>v. inner (U t) (U v)) ` C) \<le> inner (U t) (U t - p)"
    using v(2) unit by (simp add: inner_diff_right power2_norm_eq_inner[symmetric])
  also have "\<dots> \<le> norm (U t) * norm (U t - p)" by (rule norm_cauchy_schwarz)
  also have "\<dots> = hdist" using unit p(2) by (simp add: dist_norm)
  finally show ?thesis .
qed

corollary optimal_margin_coherence_sandwich:
  assumes unit: "\<forall>v\<in>insert t C. norm (U v) = 1"
  defines "mu \<equiv> Max ((\<lambda>v. inner (U t) (U v)) ` C)"
  shows "1 - mu \<le> optmargin" and "optmargin \<le> sqrt (2 - 2 * mu)"
proof -
  show "1 - mu \<le> optmargin"
    using hull_dist_ge_coherence unit optimal_margin_hull by (simp add: mu_def)
  have fin: "finite ((\<lambda>v. inner (U t) (U v)) ` C)" using finC by simp
  have "mu \<in> (\<lambda>v. inner (U t) (U v)) ` C" using Max_in[OF fin] neC by (simp add: mu_def)
  then obtain v where v: "v \<in> C" "inner (U t) (U v) = mu" by blast
  have one: "inner (U t) (U t) = 1" "inner (U v) (U v) = 1"
    using unit v(1) by (simp_all add: norm_eq_1)
  have "(dist (U t) (U v))\<^sup>2 = 2 - 2 * mu"
    using one v(2) by (simp add: dist_norm power2_norm_eq_inner inner_diff_left inner_diff_right inner_commute)
  hence "dist (U t) (U v) = sqrt (2 - 2 * mu)" by (simp add: real_sqrt_unique)
  thus "optmargin \<le> sqrt (2 - 2 * mu)"
    using hull_dist_le_pair[OF v(1)] optimal_margin_hull by simp
qed

end \<comment> \<open>context\<close>

section \<open>Link to PIC_Core: gamma-decodability is hull distance\<close>

theorem gdecodable_iff_hull_dist:
  fixes U :: "'v \<Rightarrow> 'a::euclidean_space"
  assumes fin: "finite (UNIV :: 'v set)" and other: "\<exists>w. w \<noteq> v" and zero: "\<forall>w. b w = 0"
  shows "v \<in> pic_frame.gdecodable U b \<gamma>
         \<longleftrightarrow> \<gamma> \<le> infdist (U v) (convex hull (U ` (- {v})))"
proof -
  have finC: "finite (- {v})" using fin by simp
  have neC: "- {v} \<noteq> ({} :: 'v set)" using other by auto
  have dec: "pic_frame.gdecodes U b \<gamma> v r \<longleftrightarrow> (\<forall>w\<in>- {v}. \<gamma> \<le> inner r (U v - U w))" for r
  proof -
    have "pic_frame.gdecodes U b \<gamma> v r \<longleftrightarrow> (\<forall>w. w \<noteq> v \<longrightarrow> inner r (U w) + \<gamma> \<le> inner r (U v))"
      using zero by (simp add: pic_frame.gdecodes_def)
    also have "\<dots> \<longleftrightarrow> (\<forall>w\<in>- {v}. \<gamma> \<le> inner r (U v - U w))"
      by (auto simp: inner_diff_right le_diff_eq add.commute)
    finally show ?thesis .
  qed
  show ?thesis
  proof
    assume "v \<in> pic_frame.gdecodable U b \<gamma>"
    then obtain r where r: "norm r \<le> 1" "\<forall>w\<in>- {v}. \<gamma> \<le> inner r (U v - U w)"
      by (auto simp: pic_frame.gdecodable_def dec)
    obtain w where "w \<in> - {v}" "inner r (U v - U w) \<le> infdist (U v) (convex hull (U ` (- {v})))"
      using hull_margin_upper[OF finC neC r(1)] by blast
    thus "\<gamma> \<le> infdist (U v) (convex hull (U ` (- {v})))" using r(2) by force
  next
    assume g: "\<gamma> \<le> infdist (U v) (convex hull (U ` (- {v})))"
    obtain r where r: "norm r \<le> 1" "\<forall>w\<in>- {v}. infdist (U v) (convex hull (U ` (- {v}))) \<le> inner r (U v - U w)"
      using hull_margin_attained[OF finC neC] by blast
    hence "\<forall>w\<in>- {v}. \<gamma> \<le> inner r (U v - U w)" using g by force
    thus "v \<in> pic_frame.gdecodable U b \<gamma>" using r(1) by (auto simp: pic_frame.gdecodable_def dec)
  qed
qed

end
