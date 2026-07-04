(*
  Gauge.thy -- C6: gauge reduction under grounding (the identifiability free-lunch).

  Concept directions recovered from decisions alone are identifiable only up to a CONTINUOUS gauge:
  any orthogonal transformation applied to residuals and directions together preserves every
  membership and every argmax decode -- and for DIM >= 2 there are infinitely many such
  transformations (an explicit Householder-reflection family, kernel-checked). Grounding adds the
  readout frame U_out: concept directions must stay aligned to a KNOWN spanning frame, and the
  gauge collapses:

    * ungrounded_gauge_membership / ungrounded_gauge_decoder : every R in O(d) preserves all
      memberships and decodes -- the O(d) gauge freedom;
    * ungrounded_gauge_infinite : that gauge group is INFINITE when DIM >= 2 (Householder
      reflections along the unit vectors (i + t j)/|i + t j|, injectively parametrized by t >= 0);
    * alignment_kills_gauge : an orthogonal R that fixes a spanning readout frame pointwise is the
      identity -- exact grounding leaves NO gauge freedom (generic case: trivial stabilizer);
    * sign_gauge_involutive / sign_gauge_finite : if alignment only pins each frame direction up to
      sign, the residual gauge maps are involutions and there are FINITELY many of them (at most
      2^d, versus the infinite ungrounded group).

  So grounding collapses the continuous O(d) gauge to a finite (generically trivial) one -- the
  frame/generator duality's identifiability statement. Domain: exact alignment to a stated frame;
  "distinct singular directions => the sign symmetries also die except identity" is the generic
  strengthening, represented here by the exact-fix case; the bridge to any estimator on real
  models stays `open`.
*)
theory Gauge
  imports ConceptCells Consolidation
begin

subsection \<open>The ungrounded gauge: all of O(d) preserves the decisions\<close>

text \<open>Rotating residuals and concept directions together preserves every membership.\<close>
theorem ungrounded_gauge_membership:
  assumes "orthogonal_transformation R"
  shows "fires (\<lambda>c. R (u c)) b c (R r) = fires u b c r"
  using assms unfolding fires_def orthogonal_transformation_def by simp

text \<open>... and every argmax decode: decisions cannot see the gauge.\<close>
theorem ungrounded_gauge_decoder:
  assumes "orthogonal_transformation R"
  shows "amax V (\<lambda>v. R (U v)) (R r) = amax V U r"
  using assms unfolding amax_def orthogonal_transformation_def by simp

subsection \<open>The Householder family: the ungrounded gauge group is infinite (DIM >= 2)\<close>

text \<open>Reflection along a direction n.\<close>
definition hreflect :: "'a::real_inner \<Rightarrow> 'a \<Rightarrow> 'a" where
  "hreflect n x = x - (2 * (x \<bullet> n)) *\<^sub>R n"

lemma hreflect_linear: "linear (hreflect n)"
  unfolding hreflect_def
  by (intro linearI) (simp_all add: inner_add_left inner_scaleR_left algebra_simps)

lemma hreflect_orthogonal:
  assumes n: "n \<bullet> n = 1"
  shows "orthogonal_transformation (hreflect n)"
  unfolding orthogonal_transformation_def
proof (intro conjI allI)
  show "linear (hreflect n)" by (rule hreflect_linear)
next
  fix v w
  show "hreflect n v \<bullet> hreflect n w = v \<bullet> w"
    unfolding hreflect_def
    by (simp add: inner_diff_left inner_diff_right inner_scaleR_left inner_scaleR_right n
                  inner_commute algebra_simps)
qed

text \<open>An explicit infinite family inside O(d) for DIM >= 2: reflections along the unit vectors in
      the (i, j)-plane, distinguished by their action on i. The ungrounded gauge group is infinite.\<close>
theorem ungrounded_gauge_infinite:
  assumes dim2: "2 \<le> DIM('a::euclidean_space)"
  shows "infinite {R::'a \<Rightarrow> 'a. orthogonal_transformation R}"
proof -
  have "\<not> (\<forall>x\<in>Basis. \<forall>y\<in>(Basis::'a set). x = y)"
  proof
    assume "\<forall>x\<in>Basis. \<forall>y\<in>(Basis::'a set). x = y"
    hence "card (Basis::'a set) \<le> Suc 0"
      using finite_Basis by (simp add: card_le_Suc0_iff_eq)
    thus False using dim2 by simp
  qed
  then obtain i j :: 'a where iB: "i \<in> Basis" and jB: "j \<in> Basis" and ij: "i \<noteq> j" by auto
  have ii: "i \<bullet> i = 1" and jj: "j \<bullet> j = 1" and ij0: "i \<bullet> j = 0" and ji0: "j \<bullet> i = 0"
    using iB jB ij by (auto simp: inner_Basis)
  define u :: "real \<Rightarrow> 'a" where "u t = (1 / sqrt (1 + t\<^sup>2)) *\<^sub>R (i + t *\<^sub>R j)" for t
  have pos: "0 < 1 + t\<^sup>2" for t :: real
    using zero_le_power2[of t] by linarith
  have vv: "(i + t *\<^sub>R j) \<bullet> (i + t *\<^sub>R j) = 1 + t\<^sup>2" for t
    by (simp add: inner_add_left inner_add_right inner_scaleR_left inner_scaleR_right
                  ii jj ij0 ji0 power2_eq_square)
  have sq: "(1 / sqrt (1 + t\<^sup>2))\<^sup>2 = 1 / (1 + t\<^sup>2)" for t :: real
    using pos[of t] by (simp add: power_one_over)
  have unit: "u t \<bullet> u t = 1" for t
  proof -
    have "u t \<bullet> u t = (1 / sqrt (1 + t\<^sup>2))\<^sup>2 * ((i + t *\<^sub>R j) \<bullet> (i + t *\<^sub>R j))"
      unfolding u_def by (simp add: inner_scaleR_left inner_scaleR_right power2_eq_square
                                    mult.assoc)
    also have "\<dots> = (1 / (1 + t\<^sup>2)) * (1 + t\<^sup>2)" by (simp add: sq vv)
    also have "\<dots> = 1" using pos[of t] by simp
    finally show ?thesis .
  qed
  have iu: "i \<bullet> u t = 1 / sqrt (1 + t\<^sup>2)" for t
    unfolding u_def
    by (simp add: inner_add_right inner_scaleR_right ii ij0)
  have func: "hreflect (u t) i \<bullet> i = 1 - 2 / (1 + t\<^sup>2)" for t
  proof -
    have "hreflect (u t) i \<bullet> i = i \<bullet> i - 2 * (i \<bullet> u t) * (u t \<bullet> i)"
      unfolding hreflect_def by (simp add: inner_diff_left inner_scaleR_left)
    also have "\<dots> = 1 - 2 * (i \<bullet> u t)\<^sup>2"
      by (simp add: ii inner_commute power2_eq_square)
    also have "\<dots> = 1 - 2 * (1 / (1 + t\<^sup>2))" by (simp add: iu sq flip: power_divide)
    finally show ?thesis by simp
  qed
  have injf: "inj_on (\<lambda>t. hreflect (u t)) {0::real..}"
  proof (rule inj_onI)
    fix t s :: real assume t: "t \<in> {0..}" and s: "s \<in> {0..}"
      and eq: "hreflect (u t) = hreflect (u s)"
    have "hreflect (u t) i \<bullet> i = hreflect (u s) i \<bullet> i" using eq by simp
    hence "1 - 2 / (1 + t\<^sup>2) = 1 - 2 / (1 + s\<^sup>2)" using func by simp
    hence "1 + t\<^sup>2 = 1 + s\<^sup>2" using pos[of t] pos[of s] by (simp add: field_simps)
    hence "t\<^sup>2 = s\<^sup>2" by simp
    then consider "t = s" | "t = - s" using power2_eq_iff by blast
    thus "t = s"
    proof cases
      case 1 thus ?thesis .
    next
      case 2
      have "0 \<le> t" and "0 \<le> s" using t s by auto
      with 2 have "t = 0" and "s = 0" by linarith+
      thus ?thesis by simp
    qed
  qed
  have sub: "(\<lambda>t. hreflect (u t)) ` {0::real..} \<subseteq> {R::'a \<Rightarrow> 'a. orthogonal_transformation R}"
    using hreflect_orthogonal unit by auto
  have "infinite ((\<lambda>t. hreflect (u t)) ` {0::real..})"
    using injf infinite_Ici by (metis finite_imageD)
  thus ?thesis using sub by (rule infinite_super[rotated])
qed

subsection \<open>Grounding: alignment to a spanning frame kills the gauge\<close>

text \<open>Two linear maps agreeing on a spanning set are equal -- the workhorse.\<close>
lemma linear_eq_UNIV:
  assumes lf: "linear f" and lg: "linear g"
      and agree: "\<And>v. v \<in> B \<Longrightarrow> f v = g v"
      and sp: "span B = UNIV"
  shows "f = g"
proof
  fix x :: 'a
  have "x \<in> span B" using sp by simp
  thus "f x = g x" using linear_eq_on_span[OF lf lg] agree by blast
qed

text \<open>Exact grounding: an orthogonal residual gauge that fixes every vector of a spanning readout
      frame pointwise is the identity. Decisions + alignment to a generic (spanning, exactly
      pinned) frame leave NO gauge freedom at all.\<close>
theorem alignment_kills_gauge:
  fixes Uout :: "'v \<Rightarrow> 'a::euclidean_space"
  assumes orth: "orthogonal_transformation R"
      and fixes_frame: "\<And>v. v \<in> V \<Longrightarrow> R (Uout v) = Uout v"
      and sp: "span (Uout ` V) = UNIV"
  shows "R = id"
proof (rule linear_eq_UNIV[OF orthogonal_transformation_linear[OF orth] _ _ sp])
  show "linear id" by (rule linear_id)
  show "\<And>w. w \<in> Uout ` V \<Longrightarrow> R w = id w" using fixes_frame by auto
qed

subsection \<open>Sign alignment: the residual gauge collapses to a finite group\<close>

text \<open>If alignment pins each frame direction only up to sign, every consistent gauge is an
      involution: applying it twice restores every residual.\<close>
theorem sign_gauge_involutive:
  assumes lin: "linear R"
      and sgn: "\<And>v. v \<in> B \<Longrightarrow> R v = v \<or> R v = - v"
      and sp: "span B = (UNIV :: 'a::euclidean_space set)"
  shows "R \<circ> R = id"
proof (rule linear_eq_UNIV[OF _ _ _ sp])
  show "linear (R \<circ> R)" by (intro linear_compose lin)
  show "linear id" by (rule linear_id)
  fix v assume "v \<in> B"
  thus "(R \<circ> R) v = id v" using sgn[of v] lin by (auto simp: linear_neg)
qed

text \<open>And there are only finitely many such gauges: a linear map sending each basis direction to
      itself or its negation is determined by those <= 2^d sign choices. Versus the INFINITE
      ungrounded group: grounding collapses a continuous gauge to a finite one.\<close>
theorem sign_gauge_finite:
  shows "finite {R::'a::euclidean_space \<Rightarrow> 'a. linear R \<and> (\<forall>v\<in>Basis. R v = v \<or> R v = - v)}"
proof -
  let ?G = "{R::'a \<Rightarrow> 'a. linear R \<and> (\<forall>v\<in>Basis. R v = v \<or> R v = - v)}"
  have inj: "inj_on (\<lambda>R. restrict R Basis) ?G"
  proof (rule inj_onI)
    fix R R' assume R: "R \<in> ?G" and R': "R' \<in> ?G"
      and eq: "restrict R Basis = restrict R' Basis"
    have "R v = R' v" if "v \<in> Basis" for v
      using fun_cong[OF eq, of v] that by (simp add: restrict_def)
    thus "R = R'"
      using R R' by (intro linear_eq_UNIV[OF _ _ _ span_Basis]) auto
  qed
  have sub: "(\<lambda>R. restrict R Basis) ` ?G \<subseteq> (\<Pi>\<^sub>E v\<in>(Basis::'a set). {v, - v})"
    by (auto simp: PiE_iff extensional_def restrict_def)
  have "finite (\<Pi>\<^sub>E v\<in>(Basis::'a set). {v, - v})"
    by (intro finite_PiE finite_Basis) simp
  hence "finite ((\<lambda>R. restrict R Basis) ` ?G)" using sub by (rule rev_finite_subset)
  thus ?thesis using inj by (rule finite_imageD)
qed

end
