(*
  PIC_Binding.thy -- tensor-product binding in PIC (examples/pic_binding/PROPOSAL.md, T1/T2/T3/T5(a)).

  Fillers f a and roles r s are bound by the concrete tensor product  tprod f r = (chi i. f$i *R r)  in
  real^'m^'n, so that  <f (x) r, g (x) s> = <f,g> <r,s>  is a LEMMA (inner_tprod), not an assumption.

    T1  tensor_coherence             : |A|,|S| >= 2, unit frames  ==>  mu(F (x) R) = max mu_F mu_R  (absolute);
        tensor_signed_coherence      : the SIGNED coherence of a bound pair (a,s) is the max of the filler's
                                       signed coherence, the role's, and the both-differ products -- the last
                                       can be positive when both signed coherences are negative;
        tensor_optimal_margin        : (corollary, via optimal_margin_coherence_sandwich) the optimal decode
                                       margin of a bound pair is >= 1 - that signed coherence.
    T2  tensor_frame_potential       : DIAGONAL-INCLUSIVE frame potential FP X = sum_{i,j} <x_i,x_j>^2 is
                                       multiplicative, FP(F (x) R) = FP F * FP R;
        tensor_welch_value / tensor_fp_welch_ratio : the Welch value card^2/dim and the FP/Welch ratio are
                                       multiplicative too.  The off-diagonal normalised form pil reports
                                       (geometry.frame_potential / welch_bound) is NOT covered and does not factor.
    T3  unbind_certified             : matched-filter unbinding decodes the filler of role s whenever
                                       1 - <f(sigma s), f b> > 2 (k-1) mu_R for every rival b.  The factor 2
                                       enters ONCE, from decode_margin_certified, with delta = (k-1) mu_R the
                                       PER-SCORE crosstalk bound.
    T5a substitution_certified       : replacing the decode input r by r_hat preserves the argmax t whenever
                                       margin(t) > 2 delta with delta >= max_v |<r - r_hat, U v>|;
        substitution_certified_max   : the same with delta = that max over a finite V (the stated form);
        substitution_certified_norm  : the Cauchy-Schwarz form  delta = |r - r_hat| * u_max.

    T5b substitution_domain_norm     : ONE fit-error bound eps on a whole domain D of contexts, with every margin
                                       > 2 eps u_max, certifies every context in D (evaluated or not);
        substitution_domain_pairwise : the per-rival domain form, margin over v > eps * |U t - U v|;
        domain_norm_implies_pairwise : the per-rival threshold never exceeds the norm one.
    T5c certificate_hull_ceiling     : bias-free; a certificate needing every margin > m fires only if
                                       m < |r| * infdist (U t) (conv hull rivals) -- a ceiling set by the frame and
                                       |r|, independent of the substitute;
        substitution_hull_ceiling    : the uniform instance, m = 2 delta.

  HONEST SCOPE. Decode-input (post-norm) substitution only: the pre-norm Lipschitz step, T2's frame-operator
  tightness (claim 4), T4 and T6 stay OPEN. T5(b) certifies D only GIVEN the error bound on all of D; bounding
  the fit error off the evaluated contexts is not supplied here. T5(c) is bias-free. Nothing here says any model is TPR-shaped.
  Self-contained over PIC_Logic + PIC_Margin_Hull (+ HOL-Analysis); 0 sorry, quick_and_dirty = false.
*)
theory PIC_Binding
  imports PIC_Logic PIC_Margin_Hull
begin

section \<open>The tensor product of two vectors\<close>

definition tprod :: "real^'n \<Rightarrow> real^'m \<Rightarrow> real^'m^'n" where
  "tprod f r = (\<chi> i. f$i *\<^sub>R r)"

lemma inner_tprod: "inner (tprod f r) (tprod g s) = inner f g * inner r s"
proof -
  have fg: "inner f g = (\<Sum>i\<in>UNIV. f$i * g$i)" by (simp add: inner_vec_def)
  have "inner (tprod f r) (tprod g s) = (\<Sum>i\<in>UNIV. inner (f$i *\<^sub>R r) (g$i *\<^sub>R s))"
    by (subst inner_vec_def) (simp add: tprod_def)
  also have "\<dots> = (\<Sum>i\<in>UNIV. (f$i * g$i) * inner r s)" by (simp add: mult_ac)
  also have "\<dots> = (\<Sum>i\<in>UNIV. f$i * g$i) * inner r s" by (simp add: sum_distrib_right)
  finally show ?thesis using fg by simp
qed

lemma norm_tprod: "norm (tprod f r) = norm f * norm r"
  by (simp add: norm_eq_sqrt_inner inner_tprod real_sqrt_mult)

lemma unit_inner_abs_le1:
  fixes x y :: "'a::real_inner"
  assumes "norm x = 1" "norm y = 1"
  shows "\<bar>inner x y\<bar> \<le> 1"
  using Cauchy_Schwarz_ineq2[of x y] assms by simp

section \<open>T1 -- coherence of a bound frame\<close>

definition offd :: "'i set \<Rightarrow> ('i \<times> 'i) set" where
  "offd I = {p \<in> I \<times> I. fst p \<noteq> snd p}"

definition coh :: "('i \<Rightarrow> 'a::real_inner) \<Rightarrow> 'i set \<Rightarrow> real" where
  "coh x I = Max ((\<lambda>p. \<bar>inner (x (fst p)) (x (snd p))\<bar>) ` offd I)"

definition bound :: "('a \<Rightarrow> real^'n) \<Rightarrow> ('s \<Rightarrow> real^'m) \<Rightarrow> 'a \<times> 's \<Rightarrow> real^'m^'n" where
  "bound f r = (\<lambda>(a, s). tprod (f a) (r s))"

lemma bound_inner: "inner (bound f r (a, s)) (bound f r (b, t)) = inner (f a) (f b) * inner (r s) (r t)"
  by (simp add: bound_def inner_tprod)

lemma bound_inner':
  "inner (bound f r i) (bound f r j) = inner (f (fst i)) (f (fst j)) * inner (r (snd i)) (r (snd j))"
  by (cases i, cases j) (simp add: bound_inner)

lemma offd_finite: "finite I \<Longrightarrow> finite (offd I)"
  unfolding offd_def by (rule finite_subset[of _ "I \<times> I"]) auto

lemma two_elems:
  assumes "2 \<le> card I" "i \<in> I" shows "I - {i} \<noteq> {}"
proof
  assume "I - {i} = {}"
  hence "I = {i}" using assms(2) by blast
  thus False using assms(1) by simp
qed

lemma card2_nonempty: assumes "2 \<le> card I" shows "I \<noteq> {}"
  using assms by (cases "I = {}") simp_all

lemma offd_nonempty:
  assumes "2 \<le> card I" shows "offd I \<noteq> {}"
proof -
  obtain i where i: "i \<in> I" using card2_nonempty[OF assms] by blast
  obtain j where j: "j \<in> I - {i}" using two_elems[OF assms i] by blast
  have "(i, j) \<in> offd I" using i j by (auto simp: offd_def)
  thus ?thesis by blast
qed

theorem tensor_coherence:
  fixes f :: "'a \<Rightarrow> real^'n" and r :: "'s \<Rightarrow> real^'m"
  assumes finA: "finite A" and finS: "finite S" and cA: "2 \<le> card A" and cS: "2 \<le> card S"
      and uf: "\<forall>a\<in>A. norm (f a) = 1" and ur: "\<forall>s\<in>S. norm (r s) = 1"
  shows "coh (bound f r) (A \<times> S) = max (coh f A) (coh r S)"
proof -
  define gF where "gF = (\<lambda>p. \<bar>inner (f (fst p)) (f (snd p))\<bar>)"
  define gR where "gR = (\<lambda>p. \<bar>inner (r (fst p)) (r (snd p))\<bar>)"
  define gB where "gB = (\<lambda>p. \<bar>inner (bound f r (fst p)) (bound f r (snd p))\<bar>)"
  have fF: "finite (gF ` offd A)" using offd_finite[OF finA] by simp
  have fR: "finite (gR ` offd S)" using offd_finite[OF finS] by simp
  have fB: "finite (gB ` offd (A \<times> S))" using offd_finite[of "A \<times> S"] finA finS by simp
  have nF: "gF ` offd A \<noteq> {}" using offd_nonempty[OF cA] by simp
  have nR: "gR ` offd S \<noteq> {}" using offd_nonempty[OF cS] by simp
  obtain s0 where s0: "s0 \<in> S" using card2_nonempty[OF cS] by blast
  obtain a0 where a0: "a0 \<in> A" using card2_nonempty[OF cA] by blast
  have one_r: "inner (r s0) (r s0) = 1" using ur s0 by (simp add: norm_eq_1)
  have one_f: "inner (f a0) (f a0) = 1" using uf a0 by (simp add: norm_eq_1)
  have FB: "gF ` offd A \<subseteq> gB ` offd (A \<times> S)"
  proof (rule image_subsetI)
    fix p assume p: "p \<in> offd A"
    let ?q = "((fst p, s0), (snd p, s0))"
    have "?q \<in> offd (A \<times> S)" using p s0 by (auto simp: offd_def)
    moreover have "gF p = gB ?q" by (simp add: gF_def gB_def bound_inner one_r)
    ultimately show "gF p \<in> gB ` offd (A \<times> S)" by (rule rev_image_eqI)
  qed
  have RB: "gR ` offd S \<subseteq> gB ` offd (A \<times> S)"
  proof (rule image_subsetI)
    fix p assume p: "p \<in> offd S"
    let ?q = "((a0, fst p), (a0, snd p))"
    have "?q \<in> offd (A \<times> S)" using p a0 by (auto simp: offd_def)
    moreover have "gR p = gB ?q" by (simp add: gR_def gB_def bound_inner one_f)
    ultimately show "gR p \<in> gB ` offd (A \<times> S)" by (rule rev_image_eqI)
  qed
  have le: "gB q \<le> max (Max (gF ` offd A)) (Max (gR ` offd S))" if q: "q \<in> offd (A \<times> S)" for q
  proof -
    define a where "a = fst (fst q)"
    define b where "b = fst (snd q)"
    define s where "s = snd (fst q)"
    define t where "t = snd (snd q)"
    have m: "a \<in> A" "b \<in> A" "s \<in> S" "t \<in> S"
      using q by (auto simp: offd_def a_def b_def s_def t_def mem_Times_iff)
    have ne: "a \<noteq> b \<or> s \<noteq> t" using q by (auto simp: offd_def a_def b_def s_def t_def prod_eq_iff)
    have e: "gB q = \<bar>inner (f a) (f b)\<bar> * \<bar>inner (r s) (r t)\<bar>"
      by (simp add: gB_def bound_inner' a_def b_def s_def t_def abs_mult)
    show ?thesis
    proof (cases "a = b")
      case True
      hence st: "s \<noteq> t" using ne by simp
      have "(s, t) \<in> offd S" using m st by (simp add: offd_def)
      hence "gR (s, t) \<le> Max (gR ` offd S)" using fR by simp
      moreover have "inner (f a) (f a) = 1" using uf m(1) by (simp add: norm_eq_1)
      hence "gB q = gR (s, t)" using e True by (simp add: gR_def)
      ultimately show ?thesis by simp
    next
      case False
      have "(a, b) \<in> offd A" using m False by (simp add: offd_def)
      hence fm: "gF (a, b) \<le> Max (gF ` offd A)" using fF by simp
      have r1: "\<bar>inner (r s) (r t)\<bar> \<le> 1" using unit_inner_abs_le1 ur m(3,4) by blast
      have "gB q \<le> \<bar>inner (f a) (f b)\<bar> * 1" unfolding e by (rule mult_left_mono[OF r1]) simp
      hence "gB q \<le> gF (a, b)" by (simp add: gF_def)
      thus ?thesis using fm by simp
    qed
  qed
  have nB: "gB ` offd (A \<times> S) \<noteq> {}" using FB nF by blast
  have "Max (gB ` offd (A \<times> S)) \<le> max (Max (gF ` offd A)) (Max (gR ` offd S))"
    using fB nB le by (simp add: Max_le_iff)
  moreover have "Max (gF ` offd A) \<le> Max (gB ` offd (A \<times> S))" by (rule Max_mono[OF FB nF fB])
  moreover have "Max (gR ` offd S) \<le> Max (gB ` offd (A \<times> S))" by (rule Max_mono[OF RB nR fB])
  ultimately show ?thesis by (simp add: coh_def gF_def gR_def gB_def)
qed

text \<open>The SIGNED coherence of element @{term i}: its largest (signed) inner product with another element.
  This is the @{text mu} of @{thm optimal_margin_coherence_sandwich}.\<close>

definition scoh :: "('i \<Rightarrow> 'a::real_inner) \<Rightarrow> 'i set \<Rightarrow> 'i \<Rightarrow> real" where
  "scoh x I i = Max ((\<lambda>j. inner (x i) (x j)) ` (I - {i}))"

theorem tensor_signed_coherence:
  fixes f :: "'a \<Rightarrow> real^'n" and r :: "'s \<Rightarrow> real^'m"
  assumes finA: "finite A" and finS: "finite S" and cA: "2 \<le> card A" and cS: "2 \<le> card S"
      and a: "a \<in> A" and s: "s \<in> S"
      and uf: "norm (f a) = 1" and ur: "norm (r s) = 1"
  shows "scoh (bound f r) (A \<times> S) (a, s)
         = Max {scoh f A a, scoh r S s,
                Max ((\<lambda>(b, t). inner (f a) (f b) * inner (r s) (r t)) ` ((A - {a}) \<times> (S - {s})))}"
proof -
  let ?g = "\<lambda>j. inner (bound f r (a, s)) (bound f r j)"
  have oa: "inner (f a) (f a) = 1" and os: "inner (r s) (r s) = 1" using uf ur by (simp_all add: norm_eq_1)
  have split: "A \<times> S - {(a, s)} = ((A - {a}) \<times> {s}) \<union> ({a} \<times> (S - {s})) \<union> ((A - {a}) \<times> (S - {s}))"
    using a s by auto
  have i1: "?g ` ((A - {a}) \<times> {s}) = (\<lambda>b. inner (f a) (f b)) ` (A - {a})"
    by (force simp: bound_inner os)
  have i2: "?g ` ({a} \<times> (S - {s})) = (\<lambda>t. inner (r s) (r t)) ` (S - {s})"
    by (force simp: bound_inner oa)
  have i3: "?g ` ((A - {a}) \<times> (S - {s}))
            = (\<lambda>(b, t). inner (f a) (f b) * inner (r s) (r t)) ` ((A - {a}) \<times> (S - {s}))"
    by (force simp: bound_inner)
  have neA: "A - {a} \<noteq> {}" by (rule two_elems[OF cA a])
  have neS: "S - {s} \<noteq> {}" by (rule two_elems[OF cS s])
  have f1: "finite ((\<lambda>b. inner (f a) (f b)) ` (A - {a}))" using finA by simp
  have f2: "finite ((\<lambda>t. inner (r s) (r t)) ` (S - {s}))" using finS by simp
  have f3: "finite ((\<lambda>(b, t). inner (f a) (f b) * inner (r s) (r t)) ` ((A - {a}) \<times> (S - {s})))"
    using finA finS by simp
  have n3: "(\<lambda>(b, t). inner (f a) (f b) * inner (r s) (r t)) ` ((A - {a}) \<times> (S - {s})) \<noteq> {}"
    using neA neS by simp
  have img: "?g ` (A \<times> S - {(a, s)})
        = (\<lambda>b. inner (f a) (f b)) ` (A - {a}) \<union> (\<lambda>t. inner (r s) (r t)) ` (S - {s})
          \<union> (\<lambda>(b, t). inner (f a) (f b) * inner (r s) (r t)) ` ((A - {a}) \<times> (S - {s}))"
    by (simp only: split image_Un i1 i2 i3)
  have "scoh (bound f r) (A \<times> S) (a, s)
        = Max ((\<lambda>b. inner (f a) (f b)) ` (A - {a}) \<union> (\<lambda>t. inner (r s) (r t)) ` (S - {s})
               \<union> (\<lambda>(b, t). inner (f a) (f b) * inner (r s) (r t)) ` ((A - {a}) \<times> (S - {s})))"
    by (simp only: scoh_def img)
  also have "\<dots> = max (max (scoh f A a) (scoh r S s))
                     (Max ((\<lambda>(b, t). inner (f a) (f b) * inner (r s) (r t)) ` ((A - {a}) \<times> (S - {s}))))"
    using f1 f2 f3 neA neS n3 by (simp add: Max_Un scoh_def)
  finally show ?thesis by (simp add: max.assoc)
qed

corollary tensor_optimal_margin:
  fixes f :: "'a \<Rightarrow> real^'n" and r :: "'s \<Rightarrow> real^'m"
  assumes finA: "finite A" and finS: "finite S" and cA: "2 \<le> card A" and cS: "2 \<le> card S"
      and a: "a \<in> A" and s: "s \<in> S"
      and uf: "\<forall>b\<in>A. norm (f b) = 1" and ur: "\<forall>t\<in>S. norm (r t) = 1"
  shows "1 - scoh (bound f r) (A \<times> S) (a, s) \<le> optmargin (bound f r) (a, s) (A \<times> S - {(a, s)})"
proof -
  let ?C = "A \<times> S - {(a, s)}"
  have fin: "finite ?C" using finA finS by simp
  have "A - {a} \<noteq> {}" by (rule two_elems[OF cA a])
  then obtain b where b: "b \<in> A" "b \<noteq> a" by blast
  hence ne: "?C \<noteq> {}" using s by blast
  have unit: "\<forall>v\<in>insert (a, s) ?C. norm (bound f r v) = 1"
    using uf ur a s by (auto simp: bound_def norm_tprod)
  have "1 - Max ((\<lambda>v. inner (bound f r (a, s)) (bound f r v)) ` ?C) \<le> optmargin (bound f r) (a, s) ?C"
    using optimal_margin_coherence_sandwich(1)[OF fin ne unit] .
  thus ?thesis by (simp add: scoh_def)
qed

section \<open>T2 -- the diagonal-inclusive frame potential is multiplicative\<close>

definition FP :: "('i \<Rightarrow> 'a::real_inner) \<Rightarrow> 'i set \<Rightarrow> real" where
  "FP x I = (\<Sum>i\<in>I. \<Sum>j\<in>I. (inner (x i) (x j))\<^sup>2)"

definition welch_value :: "'i set \<Rightarrow> nat \<Rightarrow> real" where
  "welch_value I d = real (card I) ^ 2 / real d"

lemma sum_prod_split:
  fixes g :: "'a \<Rightarrow> real" and h :: "'s \<Rightarrow> real"
  shows "(\<Sum>(a, s)\<in>A \<times> S. g a * h s) = (\<Sum>a\<in>A. g a) * (\<Sum>s\<in>S. h s)"
proof -
  have "(\<Sum>(a, s)\<in>A \<times> S. g a * h s) = (\<Sum>a\<in>A. \<Sum>s\<in>S. g a * h s)"
    by (simp add: sum.cartesian_product)
  also have "\<dots> = (\<Sum>a\<in>A. g a * (\<Sum>s\<in>S. h s))" by (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>a\<in>A. g a) * (\<Sum>s\<in>S. h s)" by (simp add: sum_distrib_right)
  finally show ?thesis .
qed

theorem tensor_frame_potential:
  fixes f :: "'a \<Rightarrow> real^'n" and r :: "'s \<Rightarrow> real^'m"
  shows "FP (bound f r) (A \<times> S) = FP f A * FP r S"
proof -
  let ?F = "\<lambda>a b. (inner (f a) (f b))\<^sup>2" and ?R = "\<lambda>s t. (inner (r s) (r t))\<^sup>2"
  have inner_pair: "\<And>i. (\<Sum>j\<in>A \<times> S. (inner (bound f r i) (bound f r j))\<^sup>2)
                        = (\<Sum>b\<in>A. ?F (fst i) b) * (\<Sum>t\<in>S. ?R (snd i) t)"
  proof -
    fix i
    have "(\<Sum>j\<in>A \<times> S. (inner (bound f r i) (bound f r j))\<^sup>2)
          = (\<Sum>(b, t)\<in>A \<times> S. ?F (fst i) b * ?R (snd i) t)"
      by (rule sum.cong) (auto simp: bound_inner' power_mult_distrib)
    also have "\<dots> = (\<Sum>b\<in>A. ?F (fst i) b) * (\<Sum>t\<in>S. ?R (snd i) t)" by (rule sum_prod_split)
    finally show "(\<Sum>j\<in>A \<times> S. (inner (bound f r i) (bound f r j))\<^sup>2)
                  = (\<Sum>b\<in>A. ?F (fst i) b) * (\<Sum>t\<in>S. ?R (snd i) t)" .
  qed
  have "FP (bound f r) (A \<times> S) = (\<Sum>i\<in>A \<times> S. (\<Sum>b\<in>A. ?F (fst i) b) * (\<Sum>t\<in>S. ?R (snd i) t))"
    by (simp add: FP_def inner_pair)
  also have "\<dots> = (\<Sum>(a, s)\<in>A \<times> S. (\<Sum>b\<in>A. ?F a b) * (\<Sum>t\<in>S. ?R s t))"
    by (rule sum.cong) auto
  also have "\<dots> = (\<Sum>a\<in>A. \<Sum>b\<in>A. ?F a b) * (\<Sum>s\<in>S. \<Sum>t\<in>S. ?R s t)" by (rule sum_prod_split)
  also have "\<dots> = FP f A * FP r S" by (simp add: FP_def)
  finally show ?thesis .
qed

theorem tensor_welch_value:
  "welch_value (A \<times> S) (dF * dR) = welch_value A dF * welch_value S dR"
  by (simp add: welch_value_def card_cartesian_product power_mult_distrib)

theorem tensor_fp_welch_ratio:
  fixes f :: "'a \<Rightarrow> real^'n" and r :: "'s \<Rightarrow> real^'m"
  shows "FP (bound f r) (A \<times> S) / welch_value (A \<times> S) (dF * dR)
         = (FP f A / welch_value A dF) * (FP r S / welch_value S dR)"
  using tensor_frame_potential[of f r A S] tensor_welch_value[of A S dF dR] by simp

text \<open>The bound vectors live in a space of dimension DIM('n) * DIM('m): the Welch value above with
  @{term "dF = CARD('n)"} and @{term "dR = CARD('m)"} is the bound frame's own.\<close>

lemma tensor_space_dim: "DIM(real^'m^'n) = CARD('n) * CARD('m)"
  by simp

section \<open>T3 -- the matched-filter unbinding certificate\<close>

text \<open>Read role @{term w} out of a matrix: the matrix-vector product, row by row.\<close>

definition unbind :: "real^'m^'n \<Rightarrow> real^'m \<Rightarrow> real^'n" where
  "unbind T w = (\<chi> i. inner (T$i) w)"

lemma unbind_tprod: "unbind (tprod f r) w = inner r w *\<^sub>R f"
  by (simp add: unbind_def tprod_def vec_eq_iff mult.commute)

lemma unbind_sum: "unbind (\<Sum>t\<in>D. T t) w = (\<Sum>t\<in>D. unbind (T t) w)"
  by (simp add: unbind_def vec_eq_iff inner_sum_left sum_component)

definition structure_tpr :: "('b \<Rightarrow> real^'n) \<Rightarrow> ('s \<Rightarrow> real^'m) \<Rightarrow> ('s \<Rightarrow> 'b) \<Rightarrow> 's set \<Rightarrow> real^'m^'n" where
  "structure_tpr f r \<sigma> D = (\<Sum>t\<in>D. tprod (f (\<sigma> t)) (r t))"

lemma unbind_score:
  assumes "finite D"
  shows "inner (unbind (structure_tpr f r \<sigma> D) w) g = (\<Sum>t\<in>D. inner (r t) w * inner (f (\<sigma> t)) g)"
  by (simp add: structure_tpr_def unbind_sum unbind_tprod inner_sum_left)

theorem unbind_certified:
  fixes f :: "'b \<Rightarrow> real^'n" and r :: "'s \<Rightarrow> real^'m"
  assumes finD: "finite D" and s0: "s0 \<in> D" and k: "card D = k"
      and ur: "norm (r s0) = 1"
      and uf: "\<forall>b\<in>Fs \<union> \<sigma> ` D. norm (f b) = 1"
      and cross: "\<forall>t\<in>D - {s0}. \<bar>inner (r t) (r s0)\<bar> \<le> \<mu>"
      and tgt: "\<sigma> s0 \<in> Fs"
      and marg: "\<forall>b\<in>Fs. b \<noteq> \<sigma> s0 \<longrightarrow> 1 - inner (f (\<sigma> s0)) (f b) > 2 * ((real k - 1) * \<mu>)"
  shows "decodes_to (\<lambda>b. inner (unbind (structure_tpr f r \<sigma> D) (r s0)) (f b)) Fs (\<sigma> s0)"
proof (rule decode_margin_certified)
  let ?L = "\<lambda>b. inner (f (\<sigma> s0)) (f b)"
  let ?L' = "\<lambda>b. inner (unbind (structure_tpr f r \<sigma> D) (r s0)) (f b)"
  show "\<sigma> s0 \<in> Fs" by (rule tgt)
  have o: "inner (r s0) (r s0) = 1" using ur by (simp add: norm_eq_1)
  show "\<bar>?L' b - ?L b\<bar> \<le> (real k - 1) * \<mu>" if b: "b \<in> Fs" for b
  proof -
    have "?L' b = (\<Sum>t\<in>D. inner (r t) (r s0) * inner (f (\<sigma> t)) (f b))" by (rule unbind_score[OF finD])
    also have "\<dots> = inner (f (\<sigma> s0)) (f b) + (\<Sum>t\<in>D - {s0}. inner (r t) (r s0) * inner (f (\<sigma> t)) (f b))"
      using finD s0 o by (simp add: sum.remove)
    finally have eq: "?L' b - ?L b = (\<Sum>t\<in>D - {s0}. inner (r t) (r s0) * inner (f (\<sigma> t)) (f b))" by simp
    have each: "\<bar>inner (r t) (r s0) * inner (f (\<sigma> t)) (f b)\<bar> \<le> \<mu>" if t: "t \<in> D - {s0}" for t
    proof -
      have f1: "\<bar>inner (f (\<sigma> t)) (f b)\<bar> \<le> 1" using unit_inner_abs_le1 uf b t by blast
      have rm: "\<bar>inner (r t) (r s0)\<bar> \<le> \<mu>" using cross t by blast
      have "\<bar>inner (r t) (r s0) * inner (f (\<sigma> t)) (f b)\<bar>
            = \<bar>inner (r t) (r s0)\<bar> * \<bar>inner (f (\<sigma> t)) (f b)\<bar>" by (rule abs_mult)
      also have "\<dots> \<le> \<bar>inner (r t) (r s0)\<bar> * 1" by (rule mult_left_mono[OF f1]) simp
      also have "\<dots> \<le> \<mu>" using rm by simp
      finally show ?thesis .
    qed
    have "\<bar>?L' b - ?L b\<bar> \<le> (\<Sum>t\<in>D - {s0}. \<bar>inner (r t) (r s0) * inner (f (\<sigma> t)) (f b)\<bar>)"
      unfolding eq by (rule sum_abs)
    also have "\<dots> \<le> (\<Sum>t\<in>D - {s0}. \<mu>)" by (rule sum_mono) (use each in blast)
    also have "\<dots> = real (card (D - {s0})) * \<mu>" by simp
    also have "\<dots> = (real k - 1) * \<mu>"
    proof -
      have "card D \<ge> 1" using finD s0 by (metis One_nat_def Suc_leI card_gt_0_iff empty_iff)
      thus ?thesis using s0 k by (simp add: card_Diff_singleton of_nat_diff)
    qed
    finally show ?thesis .
  qed
  show "?L (\<sigma> s0) - ?L b > 2 * ((real k - 1) * \<mu>)" if "b \<in> Fs" "b \<noteq> \<sigma> s0" for b
  proof -
    have "inner (f (\<sigma> s0)) (f (\<sigma> s0)) = 1" using uf tgt by (simp add: norm_eq_1)
    thus ?thesis using marg that by simp
  qed
qed

section \<open>T5(a) -- last-layer substitution is certified by the margin theorem\<close>

theorem substitution_certified:
  fixes U :: "'v \<Rightarrow> 'a::real_inner"
  assumes tV: "t \<in> V"
      and delta: "\<forall>v\<in>V. \<bar>inner (r - rhat) (U v)\<bar> \<le> \<delta>"
      and marg: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> (inner r (U t) + bias t) - (inner r (U v) + bias v) > 2 * \<delta>"
  shows "decodes_to (\<lambda>v. inner rhat (U v) + bias v) V t"
proof (rule decode_margin_certified[where L = "\<lambda>v. inner r (U v) + bias v"])
  show "t \<in> V" by (rule tV)
  show "\<bar>(inner rhat (U v) + bias v) - (inner r (U v) + bias v)\<bar> \<le> \<delta>" if "v \<in> V" for v
  proof -
    have "(inner rhat (U v) + bias v) - (inner r (U v) + bias v) = - inner (r - rhat) (U v)"
      by (simp add: inner_diff_left)
    thus ?thesis using delta that by simp
  qed
  show "(inner r (U t) + bias t) - (inner r (U v) + bias v) > 2 * \<delta>" if "v \<in> V" "v \<noteq> t" for v
    using marg that by blast
qed

corollary substitution_certified_max:
  fixes U :: "'v \<Rightarrow> 'a::real_inner"
  assumes finV: "finite V" and tV: "t \<in> V"
      and marg: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> (inner r (U t) + bias t) - (inner r (U v) + bias v)
                     > 2 * Max ((\<lambda>v. \<bar>inner (r - rhat) (U v)\<bar>) ` V)"
  shows "decodes_to (\<lambda>v. inner rhat (U v) + bias v) V t"
proof (rule substitution_certified[OF tV _ marg])
  show "\<forall>v\<in>V. \<bar>inner (r - rhat) (U v)\<bar> \<le> Max ((\<lambda>v. \<bar>inner (r - rhat) (U v)\<bar>) ` V)"
    using finV by simp
qed

corollary substitution_certified_norm:
  fixes U :: "'v \<Rightarrow> 'a::real_inner"
  assumes tV: "t \<in> V" and umax: "\<forall>v\<in>V. norm (U v) \<le> u"
      and marg: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> (inner r (U t) + bias t) - (inner r (U v) + bias v) > 2 * (norm (r - rhat) * u)"
  shows "decodes_to (\<lambda>v. inner rhat (U v) + bias v) V t"
proof (rule substitution_certified[OF tV _ marg])
  show "\<forall>v\<in>V. \<bar>inner (r - rhat) (U v)\<bar> \<le> norm (r - rhat) * u"
  proof
    fix v assume v: "v \<in> V"
    have "\<bar>inner (r - rhat) (U v)\<bar> \<le> norm (r - rhat) * norm (U v)" by (rule Cauchy_Schwarz_ineq2)
    also have "\<dots> \<le> norm (r - rhat) * u" using umax v by (simp add: mult_left_mono)
    finally show "\<bar>inner (r - rhat) (U v)\<bar> \<le> norm (r - rhat) * u" .
  qed
qed

section \<open>T5(a), pairwise -- the exact substitution certificate\<close>

text \<open>Per rival, the substituted decode keeps @{term t} iff the original margin over that rival exceeds the
  projection of the substitution error onto the readout difference. The condition is EXACT (an iff), so it
  certifies precisely the contexts on which the decision is preserved; the uniform form above is a sufficient
  special case, and the hybrid form checks only a finite rival set K pairwise and bounds the rest by a norm.\<close>

lemma subst_logit_gap:
  "(inner rhat (U t) + bias t) - (inner rhat (U v) + bias v)
   = ((inner r (U t) + bias t) - (inner r (U v) + bias v)) - inner (r - rhat) (U t - U v)"
  by (simp add: inner_diff_left inner_diff_right algebra_simps)

theorem substitution_pairwise_iff:
  fixes U :: "'v \<Rightarrow> 'a::real_inner"
  assumes tV: "t \<in> V"
  shows "decodes_to (\<lambda>v. inner rhat (U v) + bias v) V t
         \<longleftrightarrow> (\<forall>v\<in>V. v \<noteq> t \<longrightarrow>
               (inner r (U t) + bias t) - (inner r (U v) + bias v) > inner (r - rhat) (U t - U v))"
proof -
  have "inner rhat (U v) + bias v < inner rhat (U t) + bias t
        \<longleftrightarrow> (inner r (U t) + bias t) - (inner r (U v) + bias v) > inner (r - rhat) (U t - U v)" for v
    using subst_logit_gap[of rhat U t bias v r] by linarith
  thus ?thesis using tV by (simp add: decodes_to_def)
qed

corollary substitution_certified_pairwise:
  fixes U :: "'v \<Rightarrow> 'a::real_inner"
  assumes tV: "t \<in> V"
      and pair: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow>
                   (inner r (U t) + bias t) - (inner r (U v) + bias v) > inner (r - rhat) (U t - U v)"
  shows "decodes_to (\<lambda>v. inner rhat (U v) + bias v) V t"
  using substitution_pairwise_iff[OF tV] pair by blast

theorem uniform_implies_pairwise:
  fixes U :: "'v \<Rightarrow> 'a::real_inner"
  assumes tV: "t \<in> V"
      and delta: "\<forall>v\<in>V. \<bar>inner (r - rhat) (U v)\<bar> \<le> \<delta>"
      and marg: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> (inner r (U t) + bias t) - (inner r (U v) + bias v) > 2 * \<delta>"
  shows "\<forall>v\<in>V. v \<noteq> t \<longrightarrow>
           (inner r (U t) + bias t) - (inner r (U v) + bias v) > inner (r - rhat) (U t - U v)"
proof (intro ballI impI)
  fix v assume v: "v \<in> V" and ne: "v \<noteq> t"
  have "inner (r - rhat) (U t - U v) = inner (r - rhat) (U t) - inner (r - rhat) (U v)"
    by (simp add: inner_diff_right)
  also have "\<dots> \<le> \<bar>inner (r - rhat) (U t)\<bar> + \<bar>inner (r - rhat) (U v)\<bar>" by linarith
  also have "\<dots> \<le> 2 * \<delta>" using delta tV v by (smt (verit))
  finally show "(inner r (U t) + bias t) - (inner r (U v) + bias v) > inner (r - rhat) (U t - U v)"
    using marg v ne by fastforce
qed

theorem substitution_certified_hybrid:
  fixes U :: "'v \<Rightarrow> 'a::real_inner"
  assumes tV: "t \<in> V"
      and umax: "\<forall>v\<in>V. norm (U v) \<le> u"
      and head: "\<forall>v\<in>K. v \<noteq> t \<longrightarrow>
                   (inner r (U t) + bias t) - (inner r (U v) + bias v) > inner (r - rhat) (U t - U v)"
      and tail: "\<forall>v\<in>V - K. v \<noteq> t \<longrightarrow>
                   (inner r (U t) + bias t) - (inner r (U v) + bias v)
                   > \<bar>inner (r - rhat) (U t)\<bar> + norm (r - rhat) * u"
  shows "decodes_to (\<lambda>v. inner rhat (U v) + bias v) V t"
proof (rule substitution_certified_pairwise[OF tV], intro ballI impI)
  fix v assume v: "v \<in> V" and ne: "v \<noteq> t"
  show "(inner r (U t) + bias t) - (inner r (U v) + bias v) > inner (r - rhat) (U t - U v)"
  proof (cases "v \<in> K")
    case True
    thus ?thesis using head ne by blast
  next
    case False
    have cs: "\<bar>inner (r - rhat) (U v)\<bar> \<le> norm (r - rhat) * u"
    proof -
      have "\<bar>inner (r - rhat) (U v)\<bar> \<le> norm (r - rhat) * norm (U v)" by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> norm (r - rhat) * u" using umax v by (simp add: mult_left_mono)
      finally show ?thesis .
    qed
    have "inner (r - rhat) (U t - U v) = inner (r - rhat) (U t) - inner (r - rhat) (U v)"
      by (simp add: inner_diff_right)
    also have "\<dots> \<le> \<bar>inner (r - rhat) (U t)\<bar> + norm (r - rhat) * u" using cs by linarith
    finally show ?thesis using tail v ne False by fastforce
  qed
qed

section \<open>T5(b) -- substitution certified uniformly over a domain of contexts\<close>

text \<open>A domain D of contexts x, each with a decode input r x, a substitute rhat x and a decision t x. If ONE
  error bound eps holds on all of D, one margin condition certifies every context in D at once, including
  contexts never evaluated. The theorem moves the burden to the hypothesis: bounding the fit error on all of D
  is an empirical or separate claim, not something this theory supplies.\<close>

theorem substitution_domain_norm:
  fixes U :: "'v \<Rightarrow> 'a::real_inner" and r rhat :: "'x \<Rightarrow> 'a" and t :: "'x \<Rightarrow> 'v"
  assumes tV: "\<forall>x\<in>D. t x \<in> V"
      and umax: "\<forall>v\<in>V. norm (U v) \<le> u"
      and err: "\<forall>x\<in>D. norm (r x - rhat x) \<le> \<epsilon>"
      and marg: "\<forall>x\<in>D. \<forall>v\<in>V. v \<noteq> t x \<longrightarrow>
                   (inner (r x) (U (t x)) + bias (t x)) - (inner (r x) (U v) + bias v) > 2 * (\<epsilon> * u)"
  shows "\<forall>x\<in>D. decodes_to (\<lambda>v. inner (rhat x) (U v) + bias v) V (t x)"
proof
  fix x assume x: "x \<in> D"
  have tx: "t x \<in> V" using tV x by blast
  have u0: "0 \<le> u" using umax tx by (meson norm_ge_zero order_trans)
  have le: "norm (r x - rhat x) * u \<le> \<epsilon> * u" using err x u0 by (simp add: mult_right_mono)
  show "decodes_to (\<lambda>v. inner (rhat x) (U v) + bias v) V (t x)"
  proof (rule substitution_certified_norm[OF tx umax])
    show "\<forall>v\<in>V. v \<noteq> t x \<longrightarrow> (inner (r x) (U (t x)) + bias (t x)) - (inner (r x) (U v) + bias v)
            > 2 * (norm (r x - rhat x) * u)"
      using marg x le by fastforce
  qed
qed

theorem substitution_domain_pairwise:
  fixes U :: "'v \<Rightarrow> 'a::real_inner" and r rhat :: "'x \<Rightarrow> 'a" and t :: "'x \<Rightarrow> 'v"
  assumes tV: "\<forall>x\<in>D. t x \<in> V"
      and err: "\<forall>x\<in>D. norm (r x - rhat x) \<le> \<epsilon>"
      and marg: "\<forall>x\<in>D. \<forall>v\<in>V. v \<noteq> t x \<longrightarrow>
                   (inner (r x) (U (t x)) + bias (t x)) - (inner (r x) (U v) + bias v)
                   > \<epsilon> * norm (U (t x) - U v)"
  shows "\<forall>x\<in>D. decodes_to (\<lambda>v. inner (rhat x) (U v) + bias v) V (t x)"
proof
  fix x assume x: "x \<in> D"
  have tx: "t x \<in> V" using tV x by blast
  show "decodes_to (\<lambda>v. inner (rhat x) (U v) + bias v) V (t x)"
  proof (rule substitution_certified_pairwise[OF tx], intro ballI impI)
    fix v assume v: "v \<in> V" and ne: "v \<noteq> t x"
    have "inner (r x - rhat x) (U (t x) - U v) \<le> norm (r x - rhat x) * norm (U (t x) - U v)"
      by (rule norm_cauchy_schwarz)
    also have "\<dots> \<le> \<epsilon> * norm (U (t x) - U v)" using err x by (simp add: mult_right_mono)
    finally show "(inner (r x) (U (t x)) + bias (t x)) - (inner (r x) (U v) + bias v)
                  > inner (r x - rhat x) (U (t x) - U v)"
      using marg x v ne by fastforce
  qed
qed

text \<open>The per-rival domain form is at least as strong as the norm form: its threshold is never larger.\<close>

theorem domain_norm_implies_pairwise:
  fixes U :: "'v \<Rightarrow> 'a::real_inner"
  assumes tV: "t \<in> V" and v: "v \<in> V" and umax: "\<forall>w\<in>V. norm (U w) \<le> u" and eps: "0 \<le> \<epsilon>"
  shows "\<epsilon> * norm (U t - U v) \<le> 2 * (\<epsilon> * u)"
proof -
  have "norm (U t - U v) \<le> norm (U t) + norm (U v)" by (rule norm_triangle_ineq4)
  also have "\<dots> \<le> 2 * u"
  proof -
    have "norm (U t) \<le> u" "norm (U v) \<le> u" using umax tV v by blast+
    thus ?thesis by linarith
  qed
  finally have n: "norm (U t - U v) \<le> 2 * u" .
  have "\<epsilon> * norm (U t - U v) \<le> \<epsilon> * (2 * u)" by (rule mult_left_mono[OF n eps])
  thus ?thesis by simp
qed

section \<open>T5(c) -- the hull ceiling on any margin-threshold certificate\<close>

text \<open>Bias-free decode. hull_margin_upper bounds the worst-rival margin of a UNIT residual by the hull distance;
  scaling gives margin <= norm r * hull distance for any residual. So a certificate that needs every margin above
  a threshold m can fire only when m < norm r * hdist(t). The ceiling depends on the frame U and the residual
  norm, NOT on the substitute: no fit, however good, is certified past it by a margin-threshold certificate.
  The EXACT pairwise certificate (substitution_pairwise_iff) is not a threshold certificate and has no such
  ceiling.\<close>

lemma hull_margin_upper_scaled:
  fixes U :: "'v \<Rightarrow> 'a::euclidean_space"
  assumes finC: "finite C" and neC: "C \<noteq> {}"
  shows "\<exists>v\<in>C. inner r (U t - U v) \<le> norm r * infdist (U t) (convex hull (U ` C))"
proof (cases "r = 0")
  case True
  thus ?thesis using neC by auto
next
  case False
  define s where "s = (1 / norm r) *\<^sub>R r"
  have ns: "norm s \<le> 1" using False by (simp add: s_def)
  obtain v where v: "v \<in> C" "inner s (U t - U v) \<le> infdist (U t) (convex hull (U ` C))"
    using hull_margin_upper[where U = U and t = t, OF finC neC ns] by blast
  have "inner r (U t - U v) = norm r * inner s (U t - U v)" using False by (simp add: s_def)
  also have "\<dots> \<le> norm r * infdist (U t) (convex hull (U ` C))" using v(2) by (simp add: mult_left_mono)
  finally show ?thesis using v(1) by blast
qed

theorem certificate_hull_ceiling:
  fixes U :: "'v \<Rightarrow> 'a::euclidean_space"
  assumes finC: "finite C" and neC: "C \<noteq> {}"
      and marg: "\<forall>v\<in>C. inner r (U t) - inner r (U v) > m"
  shows "m < norm r * infdist (U t) (convex hull (U ` C))"
proof -
  obtain v where v: "v \<in> C" "inner r (U t - U v) \<le> norm r * infdist (U t) (convex hull (U ` C))"
    using hull_margin_upper_scaled[OF finC neC] by blast
  have "m < inner r (U t) - inner r (U v)" using marg v(1) by blast
  also have "\<dots> = inner r (U t - U v)" by (simp add: inner_diff_right)
  finally show ?thesis using v(2) by linarith
qed

corollary substitution_hull_ceiling:
  fixes U :: "'v \<Rightarrow> 'a::euclidean_space"
  assumes finV: "finite V" and other: "V - {t} \<noteq> {}"
      and marg: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> inner r (U t) - inner r (U v) > 2 * \<delta>"
  shows "2 * \<delta> < norm r * infdist (U t) (convex hull (U ` (V - {t})))"
  using certificate_hull_ceiling[of "V - {t}"] finV other marg by blast

end
