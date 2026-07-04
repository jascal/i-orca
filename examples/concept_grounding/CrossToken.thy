(*
  CrossToken.thy -- C7: cross-token equality is linear-impossible but bilinear-easy.

  Follow-on conjecture from the Wyly review (pil PR #10, `feat/concept-rule-learner`). The PR's
  descriptive frontier: cross-token comparison (is_repeat / induction) caps at ~0.78 for every
  grounded reader while lexical properties sit at ~0.94, scale-invariant from pythia-70m to 1b, and
  `ground_multipos.py` finds the relation "computed-in-mechanism, not stored" -- symbolic, not
  geometric. This theory proves the geometry behind that wall, four ways:

    (i)   ADDITIVE IMPOSSIBILITY, dimension-free: no reader of the form g(t1) + h(t2) >= theta --
          which subsumes EVERY linear head over concatenated per-position features, residuals, or
          concept memberships, in any dimension -- decides [t1 = t2] once the vocabulary has two
          tokens. The 4-point argument: the two matched pairs and the two mismatched pairs have the
          SAME total score, but equality demands the first two clear a threshold the last two miss.
    (ii)  the concrete instances: linear readouts over per-position residual embeddings and over
          per-position concept-membership vectors (the grounded readers the PR trained) are special
          cases of (i), hence impossible.
    (iii) BILINEAR SUFFICIENCY: with orthonormal per-token features, the bilinear score
          <phi(t1), phi(t2)> IS the equality indicator (threshold 1/2, margin 1/2); such features
          exist whenever card V <= d. This is the PR's soft-eq `match = <m(cur), m(o)>` (and QK
          attention): equality is one bilinear feature away, though no number of linear ones suffice.
    (iv)  RULE-COUNT SEPARATION, C3-style: any conjunction of per-position concepts fires on a
          PRODUCT set A x B, and any family of product rules that covers the diagonal without firing
          off-diagonal needs at least card V rules (each rule pins a single token) -- realized
          exactly by the card V singleton rules. One symbolic eq_atom replaces card V geometric
          rules: the kernel-checked case for Wyly's unified substrate.

  Honest scope: (i)-(iv) are statements about EXACT deciders over a stated reader class; the PR's
  ~0.78 empirical ceiling for approximate readers, and anything about what pythia actually computes,
  stay `empirical`. Soft-AND rules with graded memberships are not the hard product rules of (iv);
  the counting bound applies to the {0,1}-conjunction semantics.
*)
theory CrossToken
  imports ConceptCells Consolidation
begin

subsection \<open>(i) No additive reader decides equality\<close>

text \<open>The 4-point core. If an additive score g(t1) + h(t2) clears theta exactly on the diagonal,
      the four evaluations on {x,y} x {x,y} are contradictory: both orderings of the sum are equal,
      yet the matched pairs must total at least 2*theta and the mismatched pairs strictly less.\<close>
theorem equality_not_additive:
  fixes g h :: "'t \<Rightarrow> real" and theta :: real
  assumes xV: "x \<in> V" and yV: "y \<in> V" and xy: "x \<noteq> y"
      and dec: "\<And>t1 t2. t1 \<in> V \<Longrightarrow> t2 \<in> V \<Longrightarrow> (theta \<le> g t1 + h t2) \<longleftrightarrow> (t1 = t2)"
  shows False
proof -
  have 1: "theta \<le> g x + h x" using dec[OF xV xV] by simp
  have 2: "theta \<le> g y + h y" using dec[OF yV yV] by simp
  have 3: "\<not> theta \<le> g x + h y" using dec[OF xV yV] xy by simp
  have 4: "\<not> theta \<le> g y + h x" using dec[OF yV xV] xy by simp
  from 1 2 3 4 show False by linarith
qed

text \<open>Packaged: over any vocabulary with two tokens there is NO additive equality decider at all.\<close>
theorem equality_not_linear:
  fixes V :: "'t set"
  assumes "x \<in> V" and "y \<in> V" and "x \<noteq> y"
  shows "\<not> (\<exists>g h theta. \<forall>t1\<in>V. \<forall>t2\<in>V. ((theta::real) \<le> g t1 + h t2) \<longleftrightarrow> (t1 = t2))"
proof
  assume "\<exists>g h theta. \<forall>t1\<in>V. \<forall>t2\<in>V. ((theta::real) \<le> g t1 + h t2) \<longleftrightarrow> (t1 = t2)"
  then obtain g h theta
    where dec: "\<forall>t1\<in>V. \<forall>t2\<in>V. ((theta::real) \<le> g t1 + h t2) \<longleftrightarrow> (t1 = t2)" by auto
  show False
  proof (rule equality_not_additive[OF assms, of theta g h])
    fix t1 t2 assume "t1 \<in> V" and "t2 \<in> V"
    thus "(theta \<le> g t1 + h t2) \<longleftrightarrow> (t1 = t2)" using dec by auto
  qed
qed

subsection \<open>(ii) The grounded readers are additive, hence impossible\<close>

text \<open>A linear head over concatenated per-position RESIDUALS is an additive reader.\<close>
corollary equality_not_residual_linear:
  fixes r1 r2 :: "'t \<Rightarrow> 'a::real_inner" and W1 W2 :: 'a
  assumes "x \<in> V" and "y \<in> V" and "x \<noteq> y"
  shows "\<not> (\<exists>theta. \<forall>t1\<in>V. \<forall>t2\<in>V.
              ((theta::real) \<le> W1 \<bullet> r1 t1 + W2 \<bullet> r2 t2) \<longleftrightarrow> (t1 = t2))"
proof
  assume "\<exists>theta. \<forall>t1\<in>V. \<forall>t2\<in>V. ((theta::real) \<le> W1 \<bullet> r1 t1 + W2 \<bullet> r2 t2) \<longleftrightarrow> (t1 = t2)"
  then obtain theta
    where dec: "\<forall>t1\<in>V. \<forall>t2\<in>V. (theta \<le> W1 \<bullet> r1 t1 + W2 \<bullet> r2 t2) \<longleftrightarrow> (t1 = t2)" by auto
  show False
  proof (rule equality_not_additive[OF assms,
           where g = "\<lambda>t. W1 \<bullet> r1 t" and h = "\<lambda>t. W2 \<bullet> r2 t" and theta = theta])
    fix t1 t2 assume "t1 \<in> V" and "t2 \<in> V"
    thus "(theta \<le> W1 \<bullet> r1 t1 + W2 \<bullet> r2 t2) \<longleftrightarrow> (t1 = t2)" using dec by auto
  qed
qed

text \<open>... and so is a linear head over concatenated per-position CONCEPT MEMBERSHIPS: no bank of
      hyperplane concepts read per-position and combined linearly decides cross-token equality.\<close>
corollary equality_not_membership_linear:
  fixes u :: "'c \<Rightarrow> 'a::real_inner" and bb :: "'c \<Rightarrow> real"
    and w1 w2 :: "'c \<Rightarrow> real" and r1 r2 :: "'t \<Rightarrow> 'a"
  assumes "x \<in> V" and "y \<in> V" and "x \<noteq> y"
  shows "\<not> (\<exists>theta. \<forall>t1\<in>V. \<forall>t2\<in>V.
              ((theta::real) \<le> (\<Sum>c\<in>C. w1 c * (if fires u bb c (r1 t1) then 1 else 0)) +
                               (\<Sum>c\<in>C. w2 c * (if fires u bb c (r2 t2) then 1 else 0)))
              \<longleftrightarrow> (t1 = t2))"
proof
  assume "\<exists>theta. \<forall>t1\<in>V. \<forall>t2\<in>V.
            ((theta::real) \<le> (\<Sum>c\<in>C. w1 c * (if fires u bb c (r1 t1) then 1 else 0)) +
                             (\<Sum>c\<in>C. w2 c * (if fires u bb c (r2 t2) then 1 else 0)))
            \<longleftrightarrow> (t1 = t2)"
  then obtain theta
    where dec: "\<forall>t1\<in>V. \<forall>t2\<in>V.
            (theta \<le> (\<Sum>c\<in>C. w1 c * (if fires u bb c (r1 t1) then 1 else 0)) +
                     (\<Sum>c\<in>C. w2 c * (if fires u bb c (r2 t2) then 1 else 0)))
            \<longleftrightarrow> (t1 = t2)" by auto
  show False
  proof (rule equality_not_additive[OF assms,
           where g = "\<lambda>t. \<Sum>c\<in>C. w1 c * (if fires u bb c (r1 t) then 1 else 0)"
             and h = "\<lambda>t. \<Sum>c\<in>C. w2 c * (if fires u bb c (r2 t) then 1 else 0)"
             and theta = theta])
    fix t1 t2 assume "t1 \<in> V" and "t2 \<in> V"
    thus "(theta \<le> (\<Sum>c\<in>C. w1 c * (if fires u bb c (r1 t1) then 1 else 0)) +
                   (\<Sum>c\<in>C. w2 c * (if fires u bb c (r2 t2) then 1 else 0)))
          \<longleftrightarrow> (t1 = t2)" using dec by auto
  qed
qed

subsection \<open>(iii) One bilinear feature decides equality exactly\<close>

text \<open>With orthonormal per-token features the bilinear score IS the equality indicator: threshold
      one half, margin one half. This is the PR's soft-eq match (and the QK-attention primitive).\<close>
theorem equality_bilinear:
  fixes phi :: "'t \<Rightarrow> 'a::real_inner"
  assumes orth: "\<And>t1 t2. t1 \<in> V \<Longrightarrow> t2 \<in> V \<Longrightarrow>
                   phi t1 \<bullet> phi t2 = (if t1 = t2 then 1 else 0)"
      and t1V: "t1 \<in> V" and t2V: "t2 \<in> V"
  shows "(1 / 2 \<le> phi t1 \<bullet> phi t2) \<longleftrightarrow> (t1 = t2)"
proof (cases "t1 = t2")
  case True thus ?thesis using orth[OF t1V t2V] by simp
next
  case False thus ?thesis using orth[OF t1V t2V] by simp
qed

text \<open>Such features exist whenever the vocabulary fits the dimension: inject tokens into the
      orthonormal basis. Bilinear equality-reading is available at card V <= d, while (i) rules out
      additive equality-reading at EVERY dimension -- the separation theorem for the frontier.\<close>
theorem bilinear_reader_exists:
  fixes V :: "'t set"
  assumes fin: "finite V" and cd: "card V \<le> DIM('a::euclidean_space)"
  shows "\<exists>phi::'t \<Rightarrow> 'a. \<forall>t1\<in>V. \<forall>t2\<in>V. (1 / 2 \<le> phi t1 \<bullet> phi t2) \<longleftrightarrow> (t1 = t2)"
proof -
  have "card V \<le> card (Basis :: 'a set)" using cd by simp
  from card_le_inj[OF fin finite_Basis this]
  obtain phi :: "'t \<Rightarrow> 'a" where phiB: "phi ` V \<subseteq> Basis" and inj: "inj_on phi V" by auto
  have orth: "phi t1 \<bullet> phi t2 = (if t1 = t2 then 1 else 0)"
    if t1V: "t1 \<in> V" and t2V: "t2 \<in> V" for t1 t2
  proof -
    have B1: "phi t1 \<in> Basis" and B2: "phi t2 \<in> Basis" using phiB t1V t2V by auto
    show ?thesis
    proof (cases "t1 = t2")
      case True thus ?thesis using B1 by (simp add: inner_Basis)
    next
      case False
      hence "phi t1 \<noteq> phi t2" using inj t1V t2V by (auto dest: inj_onD)
      thus ?thesis using B1 B2 False by (simp add: inner_Basis)
    qed
  qed
  show ?thesis
  proof (intro exI[of _ phi] ballI)
    fix t1 t2 assume t1: "t1 \<in> V" and t2: "t2 \<in> V"
    show "(1 / 2 \<le> phi t1 \<bullet> phi t2) \<longleftrightarrow> (t1 = t2)"
    proof (cases "t1 = t2")
      case True thus ?thesis using orth[OF t1 t2] by simp
    next
      case False thus ?thesis using orth[OF t1 t2] by simp
    qed
  qed
qed

subsection \<open>(iv) Product rules: one token per rule\<close>

text \<open>A conjunction of per-position concepts fires on a PRODUCT set: the extent of its position-1
      concepts times the extent of its position-2 concepts. Conjunctive rules over per-position
      memberships can only carve products.\<close>
lemma conjunction_rule_is_product:
  "{(r1, r2). (\<forall>c\<in>S1. r1 \<in> Hspace u bb c) \<and> (\<forall>c\<in>S2. r2 \<in> Hspace u bb c)}
     = extent u bb S1 \<times> extent u bb S2"
  unfolding extent_def by auto

text \<open>The counting separation: any family of product rules A_i x B_i that covers every diagonal
      pair (t,t) and never fires on a mismatched pair uses at least card V rules -- each sound rule
      pins a single token. One symbolic eq_atom does the whole job.\<close>
theorem equality_needs_card_rules:
  fixes A B :: "'i \<Rightarrow> 't set" and V :: "'t set" and I :: "'i set"
  assumes finI: "finite I"
      and cover: "\<And>t. t \<in> V \<Longrightarrow> \<exists>i\<in>I. t \<in> A i \<and> t \<in> B i"
      and sound: "\<And>i t1 t2. i \<in> I \<Longrightarrow> t1 \<in> V \<Longrightarrow> t2 \<in> V \<Longrightarrow>
                    t1 \<in> A i \<Longrightarrow> t2 \<in> B i \<Longrightarrow> t1 = t2"
  shows "card V \<le> card I"
proof -
  define pick where "pick t = (SOME i. i \<in> I \<and> t \<in> A i \<and> t \<in> B i)" for t
  have pickP: "pick t \<in> I \<and> t \<in> A (pick t) \<and> t \<in> B (pick t)" if tV: "t \<in> V" for t
  proof -
    from cover[OF tV] obtain i where "i \<in> I" and "t \<in> A i" and "t \<in> B i" by auto
    hence "\<exists>i. i \<in> I \<and> t \<in> A i \<and> t \<in> B i" by (intro exI[of _ i] conjI)
    from someI_ex[OF this] show ?thesis unfolding pick_def .
  qed
  have inj: "inj_on pick V"
  proof (rule inj_onI)
    fix s t assume sV: "s \<in> V" and tV: "t \<in> V" and eq: "pick s = pick t"
    have iI: "pick s \<in> I" and sA: "s \<in> A (pick s)" using pickP[OF sV] by auto
    have tB: "t \<in> B (pick s)" using pickP[OF tV] eq by auto
    show "s = t" by (rule sound[OF iI sV tV sA tB])
  qed
  have sub: "pick ` V \<subseteq> I" using pickP by auto
  from card_inj_on_le[OF inj sub finI] show ?thesis .
qed

text \<open>Tightness: the card V singleton rules (one per token) cover the diagonal soundly, so the
      product-rule cost of equality is EXACTLY card V.\<close>
lemma equality_card_rules_suffice:
  fixes V :: "'t set"
  shows "(\<forall>t\<in>V. \<exists>i\<in>V. t \<in> {i} \<and> t \<in> {i}) \<and>
         (\<forall>i\<in>V. \<forall>t1\<in>V. \<forall>t2\<in>V. t1 \<in> {i} \<longrightarrow> t2 \<in> {i} \<longrightarrow> t1 = t2)"
  by auto

end
