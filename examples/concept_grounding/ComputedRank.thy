(*
  ComputedRank.thy -- C5: the computed-core rank lower bound.

  The conjecture: for a combining operation g realized by a linear readout over a residual confined to
  a subspace S, the needed dimension rho = dim S is bounded below by the rank of g's one-hot matrix
  M_g[x,v] = [g x = v].

  PREMISE STRENGTHENING (the honest part -- report per the work package). As stated over the pure
  ARGMAX decoder the conjecture is FALSE: with biases, argmax_v (v*t - v^2/2) over a 1-dim residual
  t computes nearest-integer -- unboundedly many outputs at rho = 1 -- and even the homogeneous argmax
  admits many outputs at rho = 2 (a fan of cones). What survives, and is proved here:

    * EXACT (calibrated) READOUT: if the readout scores are the one-hot targets themselves
      (W_v . r x = [g x = v] -- the interpolation regime the grounding probes fit), then
      card (g ` X) <= dim S. Since distinct one-hot rows are linearly independent,
      card (g ` X) IS rank M_g: the theorem is exactly rho >= rank M_g on the stated domain.
    * The degenerate direction: retrieval (constant g) is realizable at dim S <= 1 -- so the
      rank floor separates computation from lookup: >= 2 outputs force dim S >= 2 (exact readout).
    * The HOMOGENEOUS ARGMAX salvage: over a 1-dim residual subspace the bias-free argmax decoder
      attains at most THREE distinct decision sets (positive ray / zero / negative ray) -- the
      provable form of "rho = 1 is the lookup regime" for the decoder actually conjectured.
    * The addition anchor: g(x,y) = x + y on {0..<n}^2 attains 2n - 1 values, so exact readout of
      b-bit addition needs dim S >= 2^(b+1) - 1: the required rank GROWS with width. Whether any
      measured effective rank matches (the ~4 of tiny_math) stays `empirical` -- with argmax decoding
      the floor does not apply, which is precisely why low-rank addition heads can exist.

  Extends tropical/RoutingRank.thy ("M rules move logits in a <= M-dim subspace") from the routing
  side to the computed-function side. Domain: finite input set, linear readout, stated readout regime.
*)
theory ComputedRank
  imports ConceptCells
begin

subsection \<open>The exact-readout rank bound: card (g ` X) <= dim S\<close>

text \<open>If every residual lies in the subspace S and the readout is CALIBRATED -- the score of class v
      on input x is exactly the one-hot target [g x = v] -- then the number of distinct outputs of g
      is at most dim S. The witnesses r(x_y) for distinct outputs y are linearly independent inside S,
      because the reader functionals W_y separate them.\<close>
theorem computed_rank_lower_bound:
  fixes r :: "'x \<Rightarrow> 'a::euclidean_space" and W :: "'v \<Rightarrow> 'a" and g :: "'x \<Rightarrow> 'v"
  assumes finX: "finite X"
      and sub: "\<And>x. x \<in> X \<Longrightarrow> r x \<in> S"
      and gV: "g ` X \<subseteq> V"
      and exact: "\<And>x v. x \<in> X \<Longrightarrow> v \<in> V \<Longrightarrow> W v \<bullet> r x = (if g x = v then 1 else 0)"
  shows "card (g ` X) \<le> dim S"
proof -
  define wit where "wit y = (SOME x. x \<in> X \<and> g x = y)" for y
  have witX: "wit y \<in> X \<and> g (wit y) = y" if "y \<in> g ` X" for y
  proof -
    from that obtain x where x: "x \<in> X" and gx: "g x = y" by auto
    have "\<exists>z. z \<in> X \<and> g z = y" by (intro exI[of _ x] conjI x gx)
    from someI_ex[OF this] show ?thesis unfolding wit_def .
  qed
  have reader: "W y \<bullet> r (wit z) = (if z = y then 1 else 0)"
    if y: "y \<in> g ` X" and z: "z \<in> g ` X" for y z
  proof -
    have "W y \<bullet> r (wit z) = (if g (wit z) = y then 1 else 0)"
      by (rule exact) (use witX[OF z] gV y in auto)
    thus ?thesis using witX[OF z] by simp
  qed
  have inj: "inj_on (\<lambda>y. r (wit y)) (g ` X)"
  proof (rule inj_onI)
    fix y z assume y: "y \<in> g ` X" and z: "z \<in> g ` X" and eq: "r (wit y) = r (wit z)"
    show "y = z"
    proof (rule ccontr)
      assume ne: "y \<noteq> z"
      have "W y \<bullet> r (wit y) = 1" using reader[OF y y] by simp
      hence "W y \<bullet> r (wit z) = 1" unfolding eq .
      moreover have "W y \<bullet> r (wit z) = 0"
        using reader[OF y z] ne by simp
      ultimately show False by simp
    qed
  qed
  define R where "R = (\<lambda>y. r (wit y)) ` (g ` X)"
  have finR: "finite R" using finX unfolding R_def by auto
  have RS: "R \<subseteq> S" using sub witX unfolding R_def by auto
  have indep: "independent R"
  proof (rule independent_if_scalars_zero[OF finR])
    fix f :: "'a \<Rightarrow> real" and w
    assume sum0: "(\<Sum>v\<in>R. f v *\<^sub>R v) = 0" and wR: "w \<in> R"
    obtain y where y: "y \<in> g ` X" and w: "w = r (wit y)" using wR unfolding R_def by auto
    have "0 = W y \<bullet> (\<Sum>v\<in>R. f v *\<^sub>R v)" using sum0 by simp
    also have "\<dots> = (\<Sum>v\<in>R. f v * (W y \<bullet> v))"
      by (simp add: inner_sum_right)
    also have "\<dots> = (\<Sum>z\<in>g ` X. f (r (wit z)) * (W y \<bullet> r (wit z)))"
      unfolding R_def by (rule sum.reindex_cong[OF inj refl]) simp
    also have "\<dots> = (\<Sum>z\<in>g ` X. if z = y then f (r (wit z)) else 0)"
      by (rule sum.cong[OF refl]) (simp add: reader y)
    also have "\<dots> = f (r (wit y))"
      using y finite_imageI[OF finX, of g] by (simp add: sum.delta)
    finally show "f w = 0" using w by simp
  qed
  have "card (g ` X) = card R"
    unfolding R_def by (rule card_image[symmetric, OF inj])
  also have "\<dots> \<le> dim S" using RS indep by (rule independent_card_le_dim)
  finally show ?thesis .
qed

subsection \<open>The degenerate case: retrieval is rank one\<close>

text \<open>A constant decision (pure lookup) is realizable with an exactly calibrated readout over a
      ONE-dimensional residual subspace: the converse boundary of the rank floor.\<close>
theorem retrieval_rank_one:
  fixes y0 :: 'v and X :: "'x set" and V :: "'v set"
  shows "\<exists>(S::'a::euclidean_space set) r W.
           dim S \<le> 1 \<and> (\<forall>x\<in>X. r x \<in> S) \<and>
           (\<forall>x\<in>X. \<forall>v\<in>V. W v \<bullet> r x = (if y0 = v then 1 else 0))"
proof -
  define e :: 'a where "e = (SOME i. i \<in> Basis)"
  have eB: "e \<in> Basis" unfolding e_def by (rule SOME_Basis)
  have ee: "e \<bullet> e = 1" using eB by (simp add: inner_Basis)
  define S :: "'a set" where "S = span {e}"
  define r :: "'x \<Rightarrow> 'a" where "r = (\<lambda>x. e)"
  define W :: "'v \<Rightarrow> 'a" where "W = (\<lambda>v. if v = y0 then e else 0)"
  have "dim S \<le> 1"
  proof -
    have "dim S = dim {e}" unfolding S_def by (rule dim_span)
    also have "\<dots> \<le> card {e}" by (rule dim_le_card') simp
    finally show ?thesis by simp
  qed
  moreover have "\<forall>x\<in>X. r x \<in> S" unfolding r_def S_def by (simp add: span_base)
  moreover have "\<forall>x\<in>X. \<forall>v\<in>V. W v \<bullet> r x = (if y0 = v then 1 else 0)"
    unfolding W_def r_def using ee by auto
  ultimately show ?thesis by blast
qed

text \<open>Constancy is exactly the one-output case: on a nonempty finite input set, g is constant iff
      its image has cardinality one -- so the rank floor reads "computation = rank at least two".\<close>
lemma constant_iff_card_one:
  assumes "finite X" and "X \<noteq> {}"
  shows "card (g ` X) = 1 \<longleftrightarrow> (\<exists>y. \<forall>x\<in>X. g x = y)"
proof
  assume "card (g ` X) = 1"
  then obtain y where "g ` X = {y}" by (auto simp: card_1_singleton_iff)
  thus "\<exists>y. \<forall>x\<in>X. g x = y" by auto
next
  assume "\<exists>y. \<forall>x\<in>X. g x = y"
  then obtain y where y: "\<forall>x\<in>X. g x = y" by auto
  obtain x where x: "x \<in> X" using assms(2) by auto
  have "g ` X = {y}"
  proof
    show "g ` X \<subseteq> {y}" using y by auto
    show "{y} \<subseteq> g ` X" using y x by force
  qed
  thus "card (g ` X) = 1" by simp
qed

text \<open>Any genuine dependence -- two inputs with different outputs -- forces at least two residual
      dimensions under exact readout: the provable core of "rho > 1 for non-degenerate g".\<close>
corollary computation_needs_rank_two:
  fixes r :: "'x \<Rightarrow> 'a::euclidean_space"
  assumes finX: "finite X"
      and sub: "\<And>x. x \<in> X \<Longrightarrow> r x \<in> S"
      and gV: "g ` X \<subseteq> V"
      and exact: "\<And>x v. x \<in> X \<Longrightarrow> v \<in> V \<Longrightarrow> W v \<bullet> r x = (if g x = v then 1 else 0)"
      and x12: "x1 \<in> X" "x2 \<in> X" "g x1 \<noteq> g x2"
  shows "2 \<le> dim S"
proof -
  have "(2::nat) = card {g x1, g x2}" using x12(3) by simp
  also have "\<dots> \<le> card (g ` X)"
    using x12(1,2) finX by (intro card_mono finite_imageI) auto
  finally have "2 \<le> card (g ` X)" .
  also have "\<dots> \<le> dim S" by (rule computed_rank_lower_bound[OF finX sub gV exact])
  finally show ?thesis .
qed

subsection \<open>The homogeneous-argmax salvage: one dimension gives at most three behaviors\<close>

text \<open>Positive scaling never changes the bias-free argmax.\<close>
lemma amax_scaleR:
  assumes "0 < c"
  shows "amax V W (c *\<^sub>R y) = amax V W y"
proof -
  have "(W w \<bullet> (c *\<^sub>R y) \<le> W v \<bullet> (c *\<^sub>R y)) \<longleftrightarrow> (W w \<bullet> y \<le> W v \<bullet> y)" for v w
    using assms by (simp add: inner_scaleR_right)
  thus ?thesis unfolding amax_def by blast
qed

lemma amax_zero: "amax V W 0 = V"
  unfolding amax_def by simp

text \<open>Over a one-dimensional residual subspace the homogeneous argmax decoder realizes at most
      three distinct decision sets: the two rays and the origin. This is the true form of C5's
      "rho = 1 is the retrieval regime" for the argmax decoder as conjectured -- without the
      exact-readout strengthening the decoder at rank one is not constant, but it is 3-valued.\<close>
theorem argmax_rank_one_three_behaviors:
  fixes e :: "'a::real_inner" and r :: "'x \<Rightarrow> 'a"
  assumes sub: "\<And>x. x \<in> X \<Longrightarrow> r x \<in> span {e}"
  shows "card ((\<lambda>x. amax V W (r x)) ` X) \<le> 3"
proof -
  have "(\<lambda>x. amax V W (r x)) ` X \<subseteq> {amax V W e, V, amax V W (- e)}"
  proof
    fix A assume "A \<in> (\<lambda>x. amax V W (r x)) ` X"
    then obtain x where x: "x \<in> X" and A: "A = amax V W (r x)" by auto
    obtain c where c: "r x = c *\<^sub>R e" using sub[OF x] by (auto simp: span_singleton)
    consider "0 < c" | "c = 0" | "c < 0" by linarith
    thus "A \<in> {amax V W e, V, amax V W (- e)}"
    proof cases
      case 1 thus ?thesis using A c by (simp add: amax_scaleR)
    next
      case 2 thus ?thesis using A c by (simp add: amax_zero)
    next
      case 3
      have negc: "0 < - c" using 3 by simp
      have "amax V W (r x) = amax V W ((- c) *\<^sub>R (- e))"
        using c by simp
      also have "\<dots> = amax V W (- e)" by (rule amax_scaleR[OF negc])
      finally show ?thesis using A by simp
    qed
  qed
  hence "card ((\<lambda>x. amax V W (r x)) ` X) \<le> card {amax V W e, V, amax V W (- e)}"
    by (rule card_mono[rotated]) simp
  also have "\<dots> \<le> 3" by (simp add: card_insert_le_m1)
  finally show ?thesis .
qed

subsection \<open>The addition anchor: the required rank grows with operand width\<close>

text \<open>Addition on {0..<n} x {0..<n} attains exactly 2n - 1 distinct outputs.\<close>
lemma add_range_card:
  assumes "0 < n"
  shows "card ((\<lambda>(x, y). x + y) ` ({0..<n} \<times> {0..<n})) = 2 * n - 1"
proof -
  have "(\<lambda>(x, y). x + y) ` ({0..<n} \<times> {0..<n}) = {0..<2 * n - 1}"
  proof
    show "(\<lambda>(x, y). x + y) ` ({0..<n} \<times> {0..<n}) \<subseteq> {0..<2 * n - 1}"
      using assms by auto
  next
    show "{0..<2 * n - 1} \<subseteq> (\<lambda>(x, y). x + y) ` ({0..<n} \<times> {0..<n})"
    proof
      fix k assume k: "k \<in> {0..<2 * n - 1}"
      show "k \<in> (\<lambda>(x, y). x + y) ` ({0..<n} \<times> {0..<n})"
      proof (cases "k < n")
        case True
        show ?thesis
          by (rule image_eqI[where x = "(k, 0)"]) (use True assms in auto)
      next
        case False
        show ?thesis
          by (rule image_eqI[where x = "(n - 1, k - (n - 1))"])
             (use k False assms in auto)
      qed
    qed
  qed
  thus ?thesis by simp
qed

text \<open>Hence exactly reading out the sum of two width-n operands needs at least 2n - 1 residual
      dimensions: for b-bit operands (n = 2^b) the floor 2^(b+1) - 1 grows exponentially with b.
      The tiny_math effective rank ~4 is consistent only because real models decode by argmax,
      where the floor provably does not apply (see the header and the 3-behavior theorem).\<close>
theorem addition_rank_grows:
  fixes r :: "nat \<times> nat \<Rightarrow> 'a::euclidean_space" and W :: "nat \<Rightarrow> 'a"
  assumes n: "0 < n"
      and sub: "\<And>x. x \<in> {0..<n} \<times> {0..<n} \<Longrightarrow> r x \<in> S"
      and gV: "(\<lambda>(x, y). x + y) ` ({0..<n} \<times> {0..<n}) \<subseteq> V"
      and exact: "\<And>x v. x \<in> {0..<n} \<times> {0..<n} \<Longrightarrow> v \<in> V \<Longrightarrow>
                    W v \<bullet> r x = (if fst x + snd x = v then 1 else 0)"
  shows "2 * n - 1 \<le> dim S"
proof -
  have "2 * n - 1 = card ((\<lambda>(x, y). x + y) ` ({0..<n} \<times> {0..<n}))"
    by (simp add: add_range_card[OF n])
  also have "\<dots> \<le> dim S"
  proof (rule computed_rank_lower_bound[OF _ sub gV])
    show "finite ({0..<n} \<times> {0..<n})" by simp
    show "\<And>x v. x \<in> {0..<n} \<times> {0..<n} \<Longrightarrow> v \<in> V \<Longrightarrow>
            W v \<bullet> r x = (if (case x of (a, c) \<Rightarrow> a + c) = v then 1 else 0)"
      using exact by (auto simp: case_prod_beta)
  qed
  finally show ?thesis .
qed

end
