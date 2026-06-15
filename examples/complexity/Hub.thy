theory Hub
  imports Hardness Density
begin

text \<open>Corrected hub / shared-core formalisation. Fixes in the draft:
  (a) undefined token_t / token_V / active_sources / fires_on -> use the verified
      `active_on`; (b) `decides` is NOT monotone, so route each token to its minimal
      decider M e (which decides), NOT M e \<union> H (adding hub neurons outside M e can
      break the decision); (c) missing finiteness; (d) MOST important: the
      cross-token disjointness condition does NOT enter the per-token density bound
      -- that bound is plain subadditivity, true for ANY H. Its real role is that the
      PRIVATE parts form pairwise-disjoint clean bits. We separate the two.\<close>

text \<open>(1) Per-token active-count bound: pure subadditivity. NO hub condition needed,
  and the token is routed to its own minimal decider M e (so it still decides).\<close>

lemma per_token_active_bound:
  assumes finM: "finite (M e)" and finH: "finite H"
  shows "card (active_on a \<theta> x (M e)) \<le> card H + card (M e - H)"
proof -
  have sub: "active_on a \<theta> x (M e) \<subseteq> M e" by (auto simp: active_on_def)
  have "(M e \<inter> H) \<union> (M e - H) = M e" by auto
  moreover have "(M e \<inter> H) \<inter> (M e - H) = {}" by auto
  ultimately have eq: "card (M e) = card (M e \<inter> H) + card (M e - H)"
    using finM by (metis card_Un_disjoint finite_Diff finite_Int)
  have "card (M e \<inter> H) \<le> card H" by (meson card_mono finH inf_le2)
  hence "card (M e) \<le> card H + card (M e - H)" using eq by simp
  moreover have "card (active_on a \<theta> x (M e)) \<le> card (M e)"
    using finM sub by (simp add: card_mono)
  ultimately show ?thesis by simp
qed

text \<open>(2) The disjointness condition's ACTUAL role: the private parts {M e - H} are
  pairwise disjoint, so they can be placed in separate clean bits (a valid partition).
  This is the disentangling content -- it is NOT what bounds the density above.\<close>

definition disjoint_private :: "(nat \<Rightarrow> nat set) \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> bool" where
  "disjoint_private M H Es \<longleftrightarrow>
     (\<forall>e1\<in>Es. \<forall>e2\<in>Es. e1 \<noteq> e2 \<longrightarrow> (M e1 - H) \<inter> (M e2 - H) = {})"

lemma disjoint_private_clean:
  assumes "disjoint_private M H Es" "e1 \<in> Es" "e2 \<in> Es" "e1 \<noteq> e2"
  shows "(M e1 - H) \<inter> (M e2 - H) = {}"
  using assms by (simp add: disjoint_private_def)

text \<open>Under disjoint_private the total DISTINCT private neurons across the sample is the
  SUM of the private sizes (no double-counting) -- this is where the disjointness pays,
  bounding the overall bit budget, not the per-token density.\<close>

lemma disjoint_private_card_Union:
  assumes dp: "disjoint_private M H Es" and fin: "finite Es"
      and finM: "\<And>e. e \<in> Es \<Longrightarrow> finite (M e)"
  shows "card (\<Union>e\<in>Es. (M e - H)) = (\<Sum>e\<in>Es. card (M e - H))"
  using fin
proof (rule card_UN_disjoint)
  show "\<forall>e\<in>Es. finite (M e - H)" using finM by simp
  show "\<forall>e1\<in>Es. \<forall>e2\<in>Es. e1 \<noteq> e2 \<longrightarrow> (M e1 - H) \<inter> (M e2 - H) = {}"
    using dp by (simp add: disjoint_private_def)
qed

text \<open>(3) GAP #3 -- the REALISTIC hub. Perfect disjointness (disjoint_private) is too
  strong for real models: private parts overlap. The honest condition is BOUNDED
  overlap -- every neuron lies in the private part (M e - H) of at most d tokens of the
  sample. disjoint_private is exactly the d = 1 case.\<close>

definition is_d_bounded_disentangling_hub ::
  "nat set \<Rightarrow> (nat \<Rightarrow> nat set) \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> bool" where
  "is_d_bounded_disentangling_hub H M Es d \<longleftrightarrow>
     (\<forall>j. card {e \<in> Es. j \<in> M e - H} \<le> d)"

text \<open>Helper: summing a 0/1 indicator over a finite set counts the satisfying elements.\<close>

lemma sum_ind_card:
  assumes finA: "finite A"
  shows "(\<Sum>x\<in>A. if P x then (1::nat) else 0) = card {x\<in>A. P x}"
proof -
  have B: "{x\<in>A. P x} \<subseteq> A" by auto
  have "(\<Sum>x\<in>A. if P x then (1::nat) else 0) = (\<Sum>x\<in>{x\<in>A. P x}. if P x then 1 else 0)"
    by (rule sum.mono_neutral_right[OF finA B]) auto
  also have "\<dots> = (\<Sum>x\<in>{x\<in>A. P x}. 1)" by (rule sum.cong[OF refl]) auto
  also have "\<dots> = card {x\<in>A. P x}" by simp
  finally show ?thesis .
qed

text \<open>disjoint_private is the d = 1 instance: disjoint private parts put each neuron in
  at most one token's private part.\<close>

lemma disjoint_private_is_1_bounded:
  assumes dp: "disjoint_private M H Es"
  shows "is_d_bounded_disentangling_hub H M Es 1"
  unfolding is_d_bounded_disentangling_hub_def
proof (intro allI)
  fix j
  have sub: "\<And>x y. x \<in> {e\<in>Es. j \<in> M e - H} \<Longrightarrow> y \<in> {e\<in>Es. j \<in> M e - H} \<Longrightarrow> x = y"
  proof -
    fix x y assume x: "x \<in> {e\<in>Es. j \<in> M e - H}" and y: "y \<in> {e\<in>Es. j \<in> M e - H}"
    show "x = y"
    proof (rule ccontr)
      assume ne: "x \<noteq> y"
      have mem: "x \<in> Es" "y \<in> Es" "j \<in> M x - H" "j \<in> M y - H" using x y by auto
      hence "(M x - H) \<inter> (M y - H) = {}" using dp ne by (auto simp: disjoint_private_def)
      thus False using mem by auto
    qed
  qed
  have "{e\<in>Es. j \<in> M e - H} = {} \<or> (\<exists>z. {e\<in>Es. j \<in> M e - H} = {z})"
  proof (cases "{e\<in>Es. j \<in> M e - H} = {}")
    case True
    thus ?thesis by blast
  next
    case False
    then obtain z where z: "z \<in> {e\<in>Es. j \<in> M e - H}" by blast
    have "{e\<in>Es. j \<in> M e - H} = {z}" using sub z by blast
    thus ?thesis by blast
  qed
  thus "card {e\<in>Es. j \<in> M e - H} \<le> 1"
  proof (elim disjE exE)
    assume h: "{e\<in>Es. j \<in> M e - H} = {}"
    have "card {e\<in>Es. j \<in> M e - H} = card ({}::nat set)" by (rule arg_cong[where f=card, OF h])
    thus "card {e\<in>Es. j \<in> M e - H} \<le> 1" by simp
  next
    fix z assume h: "{e\<in>Es. j \<in> M e - H} = {z}"
    have "card {e\<in>Es. j \<in> M e - H} = card {z}" by (rule arg_cong[where f=card, OF h])
    thus "card {e\<in>Es. j \<in> M e - H} \<le> 1" by simp
  qed
qed

text \<open>The d-bounded budget theorem: under d-bounded overlap, the naive SUM of private
  sizes overcounts the DISTINCT private union by at most a factor d. So the distinct
  private neuron budget is at least (1/d) of the sum -- the hub disentangles up to a
  factor d. At d = 1 this gives equality with disjoint_private_card_Union (the clean
  partition). Pure double-counting: sum over tokens of card = sum over neurons of the
  per-neuron token-multiplicity, which is at most d on each of the card(Union) neurons.\<close>

theorem d_bounded_private_budget:
  assumes hub: "is_d_bounded_disentangling_hub H M Es d"
      and finEs: "finite Es"
      and finM: "\<And>e. e \<in> Es \<Longrightarrow> finite (M e)"
  shows "(\<Sum>e\<in>Es. card (M e - H)) \<le> d * card (\<Union>e\<in>Es. (M e - H))"
proof -
  define U where U_def: "U = (\<Union>e\<in>Es. (M e - H))"
  have finU: "finite U"
    unfolding U_def
  proof (rule finite_UN_I[OF finEs])
    fix e assume "e \<in> Es" thus "finite (M e - H)" using finM by (blast intro: finite_Diff)
  qed
  \<comment> \<open>each token's private count, expanded as an indicator sum over the distinct union\<close>
  have inner_e: "\<And>e. e \<in> Es \<Longrightarrow>
      (\<Sum>j\<in>U. if j \<in> M e - H then (1::nat) else 0) = card (M e - H)"
  proof -
    fix e assume e: "e \<in> Es"
    have subU: "M e - H \<subseteq> U" using e by (auto simp: U_def)
    have "(\<Sum>j\<in>U. if j \<in> M e - H then (1::nat) else 0) = card {j\<in>U. j \<in> M e - H}"
      by (rule sum_ind_card[OF finU])
    also have "{j\<in>U. j \<in> M e - H} = M e - H" using subU by auto
    finally show "(\<Sum>j\<in>U. if j \<in> M e - H then (1::nat) else 0) = card (M e - H)" .
  qed
  \<comment> \<open>each neuron's token-multiplicity, expanded as an indicator sum over the sample\<close>
  have inner_j: "\<And>j. (\<Sum>e\<in>Es. if j \<in> M e - H then (1::nat) else 0) = card {e\<in>Es. j \<in> M e - H}"
    by (rule sum_ind_card[OF finEs])
  have "(\<Sum>e\<in>Es. card (M e - H))
        = (\<Sum>e\<in>Es. (\<Sum>j\<in>U. if j \<in> M e - H then (1::nat) else 0))"
  proof (rule sum.cong[OF refl])
    fix e assume "e \<in> Es"
    thus "card (M e - H) = (\<Sum>j\<in>U. if j \<in> M e - H then (1::nat) else 0)"
      using inner_e[OF \<open>e \<in> Es\<close>] by simp
  qed
  also have "\<dots> = (\<Sum>j\<in>U. (\<Sum>e\<in>Es. if j \<in> M e - H then (1::nat) else 0))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>j\<in>U. card {e\<in>Es. j \<in> M e - H})"
  proof (rule sum.cong[OF refl])
    fix j assume "j \<in> U"
    show "(\<Sum>e\<in>Es. if j \<in> M e - H then (1::nat) else 0) = card {e\<in>Es. j \<in> M e - H}"
      by (rule inner_j)
  qed
  also have "\<dots> \<le> (\<Sum>j\<in>U. d)"
  proof (rule sum_mono)
    fix j assume "j \<in> U"
    show "card {e\<in>Es. j \<in> M e - H} \<le> d"
      using hub[unfolded is_d_bounded_disentangling_hub_def] by blast
  qed
  also have "\<dots> = card U * d" by simp
  also have "\<dots> = d * card U" by (simp add: mult.commute)
  finally show ?thesis unfolding U_def .
qed

text \<open>At d = 1, bounded overlap is disjointness and the budget bound becomes the
  equality already proved (distinct union = sum), recovering disjoint_private_card_Union.\<close>

corollary d1_bounded_budget_is_partition:
  assumes dp: "disjoint_private M H Es" and finEs: "finite Es"
      and finM: "\<And>e. e \<in> Es \<Longrightarrow> finite (M e)"
  shows "(\<Sum>e\<in>Es. card (M e - H)) = card (\<Union>e\<in>Es. (M e - H))"
  using disjoint_private_card_Union[OF dp finEs finM] by simp

end
