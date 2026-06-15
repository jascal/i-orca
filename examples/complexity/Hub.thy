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

end
