theory Hardness_RouteB
  imports Hardness
begin

text \<open>Route B, K = 2 (two competitors). This CORRECTS and simplifies the draft
  k2_reducible_char: the "both-positive" (pp) and "both-negative" (mm) sign classes
  give clean, UNCONDITIONAL reducibility (proved below); only the residual pm/mp-only
  case (pp = mm = {}) is the genuine pseudo-poly core. The kernel-checked c4 example
  (Characterization.thy) lives precisely in that residual case and is reducible via a
  balancing pair — exactly where no simple sign test decides.\<close>

definition pp where
  "pp c t v1 v2 S = {j\<in>S. 0 < margin c t v1 j \<and> 0 < margin c t v2 j}"
definition mm where
  "mm c t v1 v2 S = {j\<in>S. margin c t v1 j < 0 \<and> margin c t v2 j < 0}"

lemma decides_k2:
  "decides c P {t, v1, v2} t \<longleftrightarrow>
     (v1 \<noteq> t \<longrightarrow> 0 < (\<Sum>j\<in>P. margin c t v1 j))
   \<and> (v2 \<noteq> t \<longrightarrow> 0 < (\<Sum>j\<in>P. margin c t v2 j))"
  by (auto simp: decides_via_margin)

text \<open>(1) A both-positive source class already decides, so pp \<noteq> {} \<Longrightarrow> reducible.\<close>

lemma pp_decides:
  assumes finS: "finite S" and v1: "v1 \<noteq> t" and v2: "v2 \<noteq> t"
      and ne: "pp c t v1 v2 S \<noteq> {}"
  shows "decides c (pp c t v1 v2 S) {t, v1, v2} t"
proof -
  have fin: "finite (pp c t v1 v2 S)" using finS by (simp add: pp_def)
  have "0 < (\<Sum>j\<in>pp c t v1 v2 S. margin c t v1 j)"
    using ne fin by (intro sum_pos) (auto simp: pp_def)
  moreover have "0 < (\<Sum>j\<in>pp c t v1 v2 S. margin c t v2 j)"
    using ne fin by (intro sum_pos) (auto simp: pp_def)
  ultimately show ?thesis using v1 v2 by (simp add: decides_k2)
qed

lemma pp_nonempty_reducible:
  assumes finS: "finite S" and card2: "2 \<le> card S"
      and v1: "v1 \<noteq> t" and v2: "v2 \<noteq> t" and ne: "pp c t v1 v2 S \<noteq> {}"
  shows "has_suff_sub c S {t, v1, v2} t"
proof (cases "pp c t v1 v2 S = S")
  case False
  hence "pp c t v1 v2 S \<subset> S" by (auto simp: pp_def)
  thus ?thesis unfolding has_suff_sub_def
    using ne pp_decides[OF finS v1 v2 ne] by (intro exI[of _ "pp c t v1 v2 S"]) simp
next
  case True
  obtain j where jS: "j \<in> S" using card2 by fastforce
  have "0 < margin c t v1 j" "0 < margin c t v2 j" using True jS by (auto simp: pp_def)
  hence decj: "decides c {j} {t, v1, v2} t" using v1 v2 by (simp add: decides_k2)
  have "card {j} \<noteq> card S" using card2 by simp
  hence "{j} \<subset> S" using jS by auto
  thus ?thesis unfolding has_suff_sub_def using decj by (intro exI[of _ "{j}"]) simp
qed

text \<open>(2) Dropping a both-negative source raises both sums, so mm \<noteq> {} \<Longrightarrow> reducible.\<close>

lemma mm_nonempty_reducible:
  assumes finS: "finite S" and card2: "2 \<le> card S"
      and v1: "v1 \<noteq> t" and v2: "v2 \<noteq> t"
      and dec: "decides c S {t, v1, v2} t" and ne: "mm c t v1 v2 S \<noteq> {}"
  shows "has_suff_sub c S {t, v1, v2} t"
proof -
  obtain m where mM: "m \<in> mm c t v1 v2 S" using ne by auto
  have mS: "m \<in> S" using mM by (simp add: mm_def)
  have neg1: "margin c t v1 m < 0" and neg2: "margin c t v2 m < 0"
    using mM by (auto simp: mm_def)
  have d1: "0 < (\<Sum>j\<in>S. margin c t v1 j)" and d2: "0 < (\<Sum>j\<in>S. margin c t v2 j)"
    using dec v1 v2 by (simp_all add: decides_k2)
  have "(\<Sum>j\<in>S. margin c t v1 j) = margin c t v1 m + (\<Sum>j\<in>S - {m}. margin c t v1 j)"
    using mS finS by (metis sum.remove)
  hence p1: "0 < (\<Sum>j\<in>S - {m}. margin c t v1 j)" using d1 neg1 by simp
  have "(\<Sum>j\<in>S. margin c t v2 j) = margin c t v2 m + (\<Sum>j\<in>S - {m}. margin c t v2 j)"
    using mS finS by (metis sum.remove)
  hence p2: "0 < (\<Sum>j\<in>S - {m}. margin c t v2 j)" using d2 neg2 by simp
  have decR: "decides c (S - {m}) {t, v1, v2} t" using p1 p2 v1 v2 by (simp add: decides_k2)
  have "0 < card (S - {m})" using mS finS card2 by (simp add: card_Diff_subset)
  hence ne': "S - {m} \<noteq> {}" by force
  have "S - {m} \<subset> S" using mS by auto
  thus ?thesis unfolding has_suff_sub_def using ne' decR by (intro exI[of _ "S - {m}"]) simp
qed

text \<open>So for K = 2 the only configuration where reducibility is NOT settled by a
  one-pass sign test is pp = mm = {} (every source strictly mixed: pm or mp). That
  residual case is the genuine 2-dimensional balancing problem and the locus of the
  pseudo-poly DP. It is exactly where the irreducible witnesses live:
  the n = 2 pair (irreducible_pair) is 1 pm + 1 mp; the reducible n = 4 c4 is
  2 pm + 2 mp where a sub-pair re-balances. Whether REDUCIBLE restricted to the
  fixed K = 2 mixed case is strongly-poly, only pseudo-poly, or already weakly
  NP-hard is the sharp open sub-problem (Grok's K0 question).\<close>

end
