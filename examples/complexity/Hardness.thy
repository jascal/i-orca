theory Hardness
  imports Separation
begin

text \<open>WIP (branch complexity/irreducibility-hardness): the decision-complexity of
  IRREDUCIBILITY. Reduction/gadget correctness is Isabelle-shaped (below); the
  poly-time + completeness wrapper is a paper-level meta-claim, not formalised.
  See PROPOSAL.md.\<close>

text \<open>--- Margin reformulation: deciding = positivity of per-competitor margin sums. ---\<close>

definition margin :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "margin c t v j = c j t - c j v"

lemma decides_via_margin:
  "decides c P V t \<longleftrightarrow> (\<forall>v\<in>V. v \<noteq> t \<longrightarrow> 0 < (\<Sum>j\<in>P. margin c t v j))"
  by (simp add: decides_def margin_def sum_subtractf)

text \<open>--- Route B base case (single competitor). With exactly one competitor the
  full-deciding token is ALWAYS reducible; hence IRREDUCIBLE \<Longrightarrow> at least two
  competitors. Proof: the positive-margin sources already dominate the full sum. ---\<close>

lemma single_competitor_reducible:
  assumes dec: "decides c S {t, w} t" and wt: "w \<noteq> t" and card2: "2 \<le> card S"
  shows "\<not> irreducible c S {t, w} t"
proof -
  have finS: "finite S" using card2 by (cases "finite S") simp_all
  have full: "0 < (\<Sum>j\<in>S. margin c t w j)" using dec wt by (simp add: decides_via_margin)
  define Pp where "Pp = {j\<in>S. 0 < margin c t w j}"
  have PpS: "Pp \<subseteq> S" by (auto simp: Pp_def)
  have "(\<Sum>j\<in>S. margin c t w j)
        = (\<Sum>j\<in>Pp. margin c t w j) + (\<Sum>j\<in>S - Pp. margin c t w j)"
    using PpS finS by (metis add.commute sum.subset_diff)
  moreover have "(\<Sum>j\<in>S - Pp. margin c t w j) \<le> 0"
    by (rule sum_nonpos) (auto simp: Pp_def)
  ultimately have ppPos: "0 < (\<Sum>j\<in>Pp. margin c t w j)" using full by simp
  have decPp: "decides c Pp {t, w} t" using wt ppPos by (auto simp: decides_via_margin)
  have Ppne: "Pp \<noteq> {}" proof assume "Pp = {}" thus False using ppPos by simp qed
  show ?thesis
  proof (cases "Pp = S")
    case False
    hence "Pp \<subset> S" using PpS by auto
    hence "has_suff_sub c S {t, w} t"
      unfolding has_suff_sub_def using Ppne decPp by (intro exI[of _ Pp]) simp
    thus ?thesis by (simp add: irreducible_def)
  next
    case True
    obtain j where jS: "j \<in> S" using card2 by fastforce
    have "0 < margin c t w j" using True jS by (auto simp: Pp_def)
    hence decj: "decides c {j} {t, w} t" using wt by (auto simp: decides_via_margin)
    have "card {j} \<noteq> card S" using card2 by simp
    hence "{j} \<subset> S" using jS by auto
    hence "has_suff_sub c S {t, w} t"
      unfolding has_suff_sub_def using decj by (intro exI[of _ "{j}"]) simp
    thus ?thesis by (simp add: irreducible_def)
  qed
qed

corollary irreducible_needs_two_competitors:
  assumes irr: "irreducible c S {t, w} t" and card2: "2 \<le> card S"
  shows "w = t"
proof (rule ccontr)
  assume "w \<noteq> t"
  moreover have "decides c S {t, w} t" using irr by (simp add: irreducible_def)
  ultimately have "\<not> irreducible c S {t, w} t"
    using card2 single_competitor_reducible by blast
  thus False using irr by simp
qed

text \<open>--- Route A (NP-hardness gadget) — TARGET, not yet formalised. ---

  Reduce PARTITION (positive weights ws on S summing to 2W; is there a half summing
  to exactly W?) to REDUCIBILITY. Define a parametric c_red with two competitors
  whose opposite-signed margins encode  \<Sum>(j\<in>P) ws j = W , plus an anchor source
  to fake the missing additive constant (the margin constraints are homogeneous).
  Correctness target:
      irreducible c_red S V t  \<longleftrightarrow>  \<not> (\<exists>A. A \<noteq> {} \<and> A \<subset> S \<and> (\<Sum>j\<in>A. ws j) = W).
  The "poly-time" half of NP-hardness is the paper-level meta-claim.

  --- Route B (poly for bounded #competitors) — TARGET. ---

  Conjecture: for |V| \<le> K fixed, REDUCIBLE is decidable in poly time. Base cases:
  K = 1 above (always reducible); n \<le> 3 exact on main. General K: a decision
  procedure + correctness, or the sharp K where hardness begins. This dichotomy in
  K is, we suspect, the real answer and the interpretability-relevant one.\<close>

end
