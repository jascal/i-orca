(*
  Consolidation.thy -- C4: consolidation subspace-preservation = the stability-plasticity rank tradeoff.

  The wake_sleep grounding experiment freezes a subset F of concepts (their direction u_c and bias b_c)
  and lets the rest P = K - F keep training under gradient masking. This theory proves the geometry that
  the experiment's stability-plasticity band measures:

    (i)   frozen memberships are invariant under ANY masked update -- and by induction under an entire
          training trajectory of masked steps, not just one;
    (ii)  every decision that reads only frozen memberships is preserved EXACTLY, for every residual
          simultaneously (zero forgetting on the frozen code);
    (iii) whatever the plastic updates do, the change of the concept frame spans a subspace of dimension
          <= card (K - F) = |P|; the new-task boundary normals likewise span <= |P| dimensions;
    (cor) retain-rank + learn-rank <= K -- freezing a k-dim frame caps new learning at K - k dims.

  Statements are over the stated domain (finite concept set, half-space memberships, exact parameter
  masking); the bridge to any real model's training run stays `empirical`/`open`. The rank pieces are the
  consolidation-side siblings of tropical/RoutingRank.thy's "M generators move logits in <= M dims".
*)
theory Consolidation
  imports "HOL-Analysis.Analysis"
begin

text \<open>Concept membership: concept c fires on residual r iff the linear score clears the bias --
      the half-space code of the grounding experiments.\<close>
definition fires :: "('c \<Rightarrow> 'a::real_inner) \<Rightarrow> ('c \<Rightarrow> real) \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> bool" where
  "fires u b c r \<longleftrightarrow> b c \<le> u c \<bullet> r"

text \<open>Gradient masking, abstracted: an update is masked on F iff it leaves every frozen concept's
      parameters (direction and bias) untouched. Nothing is assumed about what it does off F.\<close>
definition masked :: "'c set \<Rightarrow> ('c \<Rightarrow> 'a::real_inner) \<Rightarrow> ('c \<Rightarrow> real) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> real) \<Rightarrow> bool" where
  "masked F u b u' b' \<longleftrightarrow> (\<forall>c\<in>F. u' c = u c \<and> b' c = b c)"

subsection \<open>(i) Frozen memberships are invariant\<close>

lemma frozen_membership_invariant:
  assumes "masked F u b u' b'" and "c \<in> F"
  shows "fires u' b' c = fires u b c"
  using assms unfolding masked_def fires_def by (simp add: fun_eq_iff)

text \<open>The trajectory form: a whole training run of masked steps leaves every frozen membership
      function identical to its initial state -- invariance under all subsequent training.\<close>
lemma frozen_membership_trajectory:
  assumes steps: "\<And>n. n < N \<Longrightarrow> masked F (u n) (b n) (u (Suc n)) (b (Suc n))"
      and "c \<in> F"
  shows "fires (u N) (b N) c = fires (u 0) (b 0) c"
  using steps
proof (induction N)
  case 0 show ?case by simp
next
  case (Suc N)
  have "fires (u (Suc N)) (b (Suc N)) c = fires (u N) (b N) c"
    using Suc.prems \<open>c \<in> F\<close> by (intro frozen_membership_invariant[of F]) auto
  also have "\<dots> = fires (u 0) (b 0) c" using Suc by auto
  finally show ?case .
qed

subsection \<open>(ii) Frozen decisions are preserved exactly\<close>

text \<open>Any decision D that is a function only of the frozen memberships returns the same value on
      every residual after any masked update: zero forgetting on the frozen code, exactly.\<close>
lemma frozen_decision_preserved:
  fixes D :: "('c \<Rightarrow> bool) \<Rightarrow> 'y"
  assumes "masked F u b u' b'"
  shows "D (restrict (\<lambda>c. fires u' b' c r) F) = D (restrict (\<lambda>c. fires u b c r) F)"
proof -
  have "restrict (\<lambda>c. fires u' b' c r) F = restrict (\<lambda>c. fires u b c r) F"
    using assms unfolding masked_def fires_def restrict_def by (simp add: fun_eq_iff)
  thus ?thesis by simp
qed

subsection \<open>(iii) The reachable change is confined to the plastic span\<close>

text \<open>The frame update u' - u vanishes on F, so across ALL concepts it spans at most
      card (K - F) = number-of-plastic-concepts dimensions.\<close>
lemma reachable_change_dim:
  fixes u u' :: "'c \<Rightarrow> 'a::euclidean_space"
  assumes fin: "finite K" and msk: "masked F u b u' b'" and sub: "F \<subseteq> K"
  shows "dim (span ((\<lambda>c. u' c - u c) ` K)) \<le> card (K - F)"
proof -
  have "(\<lambda>c. u' c - u c) ` K \<subseteq> insert 0 ((\<lambda>c. u' c - u c) ` (K - F))"
    using msk unfolding masked_def by auto
  hence "span ((\<lambda>c. u' c - u c) ` K) \<subseteq> span (insert 0 ((\<lambda>c. u' c - u c) ` (K - F)))"
    by (rule span_mono)
  also have "span (insert 0 ((\<lambda>c. u' c - u c) ` (K - F))) = span ((\<lambda>c. u' c - u c) ` (K - F))"
    by (rule span_insert_0)
  finally have "dim (span ((\<lambda>c. u' c - u c) ` K)) \<le> dim (span ((\<lambda>c. u' c - u c) ` (K - F)))"
    by (rule dim_subset)
  also have "\<dots> = dim ((\<lambda>c. u' c - u c) ` (K - F))" by (rule dim_span)
  also have "\<dots> \<le> card ((\<lambda>c. u' c - u c) ` (K - F))"
    by (rule dim_le_card'[OF finite_imageI]) (use fin in auto)
  also have "\<dots> \<le> card (K - F)" using fin by (intro card_image_le) auto
  finally show ?thesis .
qed

text \<open>Any bank of directions indexed by a finite set spans at most that many dimensions -- applied
      to the plastic concepts, the new-task decision boundaries live in a <= card P dim subspace.\<close>
lemma plastic_boundary_dim:
  fixes u' :: "'c \<Rightarrow> 'a::euclidean_space"
  assumes "finite P"
  shows "dim (span (u' ` P)) \<le> card P"
proof -
  have "dim (span (u' ` P)) = dim (u' ` P)" by (rule dim_span)
  also have "\<dots> \<le> card (u' ` P)" by (rule dim_le_card'[OF finite_imageI[OF assms]])
  also have "\<dots> \<le> card P" using assms by (rule card_image_le)
  finally show ?thesis .
qed

subsection \<open>Corollary: the hard stability-plasticity budget\<close>

text \<open>retain-rank + learn-rank <= K. The frozen frame retains at most card F dimensions and the
      reachable change claims at most card (K - F); together they cannot exceed the concept budget K.
      Freezing a k-dim subspace preserves it exactly at the cost of capping new learning at K - k.\<close>
theorem retain_learn_budget:
  fixes u u' :: "'c \<Rightarrow> 'a::euclidean_space"
  assumes fin: "finite K" and sub: "F \<subseteq> K" and msk: "masked F u b u' b'"
  shows "dim (span (u ` F)) + dim (span ((\<lambda>c. u' c - u c) ` K)) \<le> card K"
proof -
  have finF: "finite F" using fin sub by (rule finite_subset[rotated])
  have "dim (span (u ` F)) \<le> card F" by (rule plastic_boundary_dim[OF finF])
  moreover have "dim (span ((\<lambda>c. u' c - u c) ` K)) \<le> card (K - F)"
    by (rule reachable_change_dim[OF fin msk sub])
  moreover have "card F + card (K - F) = card K"
    using fin sub by (metis card_Diff_subset card_mono finF le_add_diff_inverse)
  ultimately show ?thesis by linarith
qed

end
