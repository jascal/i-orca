(*
  RoutingRank.thy -- the routing-side rank bound: M generators move logits in an <=M-dim subspace.

  Companion / dual to DecodeCapacity.thy. A bank of M trainable rules contributes to the residual
  r += sum_k h_k(z) * Bdir_k; read out to logits this is sum_k h_k(z) * a_k with a_k = U . Bdir_k a
  FIXED vector in logit space (independent of the input z). So whatever the input-dependent gates
  h_k(z) do, the rule logit-adjustment always lies in span{a_1,...,a_M}, a subspace of dimension <= M.

  This is the structural reason superposition is FORCED when the number of routing decisions n exceeds
  M: there are only M (in fact <= min(M,d)) dimensions of adjustment available, so n > M routing
  features must share them. It is the routing-side dual of DecodeCapacity's frame separation:

    DecodeCapacity : how many TOKENS can be gamma-separated in R^d            (frame side)
    RoutingRank    : the rule adjustments live in an <=M-dim subspace of R^V  (generator side)

  The RANK piece is provable pure linear algebra (here). The remaining INTERFERENCE piece -- how packing
  n features into this <=M-dim subspace degrades the margin (a Welch/coherence DEGRADATION bound, not a
  count floor) -- is the open routing-side Welch conjecture; consistent with the measured sub-linear M.
*)
theory RoutingRank
  imports "HOL-Analysis.Analysis"
begin

text \<open>The input-dependent rule adjustment is a linear combination of the M fixed readout vectors
      @{term "a ` I"}, hence lies in their span.\<close>
lemma routing_adjustment_in_span:
  fixes a :: "nat \<Rightarrow> 'a::euclidean_space"
  shows "(\<Sum>i\<in>I. h i *\<^sub>R a i) \<in> span (a ` I)"
proof (rule span_sum)
  fix i assume "i \<in> I"
  hence "a i \<in> span (a ` I)" by (simp add: span_base)
  thus "h i *\<^sub>R a i \<in> span (a ` I)" by (rule span_scale)
qed

text \<open>That span has dimension at most M = card I: the rules can only move logits within an
      <=M-dimensional subspace, independent of the number of routing decisions.\<close>
lemma routing_rank_le:
  fixes a :: "nat \<Rightarrow> 'a::euclidean_space"
  assumes "finite I"
  shows "dim (span (a ` I)) \<le> card I"
proof -
  have "dim (span (a ` I)) = dim (a ` I)" by (rule dim_span)
  also have "\<dots> \<le> card (a ` I)" by (rule dim_le_card'[OF finite_imageI[OF assms]])
  also have "\<dots> \<le> card I" using assms by (rule card_image_le)
  finally show ?thesis .
qed

text \<open>Combined: every rule adjustment lives in a fixed subspace of dimension <= M. Superposition is
      forced when the number of routing features exceeds M (the generator-side capacity).\<close>
theorem routing_superposition:
  fixes a :: "nat \<Rightarrow> 'a::euclidean_space"
  assumes "finite I"
  shows "(\<Sum>i\<in>I. h i *\<^sub>R a i) \<in> span (a ` I) \<and> dim (span (a ` I)) \<le> card I"
  using routing_adjustment_in_span routing_rank_le[OF assms] by blast

end
