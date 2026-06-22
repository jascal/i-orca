(*
  RoutingWelch.thy -- the routing-side Welch bound: interference among routing features in rule space.

  The third leg of the PIL "two-sided packing" story (the other two live in examples/tropical):

    DecodeCapacity (frame side)     : how many TOKENS can be gamma-separated in R^d
    RoutingRank    (generator rank) : M rules move logits within a rank-<=min(M,d) subspace of R^V
    RoutingWelch   (generator coh.) : the n realized ROUTING FEATURES live in rule-activation space R^M,
                                      so packing n > M of them forces Welch-bounded interference   <-- here

  A rule bank of M rules gives each input a rule-activation vector h(z) in R^M.  For each routing decision
  c (e.g. a synonym pair) the realized "routing feature" is f_c = E[h | A] - E[h | B] in R^M -- the
  direction in rule-activation space the model uses to make decision c.  There are n such features (one
  per decision) living in the m = M coordinates.  So this is EXACTLY the toy-models-of-superposition
  setup, with K = the M rule coordinates and I = the n routing decisions, and the proved Welch machinery
  (Welch.thy) applies verbatim:

    routing_capacity            : cross-talk-FREE routing (orthogonal features) needs M >= n rules.
    routing_forces_interference : n > M routing features force some interfering pair (superposition).
    routing_interference_welch  : total routing interference is at least n(n-M)/M.

  This is the generator-side analogue of DecodeCapacity's frame packing -- the SAME Welch bound, now on
  the rule-activation side -- and the quantitative form of RoutingRank's "superposition is forced when
  n > M".  It is honestly scoped to the COUNT/INTERFERENCE statement: that n > M forces coherence is
  proved here; the further step "coherence degrades the decode margin" is, empirically, MILD -- trained
  rules pack the features at ~the Welch floor with margins still healthy (PIL docs/notes/pil_learning_dynamics
  S5f) -- so it is left as the measured consequence, not asserted as a kernel theorem.
*)

theory RoutingWelch
  imports Welch
begin

text \<open>Cross-talk-free routing: if the @{term "card I"} routing features are orthonormal in the
      @{term "card K"}-dimensional rule-activation space, then there are at most as many decisions as
      rules -- you need M >= n rules to route n decisions with zero interference.\<close>
corollary routing_capacity:
  fixes f :: "'dec \<Rightarrow> 'rule \<Rightarrow> real"
  assumes "finite I" and "finite K"
      and "\<forall>i\<in>I. ip K (f i) (f i) = 1"
      and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> ip K (f i) (f j) = 0"
  shows "card I \<le> card K"
  using assms by (rule orth_capacity')

text \<open>Superposition is forced: more routing decisions than rules (@{term "card K < card I"}) makes some
      pair of routing features interfere -- the qualitative origin of routing cross-talk.\<close>
corollary routing_forces_interference:
  fixes f :: "'dec \<Rightarrow> 'rule \<Rightarrow> real"
  assumes "finite I" and "finite K"
      and "\<forall>i\<in>I. ip K (f i) (f i) = 1" and "card K < card I"
  shows "\<exists>i\<in>I. \<exists>j\<in>I. i \<noteq> j \<and> ip K (f i) (f j) \<noteq> 0"
  using assms by (rule superposition_forces_interference')

text \<open>The quantitative Welch bound on the routing side: the total squared interference among the n
      routing features in M rule-dimensions is at least n(n-M)/M -- strictly positive exactly when
      n > M, and growing as the rule bank is overpacked.\<close>
corollary routing_interference_welch:
  fixes f :: "'dec \<Rightarrow> 'rule \<Rightarrow> real"
  assumes "finite I" and "finite K" and "0 < card K"
      and "\<forall>i\<in>I. ip K (f i) (f i) = 1"
  shows "(\<Sum>i\<in>I. \<Sum>j\<in>I - {i}. (ip K (f i) (f j))\<^sup>2)
         \<ge> real (card I) * (real (card I) - real (card K)) / real (card K)"
  using assms by (rule welch_offdiag')

end
