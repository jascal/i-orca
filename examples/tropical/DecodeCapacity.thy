(*
  DecodeCapacity.thy -- the decision-side capacity bound: confident decoding forces separated frames.

  The LLM decode is argmax_v (<r,U_v> + b_v).  Call token v "gamma-decodable over the unit ball" if
  there is some residual r with norm <= 1 at which v beats every competitor by at least gamma.  We prove,
  in any real inner-product space:

    margin_pair_separation : if v and w are each gamma-decodable (v at r_v, w at r_w, both in the unit
                             ball), then ||U_v - U_w|| >= gamma -- the bias CANCELS (add the two witness
                             inequalities; the cross term is <r_v - r_w, U_v - U_w>, bounded by Cauchy-
                             Schwarz and ||r_v - r_w|| <= 2).

    decode_capacity_separated / head_capacity : hence the set of gamma-decodable tokens (in particular any
                             certifiable HEAD, cf. HeadTail.thy) has gamma-separated direction images -- it
                             is a gamma-code in R^d, so its cardinality is bounded by the packing number
                             (1 + 2 rho / gamma)^d (rho = max ||U_v||).  Decision-side sibling of the Welch
                             bound; the formal "structure is the hard limit" -- no frame tuning or rule
                             allocation yields more than a bounded number of cleanly-separable decodes
                             without raising the (effective) dimension (= tau* = min(exp H, d)).

  Ties to HeadTail.thy (the certifiable head is gamma-decodable, hence gamma-separated, hence bounded).
*)
theory DecodeCapacity
  imports "HOL-Analysis.Analysis"
begin

text \<open>Token @{term v} beats every competitor by at least @{term \<gamma>} at residual @{term r}.\<close>
definition gdecodes :: "('v \<Rightarrow> 'a::real_inner) \<Rightarrow> ('v \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> 'v \<Rightarrow> 'a \<Rightarrow> bool" where
  "gdecodes U b \<gamma> v r \<longleftrightarrow> (\<forall>w. w \<noteq> v \<longrightarrow> inner r (U w) + b w + \<gamma> \<le> inner r (U v) + b v)"

text \<open>Tokens that are gamma-decodable somewhere in the unit ball.\<close>
definition gdecodable :: "('v \<Rightarrow> 'a::real_inner) \<Rightarrow> ('v \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> 'v set" where
  "gdecodable U b \<gamma> = {v. \<exists>r. norm r \<le> 1 \<and> gdecodes U b \<gamma> v r}"

text \<open>The core: two gamma-decodable tokens have gamma-separated direction vectors (bias-free).\<close>
theorem margin_pair_separation:
  fixes U :: "'v \<Rightarrow> 'a::real_inner"
  assumes v: "gdecodes U b \<gamma> v rv" and w: "gdecodes U b \<gamma> w rw"
      and nv: "norm rv \<le> 1" and nw: "norm rw \<le> 1" and vw: "v \<noteq> w"
  shows "\<gamma> \<le> norm (U v - U w)"
proof -
  have v1: "inner rv (U w) + b w + \<gamma> \<le> inner rv (U v) + b v"
    using v[unfolded gdecodes_def, rule_format, of w] vw by simp
  have w1: "inner rw (U v) + b v + \<gamma> \<le> inner rw (U w) + b w"
    using w[unfolded gdecodes_def, rule_format, of v] vw by simp
  \<comment> \<open>add the two witnesses; biases cancel and the cross term collapses\<close>
  have eq: "inner (rv - rw) (U v - U w)
            = (inner rv (U v) - inner rv (U w)) + (inner rw (U w) - inner rw (U v))"
    by (simp add: inner_diff_left inner_diff_right algebra_simps)
  have key: "2 * \<gamma> \<le> inner (rv - rw) (U v - U w)"
    using v1 w1 eq by linarith
  \<comment> \<open>Cauchy-Schwarz, fully instantiated, then the triangle bound on the residual difference\<close>
  have cs: "inner (rv - rw) (U v - U w) \<le> norm (rv - rw) * norm (U v - U w)"
    by (rule norm_cauchy_schwarz)
  have nrw: "norm (rv - rw) \<le> 2"
    using nv nw norm_triangle_ineq4[of rv rw] by linarith
  have b2: "norm (rv - rw) * norm (U v - U w) \<le> 2 * norm (U v - U w)"
    by (rule mult_right_mono[OF nrw norm_ge_zero])
  from key cs b2 show ?thesis by linarith
qed

text \<open>Hence the gamma-decodable set is a gamma-separated code: any two members' frames are >= gamma apart.\<close>
corollary decode_capacity_separated:
  fixes U :: "'v \<Rightarrow> 'a::real_inner"
  assumes hv: "v \<in> gdecodable U b \<gamma>" and hw: "w \<in> gdecodable U b \<gamma>" and vw: "v \<noteq> w"
  shows "\<gamma> \<le> dist (U v) (U w)"
proof -
  from hv obtain rv where rv: "norm rv \<le> 1" "gdecodes U b \<gamma> v rv"
    unfolding gdecodable_def by blast
  from hw obtain rw where rw: "norm rw \<le> 1" "gdecodes U b \<gamma> w rw"
    unfolding gdecodable_def by blast
  have "\<gamma> \<le> norm (U v - U w)"
    by (rule margin_pair_separation[OF rv(2) rw(2) rv(1) rw(1) vw])
  thus ?thesis by (simp add: dist_norm)
qed

text \<open>The certifiable HEAD (any subset of gamma-decodable tokens, cf. HeadTail.head_certifies_decode) is a
      gamma-code in R^d: cardinality bounded by the gamma-packing number of the frame ball -- the decision-
      side sibling of the Welch bound.\<close>
corollary head_capacity:
  fixes U :: "'v \<Rightarrow> 'a::real_inner"
  assumes "S \<subseteq> gdecodable U b \<gamma>"
  shows "\<forall>v\<in>S. \<forall>w\<in>S. v \<noteq> w \<longrightarrow> \<gamma> \<le> dist (U v) (U w)"
proof (intro ballI impI)
  fix v w assume "v \<in> S" "w \<in> S" "v \<noteq> w"
  with assms have "v \<in> gdecodable U b \<gamma>" "w \<in> gdecodable U b \<gamma>" by auto
  thus "\<gamma> \<le> dist (U v) (U w)"
    by (rule decode_capacity_separated[OF _ _ \<open>v \<noteq> w\<close>])
qed

end
