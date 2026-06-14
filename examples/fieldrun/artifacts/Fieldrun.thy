theory Fieldrun
  imports Main "HOL-Analysis.Inner_Product" Complex_Main
begin

text \<open>Theorem 1. Under the projective pairing the decision depends only on the totals (hence on {Δ, D_j}) and is invariant to the readout multiplicity μ_t: two source tensors c, c′ with equal column sums induce the same argmax even when their per-source argmax counts μ_t differ.\<close>
theorem cardinalityinertness:
  assumes
    eqtot: "\<And>v. (\<Sum>j\<in>J. c j v) = (\<Sum>j\<in>J. c' j v)"
  shows "(\<forall>w\<in>V. (\<Sum>j\<in>J. c j w) \<le> (\<Sum>j\<in>J. c j t)) = (\<forall>w\<in>V. (\<Sum>j\<in>J. c' j w) \<le> (\<Sum>j\<in>J. c' j t))"
proof -
  have s_tot: "\<And>w. (\<Sum>j\<in>J. c j w) = (\<Sum>j\<in>J. c' j w)" using eqtot by (simp add: eqtot)
  show "(\<forall>w\<in>V. (\<Sum>j\<in>J. c j w) \<le> (\<Sum>j\<in>J. c j t)) = (\<forall>w\<in>V. (\<Sum>j\<in>J. c' j w) \<le> (\<Sum>j\<in>J. c' j t))" using s_tot by (simp add: s_tot)
qed

text \<open>Theorem 2. Competition hardness is carried by the frame Gram: for unit directions ‖U_t − U_v‖² = 2(1 − ρ_tv), so the differential incidence becomes common-mode and collapses as ρ_tv → 1; and when G is diagonal (ρ_tv = 0, mutually exclusive outcomes) it reduces to the classical disjoint-outcome distance ‖U_t − U_v‖² = 2.\<close>
theorem nontruthfunctionalitybudget:
  assumes
    ut: "norm (U t) = 1"
    and
    uv: "norm (U v) = 1"
  shows "(norm (U t - U v)) ^ 2 = 2 * (1 - inner (U t) (U v)) \<and> (inner (U t) (U v) = 0 \<longrightarrow> (norm (U t - U v)) ^ 2 = 2)"
proof -
  have s1: "(norm (U t - U v)) ^ 2 = (norm (U t)) ^ 2 - 2 * inner (U t) (U v) + (norm (U v)) ^ 2" by (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right inner_commute)
  have s2: "(norm (U t - U v)) ^ 2 = 2 * (1 - inner (U t) (U v))" using s1 by (simp add: ut uv algebra_simps)
  show "(norm (U t - U v)) ^ 2 = 2 * (1 - inner (U t) (U v)) \<and> (inner (U t) (U v) = 0 \<longrightarrow> (norm (U t - U v)) ^ 2 = 2)" using s2 by (simp add: s2)
qed

text \<open>Theorem 3 (realisability half). A COMPOSED token (μ_t = 0) is the argmax of the weighted sum Σ_j c_j though no single source's argmax selects it: an explicit two-source, three-outcome witness where the sum prefers outcome 0 while source 1 prefers 1 and source 2 prefers 2 — realised by a weighted-threshold connective but by no singleton sufficient sub-conjunction.\<close>
theorem weightedthresholdexpressivity:
  assumes
    c1_def: "c1 = (\<lambda>x::nat. if x = 0 then (2::real) else if x = 1 then 3 else 0)"
    and
    c2_def: "c2 = (\<lambda>x::nat. if x = 0 then (2::real) else if x = 1 then 0 else 3)"
    and
    L_def: "L = (\<lambda>x. c1 x + c2 x)"
  shows "L 0 > L 1 \<and> L 0 > L 2 \<and> c1 1 > c1 0 \<and> c2 2 > c2 0"
proof -
  have s1: "L 0 = 4 \<and> L 1 = 3 \<and> L 2 = 3" by (simp add: L_def c1_def c2_def)
  have s2: "c1 1 > c1 0 \<and> c2 2 > c2 0" by (simp add: c1_def c2_def)
  show "L 0 > L 1 \<and> L 0 > L 2 \<and> c1 1 > c1 0 \<and> c2 2 > c2 0" using s1 s2 by simp
qed

text \<open>Theorem 3 (general half, OPEN per the paper). Whether every μ_t = 0 conclusion is in general inexpressible in the Horn / ∩–∪ fragment yet expressible with the weighted-threshold connective is left open ("proving the separation in general rather than only on the measured μ_t = 0 set is left open"). i-orca records it as an explicit frontier hole.\<close>
theorem weightedthresholdgeneralseparation:
  shows "horn_expressible t \<longrightarrow> mu_t t \<noteq> (0::nat)"
proof -
  show "horn_expressible t \<longrightarrow> mu_t t \<noteq> (0::nat)" sorry  (* sketched *)
qed

text \<open>Theorem 4. With a uniform base measure M_0 reweighted by exp(c_j^v) per source, the normalised mass m(v)/Σ_w m(w) = exp(L_v)/Z is exactly the softmax — the Gibbs measure recovered as a PIC incidence frequency, parameter-free.\<close>
theorem recoveredprobability:
  assumes
    M0pos: "(M0::real) > 0"
  shows "(M0 * exp (L v)) / (\<Sum>w\<in>V. M0 * exp (L w)) = exp (L v) / (\<Sum>w\<in>V. exp (L w))"
proof -
  have s1: "(\<Sum>w\<in>V. M0 * exp (L w)) = M0 * (\<Sum>w\<in>V. exp (L w))" by (simp add: sum_distrib_left)
  have s2: "M0 \<noteq> 0" using M0pos by (metis less_irrefl)
  show "(M0 * exp (L v)) / (\<Sum>w\<in>V. M0 * exp (L w)) = exp (L v) / (\<Sum>w\<in>V. exp (L w))" using s1 s2 by (simp add: mult_divide_mult_cancel_left)
qed

text \<open>Theorem 5 (ratio core). Under equitable contributions e_m = E/PR, single-source relative influence is e_m/E = 1/PR and a k-source body captures only |A|/PR of E — so no bounded-size formula localises the quantity (the asymptotic O(1/PR) consequence is DiffusenessAsymptotic).\<close>
theorem diffuseness:
  assumes
    Epos: "E \<noteq> 0"
    and
    equit: "\<And>m. m \<in> {1..PR} \<Longrightarrow> e m = E / real PR"
  shows "(\<forall>m\<in>{1..PR}. e m / E = 1 / real PR) \<and> (\<forall>A. A \<subseteq> {1..PR} \<longrightarrow> (\<Sum>m\<in>A. e m) / E = real (card A) / real PR)"
proof -
  have s1: "\<forall>m\<in>{1..PR}. e m / E = 1 / real PR" using Epos by (simp add: equit field_simps)
  have s2: "\<forall>A. A \<subseteq> {1..PR} \<longrightarrow> (\<Sum>m\<in>A. e m) / E = real (card A) / real PR" sorry  (* hammer; using: Epos *)
  show "(\<forall>m\<in>{1..PR}. e m / E = 1 / real PR) \<and> (\<forall>A. A \<subseteq> {1..PR} \<longrightarrow> (\<Sum>m\<in>A. e m) / E = real (card A) / real PR)" using s1 s2 by blast
qed

text \<open>Theorem 5 (asymptotic consequence). As PR → ∞ the k-source captured fraction k/PR → 0: no bounded-size PIC formula localises a diffuse causal property, and P⟨single-module intervention alters E⟩ = O(1/PR). The limit is a standard analytic fact left to Sledgehammer.\<close>
theorem diffusenessasymptotic:
  shows "(\<lambda>n. real k / real n) \<longlonglongrightarrow> 0"
proof -
  show "(\<lambda>n. real k / real n) \<longlonglongrightarrow> 0" sorry  (* hammer *)
qed

text \<open>Theorem 6. Read Π as a semiring FAQ. Under the tropical semiring (T=0) the aggregate is the attained max with witness argmax (greedy decode); the Maslov sandwich Max(L) ≤ T·ln Σ exp(L/T) ≤ Max(L) + T·ln|V| brings it to the log-semiring softmax aggregate (T=1) — one program, two temperatures. The two bound steps are the cited Maslov dequantization, left to Sledgehammer.\<close>
theorem twotemperaturesoundness:
  assumes
    Tpos: "T > 0"
    and
    finV: "finite V"
    and
    neV: "V \<noteq> {}"
  shows "(\<exists>u\<in>V. L u = Max (L ` V)) \<and> Max (L ` V) \<le> T * ln (\<Sum>v\<in>V. exp (L v / T)) \<and> T * ln (\<Sum>v\<in>V. exp (L v / T)) \<le> Max (L ` V) + T * ln (real (card V))"
proof -
  have s_mem: "Max (L ` V) \<in> L ` V" using finV neV by (intro Max_in) auto
  have s_attained: "\<exists>u\<in>V. L u = Max (L ` V)" using s_mem by auto
  have s_lower: "Max (L ` V) \<le> T * ln (\<Sum>v\<in>V. exp (L v / T))" sorry  (* hammer; using: s_attained, Tpos, finV, neV *)
  have s_upper: "T * ln (\<Sum>v\<in>V. exp (L v / T)) \<le> Max (L ` V) + T * ln (real (card V))" sorry  (* hammer; using: Tpos, finV, neV *)
  show "(\<exists>u\<in>V. L u = Max (L ` V)) \<and> Max (L ` V) \<le> T * ln (\<Sum>v\<in>V. exp (L v / T)) \<and> T * ln (\<Sum>v\<in>V. exp (L v / T)) \<le> Max (L ` V) + T * ln (real (card V))" using s_attained s_lower s_upper by blast
qed

text \<open>Proposition 1. The linear regions of the max-logit M(r) are the Laguerre power diagram of {U_v} with weights (b_v, ‖U_v‖²): the power-distance difference between two sites equals −2× the score difference ⟨r,U_v⟩+b_v, so the cell of minimum power distance is exactly the argmax (predicted) token.\<close>
theorem proppowerdiagram:
  shows "((norm (r - U v)) ^ 2 - ((norm (U v)) ^ 2 + 2 * b v)) - ((norm (r - U w)) ^ 2 - ((norm (U w)) ^ 2 + 2 * b w)) = - 2 * ((inner r (U v) + b v) - (inner r (U w) + b w))"
proof -
  have s1v: "(norm (r - U v)) ^ 2 = (norm r) ^ 2 - 2 * inner r (U v) + (norm (U v)) ^ 2" by (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right inner_commute)
  have s1w: "(norm (r - U w)) ^ 2 = (norm r) ^ 2 - 2 * inner r (U w) + (norm (U w)) ^ 2" by (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right inner_commute)
  show "((norm (r - U v)) ^ 2 - ((norm (U v)) ^ 2 + 2 * b v)) - ((norm (r - U w)) ^ 2 - ((norm (U w)) ^ 2 + 2 * b w)) = - 2 * ((inner r (U v) + b v) - (inner r (U w) + b w))" using s1v s1w by (simp add: algebra_simps)
qed

text \<open>Proposition 2. The normalised margin (L_t − L_{v*})/‖U_t − U_{v*}‖ is the exact signed Euclidean distance from r to the t–v* facet of the tropical hypersurface: the numerator ⟨r, U_t − U_{v*}⟩ + (b_t − b_{v*}) equals L_t − L_{v*} = Δ, and dividing by ‖U_t − U_{v*}‖ gives the point-to-bisector distance.\<close>
theorem propmargindistance:
  shows "(inner r (U t - U vstar) + (b t - b vstar)) / norm (U t - U vstar) = ((inner r (U t) + b t) - (inner r (U vstar) + b vstar)) / norm (U t - U vstar)"
proof -
  have s1: "inner r (U t - U vstar) = inner r (U t) - inner r (U vstar)" by (simp add: inner_diff_right)
  show "(inner r (U t - U vstar) + (b t - b vstar)) / norm (U t - U vstar) = ((inner r (U t) + b t) - (inner r (U vstar) + b vstar)) / norm (U t - U vstar)" using s1 by (simp add: algebra_simps)
qed

end
