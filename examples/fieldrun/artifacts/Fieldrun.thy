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

text \<open>Theorem 3 (realisability half). A COMPOSED token (μ_t = 0) is the argmax of the weighted sum Σ_j c_j though no single source's argmax selects it: an explicit two-source, three-outcome witness where the sum prefers outcome 0 while source 1 prefers 1 and source 2 prefers 2 — realised by a weighted-threshold connective but by no singleton sufficient sub-conjunction. (Since at n = 2 the only proper non-empty subsets are the singletons, this witness is in fact *irreducible* — no proper sub-conjunction decides it; see `separation/Separation.thy::irreducible_pair`. Cf. MuZeroDoesNotImplyIrreducible for why this needs care at n ≥ 3.)\<close>
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

text \<open>Theorem 3 (general half) — restated faithfully and PROVEN. The earlier i-orca hole `horn_expressible t ⟶ mu_t t ≠ 0` used *uninterpreted* predicates, so it was vacuously refutable — never a faithful encoding. With explicit definitions (a source set S *decides* t when t is the strict argmax of the S-sum over outcomes V; μ_t = 0 means no *singleton* decides t; t is Horn/sub-conjunction-expressible when some *proper non-empty subset* already decides it), the substantive content is sharp: **μ_t = 0 does NOT imply not-Horn-expressible.** Witnessed here, kernel-checked: a 3-source token with μ_0 = 0 whose proper subset {1,2} already decides outcome 0. The dual positive result — genuinely *irreducible* composed tokens (no proper subset suffices) exist at every n (incl. an n = 3 case where every source is necessary, tying to §4.4 fragility) — is proven in the companion [`separation/Separation.thy`](separation/Separation.thy). The full expressivity *characterisation* over formula classes is the remaining genuine open frontier.\<close>
theorem muzerodoesnotimplyirreducible:
  assumes
    c3_def: "\<And>j v. c3 (j::nat) (v::nat) = (if j = 1 then (if v = 0 then (2::real) else if v = 1 then 3 else 0) else if j = 2 then (if v = 0 then 2 else if v = 1 then 0 else 3) else (if v = 0 then 0 else 1/2))"
  shows "(\<forall>j\<in>{1,2,3}. \<not> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>{j}. c3 i v) < (\<Sum>i\<in>{j}. c3 i 0))) \<and> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>{1,2,3}. c3 i v) < (\<Sum>i\<in>{1,2,3}. c3 i 0)) \<and> (\<exists>P. P \<noteq> {} \<and> P \<subset> {1,2,3} \<and> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>P. c3 i v) < (\<Sum>i\<in>P. c3 i 0)))"
proof -
  have s_mu0: "\<forall>j\<in>{1,2,3}. \<not> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>{j}. c3 i v) < (\<Sum>i\<in>{j}. c3 i 0))" by (simp add: c3_def)
  have s_dec: "\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>{1,2,3}. c3 i v) < (\<Sum>i\<in>{1,2,3}. c3 i 0)" by (simp add: c3_def)
  have s_suff: "\<exists>P. P \<noteq> {} \<and> P \<subset> {1,2,3} \<and> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>P. c3 i v) < (\<Sum>i\<in>P. c3 i 0))" by (rule exI[of _ "{1,2::nat}"]) (auto simp: c3_def)
  show "(\<forall>j\<in>{1,2,3}. \<not> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>{j}. c3 i v) < (\<Sum>i\<in>{j}. c3 i 0))) \<and> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>{1,2,3}. c3 i v) < (\<Sum>i\<in>{1,2,3}. c3 i 0)) \<and> (\<exists>P. P \<noteq> {} \<and> P \<subset> {1,2,3} \<and> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>P. c3 i v) < (\<Sum>i\<in>P. c3 i 0)))" using s_mu0 s_dec s_suff by blast
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
    and
    Asub: "A \<subseteq> {1..PR}"
  shows "(\<forall>m\<in>{1..PR}. e m / E = 1 / real PR) \<and> (\<Sum>m\<in>A. e m) / E = real (card A) / real PR"
proof -
  have s1: "\<forall>m\<in>{1..PR}. e m / E = 1 / real PR" using Epos by (simp add: equit field_simps)
  have s2a: "(\<Sum>m\<in>A. e m) = (\<Sum>m\<in>A. E / real PR)" by (rule sum.cong) (use Asub equit in auto)
  have s2b: "(\<Sum>m\<in>A. e m) = real (card A) * (E / real PR)" using s2a by simp
  have s2: "(\<Sum>m\<in>A. e m) / E = real (card A) / real PR" using s2b Epos by simp
  show "(\<forall>m\<in>{1..PR}. e m / E = 1 / real PR) \<and> (\<Sum>m\<in>A. e m) / E = real (card A) / real PR" using s1 s2 by blast
qed

text \<open>Theorem 5 (asymptotic consequence). As PR → ∞ the k-source captured fraction k/PR → 0: no bounded-size PIC formula localises a diffuse causal property, and P⟨single-module intervention alters E⟩ = O(1/PR). Discharged: the constant numerator over a diverging denominator tends to 0.\<close>
theorem diffusenessasymptotic:
  shows "(\<lambda>n. real k / real n) \<longlonglongrightarrow> 0"
proof -
  show "(\<lambda>n. real k / real n) \<longlonglongrightarrow> 0" by (rule tendsto_divide_0[OF tendsto_const filterlim_at_top_imp_at_infinity[OF filterlim_real_sequentially]])
qed

text \<open>Theorem 6. Read Π as a semiring FAQ. Under the tropical semiring (T=0) the aggregate is the attained max with witness argmax (greedy decode); the Maslov sandwich Max(L) ≤ T·ln Σ exp(L/T) ≤ Max(L) + T·ln|V| brings it to the log-semiring softmax aggregate (T=1) — one program, two temperatures. Both bounds are now discharged: the max term is one summand of the sum (lower), and every term is at most the max term (upper).\<close>
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
  obtain u where s_obt: "u \<in> V \<and> L u = Max (L ` V)" using s_attained by blast
  have s_uV: "u \<in> V" using s_obt by simp
  have s_Lu: "L u = Max (L ` V)" using s_obt by simp
  have s_memle: "exp (L u / T) \<le> (\<Sum>v\<in>V. exp (L v / T))" using s_uV finV by (intro member_le_sum) auto
  have s_lestar: "exp (Max (L ` V) / T) \<le> (\<Sum>v\<in>V. exp (L v / T))" using s_memle s_Lu by simp
  have s_pos: "0 < (\<Sum>v\<in>V. exp (L v / T))" using finV neV by (simp add: sum_pos)
  have s_key: "Max (L ` V) / T \<le> ln (\<Sum>v\<in>V. exp (L v / T))" using s_lestar s_pos by (simp add: ln_ge_iff)
  have s_lower: "Max (L ` V) \<le> T * ln (\<Sum>v\<in>V. exp (L v / T))" using s_key Tpos by (simp add: pos_divide_le_eq mult.commute)
  have s_ucard: "0 < real (card V)" using finV neV by (simp add: card_gt_0_iff)
  have s_ub: "\<And>v. v \<in> V \<Longrightarrow> exp (L v / T) \<le> exp (Max (L ` V) / T)" using finV Tpos by (simp add: Max_ge divide_right_mono)
  have s_bound: "(\<Sum>v\<in>V. exp (L v / T)) \<le> real (card V) * exp (Max (L ` V) / T)" using s_ub by (simp add: sum_bounded_above)
  have s_lnbound: "ln (\<Sum>v\<in>V. exp (L v / T)) \<le> ln (real (card V) * exp (Max (L ` V) / T))" using s_bound s_pos by simp
  have s_lnsplit: "ln (real (card V) * exp (Max (L ` V) / T)) = ln (real (card V)) + Max (L ` V) / T" using s_ucard by (simp add: ln_mult)
  have s_key2: "ln (\<Sum>v\<in>V. exp (L v / T)) \<le> ln (real (card V)) + Max (L ` V) / T" using s_lnbound s_lnsplit by simp
  have s_tmul: "T * ln (\<Sum>v\<in>V. exp (L v / T)) \<le> T * (ln (real (card V)) + Max (L ` V) / T)" using s_key2 Tpos by (simp add: mult_left_mono)
  have s_tsimp: "T * (ln (real (card V)) + Max (L ` V) / T) = Max (L ` V) + T * ln (real (card V))" using Tpos by (simp add: field_simps)
  have s_upper: "T * ln (\<Sum>v\<in>V. exp (L v / T)) \<le> Max (L ` V) + T * ln (real (card V))" using s_tmul s_tsimp by simp
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
