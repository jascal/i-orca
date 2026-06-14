theory NonTruthFunctionalityBudget
  imports "HOL-Analysis.Inner_Product"
begin

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

end
