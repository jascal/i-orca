theory PropPowerDiagram
  imports "HOL-Analysis.Inner_Product"
begin

text \<open>Proposition 1. The linear regions of the max-logit M(r) are the Laguerre power diagram of {U_v} with weights (b_v, ‖U_v‖²): the power-distance difference between two sites equals −2× the score difference ⟨r,U_v⟩+b_v, so the cell of minimum power distance is exactly the argmax (predicted) token.\<close>
theorem proppowerdiagram:
  shows "((norm (r - U v)) ^ 2 - ((norm (U v)) ^ 2 + 2 * b v)) - ((norm (r - U w)) ^ 2 - ((norm (U w)) ^ 2 + 2 * b w)) = - 2 * ((inner r (U v) + b v) - (inner r (U w) + b w))"
proof -
  have s1v: "(norm (r - U v)) ^ 2 = (norm r) ^ 2 - 2 * inner r (U v) + (norm (U v)) ^ 2" by (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right inner_commute)
  have s1w: "(norm (r - U w)) ^ 2 = (norm r) ^ 2 - 2 * inner r (U w) + (norm (U w)) ^ 2" by (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right inner_commute)
  show "((norm (r - U v)) ^ 2 - ((norm (U v)) ^ 2 + 2 * b v)) - ((norm (r - U w)) ^ 2 - ((norm (U w)) ^ 2 + 2 * b w)) = - 2 * ((inner r (U v) + b v) - (inner r (U w) + b w))" using s1v s1w by (simp add: algebra_simps)
qed

end
