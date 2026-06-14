theory PropMarginDistance
  imports "HOL-Analysis.Inner_Product"
begin

text \<open>Proposition 2. The normalised margin (L_t − L_{v*})/‖U_t − U_{v*}‖ is the exact signed Euclidean distance from r to the t–v* facet of the tropical hypersurface: the numerator ⟨r, U_t − U_{v*}⟩ + (b_t − b_{v*}) equals L_t − L_{v*} = Δ, and dividing by ‖U_t − U_{v*}‖ gives the point-to-bisector distance.\<close>
theorem propmargindistance:
  shows "(inner r (U t - U vstar) + (b t - b vstar)) / norm (U t - U vstar) = ((inner r (U t) + b t) - (inner r (U vstar) + b vstar)) / norm (U t - U vstar)"
proof -
  have s1: "inner r (U t - U vstar) = inner r (U t) - inner r (U vstar)" by (simp add: inner_diff_right)
  show "(inner r (U t - U vstar) + (b t - b vstar)) / norm (U t - U vstar) = ((inner r (U t) + b t) - (inner r (U vstar) + b vstar)) / norm (U t - U vstar)" using s1 by (simp add: algebra_simps)
qed

end
