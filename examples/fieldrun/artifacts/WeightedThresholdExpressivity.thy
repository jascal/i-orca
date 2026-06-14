theory WeightedThresholdExpressivity
  imports Complex_Main
begin

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

end
