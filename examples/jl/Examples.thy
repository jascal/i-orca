(*
  Examples.thy -- a concrete instance of the probabilistic-method existence.

  A minimal, fully concrete witness for the existence pillar (JLExistence.thy). Take four
  candidate projections Omega = {0,1,2,3} and two pairwise-distance constraints
  P = {0,1}, where constraint i is violated only by projection i (bad i = {i}). Only two
  of the four projections are ever bad, so their total -- card {0} + card {1} = 2 -- is
  below card Omega = 4; by probabilistic_method a projection avoiding BOTH bad sets must
  exist (here 2 or 3). This is the Johnson-Lindenstrauss union-bound argument in
  miniature: few rare failures leave a good projection standing.
*)

theory Examples
  imports JLExistence
begin

theorem example_good_projection_exists:
  "\<exists>w\<in>{0,1,2,3::nat}. \<forall>i\<in>{0,1::nat}. w \<notin> {i}"
proof (rule probabilistic_method)
  show "finite {0,1,2,3::nat}" by simp
  show "finite {0,1::nat}" by simp
  show "\<And>i. i \<in> {0,1::nat} \<Longrightarrow> {i} \<subseteq> {0,1,2,3::nat}" by auto
  show "(\<Sum>i\<in>{0,1::nat}. card {i}) < card {0,1,2,3::nat}" by simp
qed

end
