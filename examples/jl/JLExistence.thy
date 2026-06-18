(*
  JLExistence.thy -- the probabilistic method: a good projection exists.

  The Johnson-Lindenstrauss embedding is shown to EXIST by the probabilistic method: if a
  random projection violates each pairwise-distance constraint only rarely, and there are
  few constraints, then a single projection satisfying ALL of them must exist. Formally,
  over a finite sample space of projections, if the bad sets (projections that distort a
  given pair) are jointly small -- the sum of their sizes is below the size of the whole
  space -- then their union is not everything, so some projection avoids every bad set.

  probabilistic_method is the combinatorial core (a counting / union-bound argument).
  jl_good_projection_exists assembles it with the per-pair concentration bound
  (card(bad p) <= q * card Omega) and the smallness of the constraint count
  (card P * q < 1, supplied by the dimension bound of JLDimension.thy) to conclude that a
  distance-preserving projection exists. The Gaussian concentration that justifies the
  per-pair bound is the meta input.
*)

theory JLExistence
  imports Complex_Main
begin

text \<open>The probabilistic method (finite form): if the bad events jointly cover less than
  the whole sample space, a point outside all of them exists.\<close>

theorem probabilistic_method:
  fixes Omega :: "'a set"
  assumes finO: "finite Omega" and finI: "finite I"
      and sub: "\<And>i. i \<in> I \<Longrightarrow> bad i \<subseteq> Omega"
      and few: "(\<Sum>i\<in>I. card (bad i)) < card Omega"
  shows "\<exists>w\<in>Omega. \<forall>i\<in>I. w \<notin> bad i"
proof -
  have "card (\<Union>i\<in>I. bad i) \<le> (\<Sum>i\<in>I. card (bad i))"
    using finI by (rule card_UN_le)
  also have "\<dots> < card Omega" by (rule few)
  finally have lt: "card (\<Union>i\<in>I. bad i) < card Omega" .
  have subU: "(\<Union>i\<in>I. bad i) \<subseteq> Omega" using sub by auto
  have "(\<Union>i\<in>I. bad i) \<noteq> Omega" using lt by auto
  hence "Omega - (\<Union>i\<in>I. bad i) \<noteq> {}" using subU by blast
  then obtain w where "w \<in> Omega" "w \<notin> (\<Union>i\<in>I. bad i)" by auto
  thus ?thesis by auto
qed

text \<open>Bounded-quantifier surface form.\<close>

corollary probabilistic_method':
  assumes "finite Omega" and "finite I"
      and "\<forall>i\<in>I. bad i \<subseteq> Omega" and "(\<Sum>i\<in>I. card (bad i)) < card Omega"
  shows "\<exists>w\<in>Omega. \<forall>i\<in>I. w \<notin> bad i"
  using assms by (intro probabilistic_method) auto

text \<open>Assembled existence: per-pair concentration (q) plus a small constraint count
  (card P * q < 1) give a projection that preserves every pair.\<close>

theorem jl_good_projection_exists:
  fixes Omega :: "'r set" and P :: "'p set" and q :: real
  assumes finO: "finite Omega" and One: "Omega \<noteq> {}" and finP: "finite P"
      and bad_sub: "\<And>p. p \<in> P \<Longrightarrow> bad p \<subseteq> Omega"
      and conc: "\<And>p. p \<in> P \<Longrightarrow> real (card (bad p)) \<le> q * real (card Omega)"
      and few: "real (card P) * q < 1"
  shows "\<exists>R\<in>Omega. \<forall>p\<in>P. R \<notin> bad p"
proof -
  have Opos: "0 < real (card Omega)" using finO One by (simp add: card_gt_0_iff)
  have "real (\<Sum>p\<in>P. card (bad p)) = (\<Sum>p\<in>P. real (card (bad p)))" by simp
  also have "\<dots> \<le> (\<Sum>p\<in>P. q * real (card Omega))"
    using conc by (intro sum_mono) simp
  also have "\<dots> = real (card P) * q * real (card Omega)"
    by (simp add: sum_distrib_right mult.commute mult.left_commute)
  also have "\<dots> < 1 * real (card Omega)"
    using few Opos by (intro mult_strict_right_mono) auto
  finally have "real (\<Sum>p\<in>P. card (bad p)) < real (card Omega)" by simp
  hence "(\<Sum>p\<in>P. card (bad p)) < card Omega" by (simp add: of_nat_less_iff flip: of_nat_sum)
  with finO finP bad_sub show ?thesis by (rule probabilistic_method)
qed

text \<open>Bounded-quantifier surface form.\<close>

corollary jl_good_projection_exists':
  fixes Omega :: "'r set" and P :: "'p set" and q :: real
  assumes "finite Omega" and "Omega \<noteq> {}" and "finite P"
      and "\<forall>p\<in>P. bad p \<subseteq> Omega"
      and "\<forall>p\<in>P. real (card (bad p)) \<le> q * real (card Omega)"
      and "real (card P) * q < 1"
  shows "\<exists>R\<in>Omega. \<forall>p\<in>P. R \<notin> bad p"
  using assms by (intro jl_good_projection_exists) auto

end
