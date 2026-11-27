theory Capacity_Counting
  imports Complex_Main Node_Mask_Clamp
begin

section \<open>How many distinct values must a node carry?\<close>

text \<open>If a student matches a host exactly under every single-node swap of node n, then the student's
node n must take at least as many distinct values over the domain as the host's node n has distinct
swap behaviours. A sparse discrete site can produce only as many values as it has codes, which gives a
necessary condition on its dictionary size D, number of active latents k and number of levels L.
The condition concerns exact swap equivalence on a finite domain; it says nothing about learnability.\<close>

subsection \<open>Swap behaviours versus node values\<close>

definition swap_row :: "('x, 'n, 'v) mechanisms \<Rightarrow> 'n list \<Rightarrow> (('n \<Rightarrow> 'v) \<Rightarrow> 'y) \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> ('n \<Rightarrow> 'v option) \<Rightarrow> 'x \<Rightarrow> ('x \<Rightarrow> 'y)" where
  "swap_row mech order rd d n ov b = (\<lambda>a. eval mech order rd d a (swap_ov mech order d {n} b ov))"

definition put_node :: "'n \<Rightarrow> 'v \<Rightarrow> ('n \<Rightarrow> 'v option) \<Rightarrow> ('n \<Rightarrow> 'v option)" where
  "put_node n v ov = (\<lambda>m. if m = n then Some v else ov m)"

lemma swap_ov_single: "swap_ov mech order d {n} b ov = put_node n (nodeval mech order d b ov n) ov"
  unfolding swap_ov_def put_node_def by (rule ext) simp

lemma swap_row_via_value:
  "swap_row mech order rd d n ov b = (\<lambda>a. eval mech order rd d a (put_node n (nodeval mech order d b ov n) ov))"
  unfolding swap_row_def swap_ov_single by simp

theorem swap_behaviours_le_node_values:
  assumes fin: "finite D"
      and eq: "\<And>b. b \<in> D \<Longrightarrow> swap_row mech1 order1 rd1 d1 n ov1 b = swap_row mech2 order2 rd2 d2 n ov2 b"
  shows "card (swap_row mech1 order1 rd1 d1 n ov1 ` D) \<le> card ((\<lambda>b. nodeval mech2 order2 d2 b ov2 n) ` D)"
proof -
  let ?f = "\<lambda>b. nodeval mech2 order2 d2 b ov2 n"
  let ?R = "\<lambda>v a. eval mech2 order2 rd2 d2 a (put_node n v ov2)"
  have row2: "\<And>b. swap_row mech2 order2 rd2 d2 n ov2 b = ?R (?f b)"
    by (simp add: swap_row_via_value)
  have "swap_row mech1 order1 rd1 d1 n ov1 ` D = ?R ` (?f ` D)"
  proof -
    have "swap_row mech1 order1 rd1 d1 n ov1 ` D = swap_row mech2 order2 rd2 d2 n ov2 ` D"
      by (rule image_cong[OF refl]) (rule eq)
    also have "... = ?R ` (?f ` D)" by (simp add: row2 image_image)
    finally show ?thesis .
  qed
  moreover have "card (?R ` (?f ` D)) \<le> card (?f ` D)" by (rule card_image_le) (simp add: fin)
  ultimately show ?thesis by simp
qed

subsection \<open>The code space of a sparse discrete site\<close>

text \<open>A code chooses a set S of at most k active latents out of D, and one of L levels for each of
them. It is a pair (S, levels), with the levels listed in order.\<close>

definition sparse_supports :: "nat \<Rightarrow> nat \<Rightarrow> nat set set" where
  "sparse_supports D k = {S. S \<subseteq> {..<D} \<and> card S \<le> k}"

definition sparse_codes :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat set \<times> nat list) set" where
  "sparse_codes D k L = (SIGMA S:sparse_supports D k. {ls. set ls \<subseteq> {..<L} \<and> length ls = card S})"

lemma finite_sparse_supports: "finite (sparse_supports D k)"
  unfolding sparse_supports_def by (rule finite_subset[where B = "Pow {..<D}"]) auto

lemma finite_level_lists: "finite {ls :: nat list. set ls \<subseteq> {..<(L::nat)} \<and> length ls = n}"
  by (rule finite_lists_length_eq[OF finite_lessThan])

lemma finite_sparse_codes: "finite (sparse_codes D k L)"
  unfolding sparse_codes_def by (rule finite_SigmaI) (simp_all add: finite_sparse_supports finite_level_lists)

lemma card_sparse_codes:
  "card (sparse_codes D k L) = (\<Sum>S\<in>sparse_supports D k. L ^ card S)"
  unfolding sparse_codes_def
  by (simp add: card_SigmaI finite_sparse_supports finite_level_lists card_lists_length_eq)

lemma card_sparse_codes_ge: "(D choose k) * L ^ k \<le> card (sparse_codes D k L)"
proof -
  let ?Sk = "{S. S \<subseteq> {..<D} \<and> card S = k}"
  have sub: "?Sk \<subseteq> sparse_supports D k" unfolding sparse_supports_def by auto
  have cs: "card ?Sk = D choose k" using n_subsets[of "{..<D}" k] by simp
  have e1: "(\<Sum>S\<in>?Sk. L ^ card S) = (\<Sum>S\<in>?Sk. L ^ k)" by (rule sum.cong) auto
  have e2: "(\<Sum>S\<in>?Sk. L ^ k) = card ?Sk * L ^ k" by simp
  have le: "(\<Sum>S\<in>?Sk. L ^ card S) \<le> (\<Sum>S\<in>sparse_supports D k. L ^ card S)"
    by (rule sum_mono2[OF finite_sparse_supports sub]) simp
  have "(D choose k) * L ^ k = (\<Sum>S\<in>?Sk. L ^ card S)" using e1 e2 cs by simp
  also have "... \<le> (\<Sum>S\<in>sparse_supports D k. L ^ card S)" by (rule le)
  finally have ge: "(D choose k) * L ^ k \<le> (\<Sum>S\<in>sparse_supports D k. L ^ card S)" .
  show ?thesis unfolding card_sparse_codes by (rule ge)
qed

lemma card_sparse_codes_le:
  assumes "0 < L"
  shows "card (sparse_codes D k L) \<le> card (sparse_supports D k) * L ^ k"
proof -
  have "(\<Sum>S\<in>sparse_supports D k. L ^ card S) \<le> (\<Sum>S\<in>sparse_supports D k. L ^ k)"
  proof (rule sum_mono)
    fix S assume "S \<in> sparse_supports D k"
    then have "card S \<le> k" unfolding sparse_supports_def by simp
    with assms show "L ^ card S \<le> L ^ k" by (intro power_increasing) auto
  qed
  then show ?thesis using card_sparse_codes by simp
qed

subsection \<open>The necessary condition\<close>

theorem node_values_le_codes:
  assumes fin: "finite D" and enc: "\<And>b. b \<in> D \<Longrightarrow> enc b \<in> sparse_codes Dsz k L"
      and val: "\<And>b. b \<in> D \<Longrightarrow> f b = dec (enc b)"
  shows "card (f ` D) \<le> card (sparse_codes Dsz k L)"
proof -
  have sub: "f ` D \<subseteq> dec ` sparse_codes Dsz k L" using enc val by force
  have "card (f ` D) \<le> card (dec ` sparse_codes Dsz k L)"
    by (rule card_mono) (simp_all add: finite_sparse_codes sub)
  also have "... \<le> card (sparse_codes Dsz k L)" by (rule card_image_le[OF finite_sparse_codes])
  finally show ?thesis .
qed

theorem capacity_necessary:
  assumes fin: "finite D"
      and eq: "\<And>b. b \<in> D \<Longrightarrow> swap_row mech1 order1 rd1 d1 n ov1 b = swap_row mech2 order2 rd2 d2 n ov2 b"
      and enc: "\<And>b. b \<in> D \<Longrightarrow> enc b \<in> sparse_codes Dsz k L"
      and val: "\<And>b. b \<in> D \<Longrightarrow> nodeval mech2 order2 d2 b ov2 n = dec (enc b)"
  shows "card (swap_row mech1 order1 rd1 d1 n ov1 ` D) \<le> card (sparse_codes Dsz k L)"
proof -
  have "card (swap_row mech1 order1 rd1 d1 n ov1 ` D) \<le> card ((\<lambda>b. nodeval mech2 order2 d2 b ov2 n) ` D)"
    using fin eq by (rule swap_behaviours_le_node_values)
  also have "... \<le> card (sparse_codes Dsz k L)"
    using fin enc val by (rule node_values_le_codes)
  finally show ?thesis .
qed

subsection \<open>The condition does not bind at the sizes in use\<close>

lemma choose_64_8_ge: "(8::nat) ^ 8 \<le> 64 choose 8"
proof -
  have "(of_nat (64::nat) / of_nat (8::nat) :: real) ^ 8 \<le> of_nat (64 choose 8)"
    by (rule binomial_ge_n_over_k_pow_k) simp
  then have "(8::real) ^ 8 \<le> of_nat (64 choose 8)" by simp
  then have "of_nat ((8::nat) ^ 8) \<le> (of_nat (64 choose 8) :: real)" by simp
  then show ?thesis by (simp only: of_nat_le_iff)
qed

lemma codes_64_8_10_large: "10 ^ 15 \<le> card (sparse_codes 64 8 10)"
proof -
  have "(10::nat) ^ 15 \<le> 8 ^ 8 * 10 ^ 8" by simp
  also have "... \<le> (64 choose 8) * 10 ^ 8" using choose_64_8_ge by (intro mult_right_mono) simp_all
  also have "... \<le> card (sparse_codes 64 8 10)" by (rule card_sparse_codes_ge)
  finally show ?thesis .
qed

corollary capacity_not_binding_64_8_10:
  assumes "m \<le> 10 ^ 15"
  shows "m \<le> card (sparse_codes 64 8 10)"
  using assms codes_64_8_10_large by simp

text \<open>Second operating point: the pythia-14m students (dictionary D = 1024, k = 32 active latents,
L = 40 levels). The code count exceeds 10^99, far above any finite evaluation set used.\<close>

lemma choose_1024_32_ge: "(32::nat) ^ 32 \<le> 1024 choose 32"
proof -
  have "(of_nat (1024::nat) / of_nat (32::nat) :: real) ^ 32 \<le> of_nat (1024 choose 32)"
    by (rule binomial_ge_n_over_k_pow_k) simp
  then have "(32::real) ^ 32 \<le> of_nat (1024 choose 32)" by simp
  then have "of_nat ((32::nat) ^ 32) \<le> (of_nat (1024 choose 32) :: real)" by simp
  then show ?thesis by (simp only: of_nat_le_iff)
qed

lemma codes_1024_32_40_large: "10 ^ 99 \<le> card (sparse_codes 1024 32 40)"
proof -
  have "(10::nat) ^ 99 \<le> 32 ^ 32 * 40 ^ 32" by simp
  also have "... \<le> (1024 choose 32) * 40 ^ 32" using choose_1024_32_ge by (intro mult_right_mono) simp_all
  also have "... \<le> card (sparse_codes 1024 32 40)" by (rule card_sparse_codes_ge)
  finally show ?thesis .
qed

corollary capacity_not_binding_1024_32_40:
  assumes "m \<le> 10 ^ 99"
  shows "m \<le> card (sparse_codes 1024 32 40)"
  using assms codes_1024_32_40_large by simp

end
