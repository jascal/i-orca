(*
  Newton.thy -- Newton polytopes and polytope propagation
  (Zhang-Naitzat-Lim Def 3.2 / Cor 3.4; Pachter-Sturmfels, "Tropical Geometry of
  Statistical Models", PNAS 2004).

  We represent a one-variable tropical polynomial concretely as a finite set of
  monomials (slope, intercept):

        tpoly P x = MAX (s,t) in P. s * x + t.

  The tropical PRODUCT of polynomials is their tropical-multiplicative combination,
  whose monomial set is the sumset

        tprod P Q = { (s+s', t+t') : (s,t) in P, (s',t') in Q }.

  Pachter-Sturmfels "polytope propagation": tropical multiplication of polynomials is
  pointwise ADDITION of the functions (tpoly_tprod) -- the sum-product / Viterbi
  recursion run on (slope) Newton polytopes. Consequences: the monomial count is
  submultiplicative (tprod_card_le) and the Newton polytope (here, the slope support)
  of a product is the MINKOWSKI SUM of the factors' supports (tprod_slope_sumset) --
  the zonotope/vertex-count mechanism behind the linear-region bounds (Cor 3.4).
*)

theory Newton
  imports Complex_Main
begin

text \<open>Max of a sum over a product set splits into the sum of the component maxima.\<close>

lemma Max_sum_prod:
  fixes f :: "'a \<Rightarrow> real" and g :: "'b \<Rightarrow> real"
  assumes "finite P" "finite Q" "P \<noteq> {}" "Q \<noteq> {}"
  shows "(MAX z\<in>P\<times>Q. f (fst z) + g (snd z)) = Max (f ` P) + Max (g ` Q)"
proof -
  have fin: "finite (P \<times> Q)" using assms by simp
  have ne: "P \<times> Q \<noteq> {}" using assms by simp
  have le: "f (fst z) + g (snd z) \<le> Max (f ` P) + Max (g ` Q)" if "z \<in> P \<times> Q" for z
  proof -
    have "fst z \<in> P" and "snd z \<in> Q" using that by (auto simp: mem_Times_iff)
    hence "f (fst z) \<le> Max (f ` P)" and "g (snd z) \<le> Max (g ` Q)"
      using assms(1,2) by (auto intro: Max_ge)
    thus ?thesis by simp
  qed
  have "Max (f ` P) \<in> f ` P" using assms(1,3) by (intro Max_in) auto
  then obtain p where p: "p \<in> P" "f p = Max (f ` P)" by auto
  have "Max (g ` Q) \<in> g ` Q" using assms(2,4) by (intro Max_in) auto
  then obtain q where q: "q \<in> Q" "g q = Max (g ` Q)" by auto
  have ge: "Max (f ` P) + Max (g ` Q) \<le> (MAX z\<in>P\<times>Q. f (fst z) + g (snd z))"
  proof -
    have mem: "(p, q) \<in> P \<times> Q" using p q by simp
    have "f p + g q \<in> (\<lambda>z. f (fst z) + g (snd z)) ` (P \<times> Q)"
      using mem by (auto intro!: rev_image_eqI)
    moreover have "finite ((\<lambda>z. f (fst z) + g (snd z)) ` (P \<times> Q))" using fin by simp
    ultimately have "f p + g q \<le> (MAX z\<in>P\<times>Q. f (fst z) + g (snd z))" by (simp add: Max_ge)
    thus ?thesis using p q by simp
  qed
  have "(MAX z\<in>P\<times>Q. f (fst z) + g (snd z)) \<le> Max (f ` P) + Max (g ` Q)"
    using fin ne le by (subst Max_le_iff) auto
  thus ?thesis using ge by simp
qed

type_synonym monomial = "real \<times> real"

definition tmon :: "monomial \<Rightarrow> real \<Rightarrow> real" where
  "tmon m x = fst m * x + snd m"

definition tpoly :: "monomial set \<Rightarrow> real \<Rightarrow> real" where
  "tpoly P x = (MAX m\<in>P. tmon m x)"

definition tprod :: "monomial set \<Rightarrow> monomial set \<Rightarrow> monomial set" where
  "tprod P Q = (\<lambda>(p, q). (fst p + fst q, snd p + snd q)) ` (P \<times> Q)"

text \<open>Polytope propagation: the tropical product of polynomials is the pointwise sum
  of the functions.\<close>

theorem tpoly_tprod:
  assumes "finite P" "finite Q" "P \<noteq> {}" "Q \<noteq> {}"
  shows "tpoly (tprod P Q) x = tpoly P x + tpoly Q x"
proof -
  have "(\<lambda>m. tmon m x) \<circ> (\<lambda>(p, q). (fst p + fst q, snd p + snd q))
        = (\<lambda>z. tmon (fst z) x + tmon (snd z) x)"
    by (auto simp: fun_eq_iff tmon_def case_prod_beta algebra_simps)
  hence "tpoly (tprod P Q) x = (MAX z\<in>P\<times>Q. tmon (fst z) x + tmon (snd z) x)"
    by (simp add: tpoly_def tprod_def image_comp)
  also have "\<dots> = Max ((\<lambda>p. tmon p x) ` P) + Max ((\<lambda>q. tmon q x) ` Q)"
    using assms by (rule Max_sum_prod)
  also have "\<dots> = tpoly P x + tpoly Q x" by (simp add: tpoly_def)
  finally show ?thesis .
qed

text \<open>The monomial count is submultiplicative under tropical product.\<close>

theorem tprod_card_le:
  assumes "finite P" "finite Q"
  shows "card (tprod P Q) \<le> card P * card Q"
proof -
  have "finite (P \<times> Q)" using assms by simp
  hence "card (tprod P Q) \<le> card (P \<times> Q)"
    unfolding tprod_def by (rule card_image_le)
  thus ?thesis by (simp add: card_cartesian_product)
qed

text \<open>The slope support (Newton polytope) of a tropical product is the Minkowski sum
  of the factors' slope supports.\<close>

theorem tprod_slope_sumset:
  "fst ` tprod P Q = (\<lambda>(a, b). a + b) ` (fst ` P \<times> fst ` Q)"
  unfolding tprod_def by (force simp: image_image case_prod_beta)

end
