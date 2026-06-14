theory Diffuseness
  imports Complex_Main
begin

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

end
