theory MuZeroNotIrreducible
  imports Complex_Main
begin

text \<open>Theorem 3 (general half) — restated faithfully and PROVEN. The earlier i-orca hole `horn_expressible t ⟶ mu_t t ≠ 0` used *uninterpreted* predicates, so it was vacuously refutable — never a faithful encoding. With explicit definitions (a source set S *decides* t when t is the strict argmax of the S-sum over outcomes V; μ_t = 0 means no *singleton* decides t; t is Horn/sub-conjunction-expressible when some *proper non-empty subset* already decides it), the substantive content is sharp: **μ_t = 0 does NOT imply not-Horn-expressible.** Witnessed here, kernel-checked: a 3-source token with μ_0 = 0 whose proper subset {1,2} already decides outcome 0. The dual positive result — genuinely *irreducible* composed tokens (no proper subset suffices) exist at every n (incl. an n = 3 case where every source is necessary, tying to §4.4 fragility) — is proven in the companion [`separation/Separation.thy`](separation/Separation.thy). The full expressivity *characterisation* over formula classes is the remaining genuine open frontier.\<close>
theorem muzeronotirreducible:
  assumes
    c3_def: "\<And>j v. c3 (j::nat) (v::nat) = (if j = 1 then (if v = 0 then (2::real) else if v = 1 then 3 else 0) else if j = 2 then (if v = 0 then 2 else if v = 1 then 0 else 3) else (if v = 0 then 0 else 1/2))"
  shows "(\<forall>j\<in>{1,2,3}. \<not> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>{j}. c3 i v) < (\<Sum>i\<in>{j}. c3 i 0))) \<and> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>{1,2,3}. c3 i v) < (\<Sum>i\<in>{1,2,3}. c3 i 0)) \<and> (\<exists>P. P \<noteq> {} \<and> P \<subset> {1,2,3} \<and> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>P. c3 i v) < (\<Sum>i\<in>P. c3 i 0)))"
proof -
  have s_mu0: "\<forall>j\<in>{1,2,3}. \<not> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>{j}. c3 i v) < (\<Sum>i\<in>{j}. c3 i 0))" by (simp add: c3_def)
  have s_dec: "\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>{1,2,3}. c3 i v) < (\<Sum>i\<in>{1,2,3}. c3 i 0)" by (simp add: c3_def)
  have s_suff: "\<exists>P. P \<noteq> {} \<and> P \<subset> {1,2,3} \<and> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>P. c3 i v) < (\<Sum>i\<in>P. c3 i 0))" by (rule exI[of _ "{1,2::nat}"]) (auto simp: c3_def)
  show "(\<forall>j\<in>{1,2,3}. \<not> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>{j}. c3 i v) < (\<Sum>i\<in>{j}. c3 i 0))) \<and> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>{1,2,3}. c3 i v) < (\<Sum>i\<in>{1,2,3}. c3 i 0)) \<and> (\<exists>P. P \<noteq> {} \<and> P \<subset> {1,2,3} \<and> (\<forall>v\<in>{0,1,2}. v \<noteq> 0 \<longrightarrow> (\<Sum>i\<in>P. c3 i v) < (\<Sum>i\<in>P. c3 i 0)))" using s_mu0 s_dec s_suff by blast
qed

end
