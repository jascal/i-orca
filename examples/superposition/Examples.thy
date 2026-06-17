(*
  Examples.thy -- the simplest superposition: an antipodal pair.

  A concrete, kernel-checked witness for the Toy-Models picture. Put n = 2 features
  into m = 1 dimension as the antipodal unit vectors +1 and -1. They are unit-norm,
  they interfere maximally (<v_0,v_1> = -1), and they achieve the Welch off-diagonal
  bound n(n-m)/m = 2 with EQUALITY -- the optimal way to pack two features into one
  dimension, exactly the antipodal configuration the paper finds for sparse pairs.
*)

theory Examples
  imports Welch
begin

definition antipodal :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "antipodal i k = (if i = 0 then 1 else - 1)"

lemma antipodal_unit: "i \<in> {0, 1} \<Longrightarrow> ip {0::nat} (antipodal i) (antipodal i) = 1"
  by (auto simp: ip_def antipodal_def)

text \<open>The two features interfere maximally.\<close>

lemma antipodal_interference: "ip {0::nat} (antipodal 0) (antipodal 1) = - 1"
  by (simp add: ip_def antipodal_def)

text \<open>Two features in one dimension, with non-zero interference: a concrete instance of
  superposition (more features than dimensions forces interference).\<close>

theorem antipodal_is_superposition:
  "\<exists>i\<in>{0,1::nat}. \<exists>j\<in>{0,1}. i \<noteq> j \<and> ip {0::nat} (antipodal i) (antipodal j) \<noteq> 0"
  by (rule superposition_forces_interference) (auto simp: antipodal_unit)

text \<open>The antipodal pair achieves the Welch off-diagonal bound with equality -- the
  optimal packing of two features into one dimension.\<close>

theorem antipodal_achieves_welch:
  "(\<Sum>i\<in>{0,1::nat}. \<Sum>j\<in>{0,1} - {i}. (ip {0::nat} (antipodal i) (antipodal j))\<^sup>2)
   = real (card {0,1::nat}) * (real (card {0,1::nat}) - real (card {0::nat}))
     / real (card {0::nat})"
proof -
  \<comment> \<open>both sides evaluate to 2 = n(n-m)/m at n = 2, m = 1.\<close>
  have lhs: "(\<Sum>i\<in>{0,1::nat}. \<Sum>j\<in>{0,1} - {i}. (ip {0::nat} (antipodal i) (antipodal j))\<^sup>2) = 2"
    by (simp add: ip_def antipodal_def insert_Diff_if)
  have rhs: "real (card {0,1::nat}) * (real (card {0,1::nat}) - real (card {0::nat}))
             / real (card {0::nat}) = 2"
    by simp
  show ?thesis using lhs rhs by simp
qed

end
