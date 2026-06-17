(*
  MaxPlus.thy -- max-plus linear algebra and residuation
  (Maragos-Charisopoulos-Theodosis, "Tropical Geometry and Machine Learning",
  Proc. IEEE 2021; classical Cuninghame-Green).

  In the max-plus semiring a "matrix" A and "vector" x multiply by

        (A odot x)_i = MAX_j (A i j + x j)      (mpmul)

  the operation a morphological / max-plus neural layer performs. The max-plus
  inequality A odot x <= b need not have an exact solution, but it always has a
  GREATEST subsolution, given by the residuation (the adjoint / erosion)

        xstar_j = MIN_i (b i - A i j)               (mpres).

  We prove the two defining properties: xstar is feasible
  (mpres_feasible: A odot xstar <= b) and it is the greatest such
  (mpres_greatest: every feasible x is dominated by xstar). Together these are the
  max-plus Galois connection underlying morphological-network analysis and max-plus
  equation solving.
*)

theory MaxPlus
  imports Complex_Main
begin

definition mpmul :: "('i \<Rightarrow> 'j \<Rightarrow> real) \<Rightarrow> 'j set \<Rightarrow> ('j \<Rightarrow> real) \<Rightarrow> 'i \<Rightarrow> real" where
  "mpmul A J x i = (MAX j\<in>J. A i j + x j)"

definition mpres :: "('i \<Rightarrow> 'j \<Rightarrow> real) \<Rightarrow> 'i set \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> 'j \<Rightarrow> real" where
  "mpres A I b j = (MIN i\<in>I. b i - A i j)"

text \<open>Feasibility: the residuated vector is a subsolution, @{term "mpmul A J (mpres A I b) i \<le> b i"}.\<close>

theorem mpres_feasible:
  assumes "finite I" "finite J" "J \<noteq> {}" "i \<in> I"
  shows "mpmul A J (mpres A I b) i \<le> b i"
proof -
  have "A i j + mpres A I b j \<le> b i" if "j \<in> J" for j
  proof -
    have "mpres A I b j \<le> b i - A i j"
      unfolding mpres_def using assms(1,4) by (simp add: Min_le_iff)
    thus ?thesis by simp
  qed
  thus ?thesis unfolding mpmul_def using assms(2,3) by (simp add: Max.bounded_iff)
qed

text \<open>Maximality: every subsolution is dominated by the residuated vector.\<close>

theorem mpres_greatest:
  assumes "finite I" "finite J" "I \<noteq> {}"
      and feas: "\<And>i. i \<in> I \<Longrightarrow> mpmul A J x i \<le> b i"
      and "j \<in> J"
  shows "x j \<le> mpres A I b j"
proof -
  have "x j \<le> b i - A i j" if "i \<in> I" for i
  proof -
    have "A i j + x j \<le> mpmul A J x i"
      unfolding mpmul_def using assms(2) \<open>j \<in> J\<close> by (simp add: Max_ge)
    also have "\<dots> \<le> b i" using feas that by simp
    finally show ?thesis by simp
  qed
  thus ?thesis unfolding mpres_def using assms(1,3) by (simp add: Min_ge_iff)
qed

text \<open>The same maximality with the feasibility premise written as a bounded
  quantifier (the convenient surface form).\<close>

corollary mpres_greatest':
  assumes "finite I" "finite J" "I \<noteq> {}"
      and "\<forall>i\<in>I. mpmul A J x i \<le> b i" "j \<in> J"
  shows "x j \<le> mpres A I b j"
  using assms by (intro mpres_greatest) auto

end
