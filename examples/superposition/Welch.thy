(*
  Welch.thy -- the Welch bound and the cost of superposition.

  The mathematical jewel behind "Toy Models of Superposition": you cannot pack n
  feature directions into m < n dimensions without interference. Everything follows
  from one elementary sum-of-squares inequality (welch_sos),

        SUM_{i,j} <v_i,v_j>^2  >=  (SUM_i <v_i,v_i>)^2 / m,     m = card K,

  proved here from scratch (Cauchy-Schwarz on the Gram diagonal, no matrix library).
  Its consequences for unit feature vectors:

    orth_capacity                  : orthogonal features fit only m of them (n <= m)
                                     -- "dense regime, no superposition".
    superposition_forces_interference : n > m forces some pair with <v_i,v_j> != 0
                                     -- representing more features than dimensions is
                                     impossible without interference.
    welch_offdiag                  : the total off-diagonal interference is at least
                                     n(n-m)/m -- the Welch bound, quantifying the cost
                                     that grows as you overpack.
*)

theory Welch
  imports Superposition "HOL-Analysis.Convex"
begin

text \<open>The Welch sum-of-squares inequality. Proof: expand each inner product over the
  coordinate set, swap the feature and coordinate sums to recognise the Gram matrix
  M b b' = SUM_i v_i[b] v_i[b'], drop the off-diagonal (non-negative) Gram entries, and
  apply Cauchy-Schwarz to the diagonal.\<close>

theorem welch_sos:
  fixes v :: "'i \<Rightarrow> 'k \<Rightarrow> real"
  assumes finI: "finite I" and finK: "finite K"
  shows "(\<Sum>i\<in>I. \<Sum>j\<in>I. (ip K (v i) (v j))\<^sup>2) \<ge> (\<Sum>i\<in>I. ip K (v i) (v i))\<^sup>2 / card K"
proof -
  define M where "M = (\<lambda>b b'. \<Sum>i\<in>I. v i b * v i b')"
  have reorder: "(\<Sum>i\<in>I. \<Sum>j\<in>I. \<Sum>b\<in>K. \<Sum>b'\<in>K. P i j b b')
               = (\<Sum>b\<in>K. \<Sum>b'\<in>K. \<Sum>i\<in>I. \<Sum>j\<in>I. P i j b b')" for P :: "'i\<Rightarrow>'i\<Rightarrow>'k\<Rightarrow>'k\<Rightarrow>real"
  proof -
    have "(\<Sum>i\<in>I. \<Sum>j\<in>I. \<Sum>b\<in>K. \<Sum>b'\<in>K. P i j b b')
        = (\<Sum>z\<in>I\<times>I\<times>K\<times>K. case z of (i,j,b,b') \<Rightarrow> P i j b b')"
      by (simp add: sum.cartesian_product)
    also have "\<dots> = (\<Sum>w\<in>K\<times>K\<times>I\<times>I. case w of (b,b',i,j) \<Rightarrow> P i j b b')"
      by (rule sum.reindex_bij_witness[where i="\<lambda>(i,j,b,b'). (b,b',i,j)"
                                         and j="\<lambda>(b,b',i,j). (i,j,b,b')"]) auto
    also have "\<dots> = (\<Sum>b\<in>K. \<Sum>b'\<in>K. \<Sum>i\<in>I. \<Sum>j\<in>I. P i j b b')"
      by (simp add: sum.cartesian_product)
    finally show ?thesis .
  qed
  have key: "(\<Sum>i\<in>I. \<Sum>j\<in>I. (ip K (v i) (v j))\<^sup>2) = (\<Sum>b\<in>K. \<Sum>b'\<in>K. (M b b')\<^sup>2)"
  proof -
    have "(\<Sum>i\<in>I. \<Sum>j\<in>I. (ip K (v i) (v j))\<^sup>2)
        = (\<Sum>i\<in>I. \<Sum>j\<in>I. \<Sum>b\<in>K. \<Sum>b'\<in>K. (v i b * v j b) * (v i b' * v j b'))"
    proof (intro sum.cong refl)
      fix i j
      have "(ip K (v i) (v j))\<^sup>2 = (\<Sum>b\<in>K. v i b * v j b) * (\<Sum>b'\<in>K. v i b' * v j b')"
        by (simp add: ip_def power2_eq_square)
      also have "\<dots> = (\<Sum>b\<in>K. \<Sum>b'\<in>K. (v i b * v j b) * (v i b' * v j b'))"
        by (rule sum_product)
      finally show "(ip K (v i) (v j))\<^sup>2 = (\<Sum>b\<in>K. \<Sum>b'\<in>K. (v i b * v j b) * (v i b' * v j b'))" .
    qed
    also have "\<dots> = (\<Sum>b\<in>K. \<Sum>b'\<in>K. \<Sum>i\<in>I. \<Sum>j\<in>I. (v i b * v j b) * (v i b' * v j b'))"
      by (rule reorder)
    also have "\<dots> = (\<Sum>b\<in>K. \<Sum>b'\<in>K. (M b b')\<^sup>2)"
    proof (intro sum.cong refl)
      fix b b'
      have "(\<Sum>i\<in>I. \<Sum>j\<in>I. (v i b * v j b) * (v i b' * v j b'))
          = (\<Sum>i\<in>I. \<Sum>j\<in>I. (v i b * v i b') * (v j b * v j b'))"
        by (simp add: mult.commute mult.left_commute)
      also have "\<dots> = (\<Sum>i\<in>I. v i b * v i b') * (\<Sum>j\<in>I. v j b * v j b')"
        by (rule sum_product[symmetric])
      also have "\<dots> = (M b b')\<^sup>2" by (simp add: M_def power2_eq_square)
      finally show "(\<Sum>i\<in>I. \<Sum>j\<in>I. (v i b * v j b) * (v i b' * v j b')) = (M b b')\<^sup>2" .
    qed
    finally show ?thesis .
  qed
  have diag: "(\<Sum>b\<in>K. (M b b)\<^sup>2) \<le> (\<Sum>b\<in>K. \<Sum>b'\<in>K. (M b b')\<^sup>2)"
  proof (rule sum_mono)
    fix b assume "b \<in> K"
    show "(M b b)\<^sup>2 \<le> (\<Sum>b'\<in>K. (M b b')\<^sup>2)"
      using \<open>b \<in> K\<close> finK by (intro member_le_sum) auto
  qed
  have cs: "(\<Sum>b\<in>K. M b b)\<^sup>2 \<le> (\<Sum>b\<in>K. (M b b)\<^sup>2) * card K"
    by (rule sum_squared_le_sum_of_squares)
  have trace: "(\<Sum>b\<in>K. M b b) = (\<Sum>i\<in>I. ip K (v i) (v i))"
    unfolding M_def ip_def by (rule sum.swap)
  show ?thesis
  proof (cases "card K = 0")
    case True
    hence "K = {}" using finK by simp
    thus ?thesis by (simp add: ip_def True)
  next
    case False
    hence cardpos: "0 < card K" by simp
    have "(\<Sum>i\<in>I. ip K (v i) (v i))\<^sup>2 = (\<Sum>b\<in>K. M b b)\<^sup>2" by (simp add: trace)
    also have "\<dots> \<le> (\<Sum>b\<in>K. (M b b)\<^sup>2) * card K" by (rule cs)
    also have "\<dots> \<le> (\<Sum>b\<in>K. \<Sum>b'\<in>K. (M b b')\<^sup>2) * card K"
      using diag cardpos by (simp add: mult_right_mono)
    finally have "(\<Sum>i\<in>I. ip K (v i) (v i))\<^sup>2 \<le> (\<Sum>b\<in>K. \<Sum>b'\<in>K. (M b b')\<^sup>2) * card K" .
    hence "(\<Sum>i\<in>I. ip K (v i) (v i))\<^sup>2 / card K \<le> (\<Sum>b\<in>K. \<Sum>b'\<in>K. (M b b')\<^sup>2)"
      using cardpos by (simp add: divide_le_eq)
    thus ?thesis using key by simp
  qed
qed

text \<open>For unit vectors the diagonal is 1: each feature's row of squared inner products
  sums to 1 plus its interference with the rest.\<close>

lemma row_split:
  assumes finI: "finite I" and iI: "i \<in> I" and unit: "ip K (v i) (v i) = 1"
  shows "(\<Sum>j\<in>I. (ip K (v i) (v j))\<^sup>2) = 1 + (\<Sum>j\<in>I - {i}. (ip K (v i) (v j))\<^sup>2)"
  using unit by (simp add: sum.remove[OF finI iI])

lemma trace_unit:
  assumes finI: "finite I" and unit: "\<And>i. i \<in> I \<Longrightarrow> ip K (v i) (v i) = 1"
  shows "(\<Sum>i\<in>I. ip K (v i) (v i)) = real (card I)"
proof -
  have "(\<Sum>i\<in>I. ip K (v i) (v i)) = (\<Sum>i\<in>I. 1)"
    by (rule sum.cong[OF refl]) (simp add: unit)
  thus ?thesis by simp
qed

text \<open>Orthogonal capacity: m orthonormal directions are the most that fit -- without
  superposition a model represents at most m = card K features (the dense regime).\<close>

theorem orth_capacity:
  fixes v :: "'i \<Rightarrow> 'k \<Rightarrow> real"
  assumes finI: "finite I" and finK: "finite K"
      and unit: "\<And>i. i \<in> I \<Longrightarrow> ip K (v i) (v i) = 1"
      and orth: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> ip K (v i) (v j) = 0"
  shows "card I \<le> card K"
proof (cases "I = {}")
  case True thus ?thesis by simp
next
  case False
  then obtain i0 where i0: "i0 \<in> I" by auto
  have Ipos: "0 < card I" using False finI by (simp add: card_gt_0_iff)
  have Kpos: "0 < card K"
  proof (rule ccontr)
    assume "\<not> 0 < card K"
    hence "K = {}" using finK by simp
    hence "ip K (v i0) (v i0) = 0" by (simp add: ip_def)
    thus False using unit[OF i0] by simp
  qed
  have sos: "(\<Sum>i\<in>I. \<Sum>j\<in>I. (ip K (v i) (v j))\<^sup>2) = real (card I)"
  proof -
    have "(\<Sum>i\<in>I. \<Sum>j\<in>I. (ip K (v i) (v j))\<^sup>2) = (\<Sum>i\<in>I. 1)"
    proof (rule sum.cong[OF refl])
      fix i assume i: "i \<in> I"
      have z: "(\<Sum>j\<in>I - {i}. (ip K (v i) (v j))\<^sup>2) = 0"
      proof (intro sum.neutral ballI)
        fix j assume "j \<in> I - {i}"
        hence "ip K (v i) (v j) = 0" using orth i by auto
        thus "(ip K (v i) (v j))\<^sup>2 = 0" by simp
      qed
      have "(\<Sum>j\<in>I. (ip K (v i) (v j))\<^sup>2) = 1 + (\<Sum>j\<in>I - {i}. (ip K (v i) (v j))\<^sup>2)"
        using finI i unit[OF i] by (rule row_split)
      thus "(\<Sum>j\<in>I. (ip K (v i) (v j))\<^sup>2) = 1" using z by simp
    qed
    thus ?thesis by simp
  qed
  have tr: "(\<Sum>i\<in>I. ip K (v i) (v i)) = real (card I)"
    using finI unit by (rule trace_unit)
  have "(real (card I))\<^sup>2 / real (card K) \<le> real (card I)"
    using welch_sos[where v=v, OF finI finK] by (simp add: sos tr)
  hence "(real (card I))\<^sup>2 \<le> real (card I) * real (card K)"
    using Kpos by (simp add: pos_divide_le_eq)
  hence "real (card I) \<le> real (card K)"
    using Ipos by (simp add: power2_eq_square)
  thus ?thesis by simp
qed

text \<open>Superposition forces interference: representing more features than dimensions is
  impossible without some non-zero off-diagonal inner product.\<close>

theorem superposition_forces_interference:
  fixes v :: "'i \<Rightarrow> 'k \<Rightarrow> real"
  assumes finI: "finite I" and finK: "finite K"
      and unit: "\<And>i. i \<in> I \<Longrightarrow> ip K (v i) (v i) = 1"
      and over: "card K < card I"
  shows "\<exists>i\<in>I. \<exists>j\<in>I. i \<noteq> j \<and> ip K (v i) (v j) \<noteq> 0"
proof (rule ccontr)
  assume "\<not> (\<exists>i\<in>I. \<exists>j\<in>I. i \<noteq> j \<and> ip K (v i) (v j) \<noteq> 0)"
  hence "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> ip K (v i) (v j) = 0" by blast
  with finI finK unit have "card I \<le> card K" by (rule orth_capacity)
  thus False using over by simp
qed

text \<open>The Welch bound (off-diagonal-sum form): total interference is at least
  n(n-m)/m, which is strictly positive exactly when n > m -- the cost of overpacking.\<close>

theorem welch_offdiag:
  fixes v :: "'i \<Rightarrow> 'k \<Rightarrow> real"
  assumes finI: "finite I" and finK: "finite K" and Kpos: "0 < card K"
      and unit: "\<And>i. i \<in> I \<Longrightarrow> ip K (v i) (v i) = 1"
  shows "(\<Sum>i\<in>I. \<Sum>j\<in>I - {i}. (ip K (v i) (v j))\<^sup>2)
         \<ge> real (card I) * (real (card I) - real (card K)) / real (card K)"
proof -
  define D where "D = (\<Sum>i\<in>I. \<Sum>j\<in>I - {i}. (ip K (v i) (v j))\<^sup>2)"
  have lhs: "(\<Sum>i\<in>I. \<Sum>j\<in>I. (ip K (v i) (v j))\<^sup>2) = real (card I) + D"
  proof -
    have "(\<Sum>i\<in>I. \<Sum>j\<in>I. (ip K (v i) (v j))\<^sup>2)
        = (\<Sum>i\<in>I. 1 + (\<Sum>j\<in>I - {i}. (ip K (v i) (v j))\<^sup>2))"
      by (rule sum.cong[OF refl]) (simp add: row_split[OF finI _ ] unit)
    also have "\<dots> = real (card I) + D"
      by (simp add: sum.distrib D_def)
    finally show ?thesis .
  qed
  have tr: "(\<Sum>i\<in>I. ip K (v i) (v i)) = real (card I)"
    using finI unit by (rule trace_unit)
  have "(real (card I))\<^sup>2 / real (card K) \<le> real (card I) + D"
    using welch_sos[where v=v, OF finI finK] by (simp only: lhs tr)
  hence "D \<ge> (real (card I))\<^sup>2 / real (card K) - real (card I)" by simp
  also have "(real (card I))\<^sup>2 / real (card K) - real (card I)
           = real (card I) * (real (card I) - real (card K)) / real (card K)"
  proof -
    have m: "real (card K) \<noteq> (0::real)" using Kpos by simp
    have "(real (card I))\<^sup>2 / real (card K) - real (card I)
        = ((real (card I))\<^sup>2 - real (card I) * real (card K)) / real (card K)"
      using m by (simp add: field_simps)
    also have "\<dots> = real (card I) * (real (card I) - real (card K)) / real (card K)"
      by (simp add: power2_eq_square algebra_simps)
    finally show ?thesis .
  qed
  finally show ?thesis unfolding D_def .
qed

text \<open>Surface forms of the three corollaries, with the per-feature unit-norm /
  orthogonality hypotheses written as bounded quantifiers.\<close>

corollary orth_capacity':
  assumes "finite I" and "finite K"
      and "\<forall>i\<in>I. ip K (v i) (v i) = 1"
      and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> ip K (v i) (v j) = 0"
  shows "card I \<le> card K"
  using assms by (intro orth_capacity) auto

corollary superposition_forces_interference':
  assumes "finite I" and "finite K"
      and "\<forall>i\<in>I. ip K (v i) (v i) = 1" and "card K < card I"
  shows "\<exists>i\<in>I. \<exists>j\<in>I. i \<noteq> j \<and> ip K (v i) (v j) \<noteq> 0"
  using assms by (intro superposition_forces_interference) auto

corollary welch_offdiag':
  assumes "finite I" and "finite K" and "0 < card K"
      and "\<forall>i\<in>I. ip K (v i) (v i) = 1"
  shows "(\<Sum>i\<in>I. \<Sum>j\<in>I - {i}. (ip K (v i) (v j))\<^sup>2)
         \<ge> real (card I) * (real (card I) - real (card K)) / real (card K)"
  using assms by (intro welch_offdiag) auto

end
