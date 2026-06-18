(*
  BalancedTernary.thy -- every integer is a balanced-ternary combination.

  The mathematical crux of "lossless transformation to BitNet by expansion": a
  finite-precision (integer) weight decomposes EXACTLY into ternary {-1, 0, 1} digits times
  powers of 3,

        n  =  SUM_{j < K} t_j * 3^j ,   t_j in {-1, 0, 1}.

  This is the balanced-ternary numeral system. It is what makes a lossless ternary
  realization possible (Lossless.thy): a real weight at finite precision is exactly a sum
  of ternary digits, so no information is lost -- only the representation expands.
*)

theory BalancedTernary
  imports Complex_Main
begin

theorem balanced_ternary_exists:
  fixes n :: int
  shows "\<exists>ts. (\<forall>d\<in>set ts. d \<in> {-1, 0, 1}) \<and> n = (\<Sum>j<length ts. ts ! j * 3 ^ j)"
proof (induction "nat \<bar>n\<bar>" arbitrary: n rule: less_induct)
  case less
  show ?case
  proof (cases "n = 0")
    case True
    show ?thesis by (rule exI[of _ "[]::int list"]) (simp add: True)
  next
    case False
    define d where "d = (n + 1) mod 3 - 1"
    define q where "q = (n + 1) div 3"
    have d_set: "d \<in> {-1, 0, 1}"
    proof -
      have "(n + 1) mod 3 - 1 = - 1 \<or> (n + 1) mod 3 - 1 = 0 \<or> (n + 1) mod 3 - 1 = 1"
        by presburger
      thus ?thesis unfolding d_def by auto
    qed
    have nq: "n = 3 * q + d" unfolding q_def d_def by presburger
    have meas: "nat \<bar>q\<bar> < nat \<bar>n\<bar>"
    proof -
      have "\<bar>(n + 1) div 3\<bar> < \<bar>n\<bar>" using False by presburger
      thus ?thesis unfolding q_def by linarith
    qed
    obtain ts where ts: "\<forall>e\<in>set ts. e \<in> {-1, 0, 1}" "q = (\<Sum>j<length ts. ts ! j * 3 ^ j)"
      using less[OF meas] by blast
    have sum_eq: "(\<Sum>j<length (d # ts). (d # ts) ! j * 3 ^ j) = d + 3 * q"
    proof -
      have "(\<Sum>j<length (d # ts). (d # ts) ! j * 3 ^ j)
          = (\<Sum>j<Suc (length ts). (d # ts) ! j * 3 ^ j)" by simp
      also have "\<dots> = (d # ts) ! 0 * 3 ^ 0 + (\<Sum>j<length ts. (d # ts) ! Suc j * 3 ^ Suc j)"
        by (subst sum.lessThan_Suc_shift) simp
      also have "\<dots> = d + (\<Sum>j<length ts. 3 * (ts ! j * 3 ^ j))"
        by (simp add: mult_ac)
      also have "\<dots> = d + 3 * (\<Sum>j<length ts. ts ! j * 3 ^ j)"
        by (simp add: sum_distrib_left)
      also have "\<dots> = d + 3 * q" using ts(2) by simp
      finally show ?thesis .
    qed
    have "n = (\<Sum>j<length (d # ts). (d # ts) ! j * 3 ^ j)" using sum_eq nq by simp
    moreover have "\<forall>e\<in>set (d # ts). e \<in> {-1, 0, 1}" using d_set ts(1) by simp
    ultimately show ?thesis by blast
  qed
qed

end
