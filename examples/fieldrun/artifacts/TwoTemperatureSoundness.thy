theory TwoTemperatureSoundness
  imports Complex_Main
begin

text \<open>Theorem 6. Read Π as a semiring FAQ. Under the tropical semiring (T=0) the aggregate is the attained max with witness argmax (greedy decode); the Maslov sandwich Max(L) ≤ T·ln Σ exp(L/T) ≤ Max(L) + T·ln|V| brings it to the log-semiring softmax aggregate (T=1) — one program, two temperatures. Both bounds are now discharged: the max term is one summand of the sum (lower), and every term is at most the max term (upper).\<close>
theorem twotemperaturesoundness:
  assumes
    Tpos: "T > 0"
    and
    finV: "finite V"
    and
    neV: "V \<noteq> {}"
  shows "(\<exists>u\<in>V. L u = Max (L ` V)) \<and> Max (L ` V) \<le> T * ln (\<Sum>v\<in>V. exp (L v / T)) \<and> T * ln (\<Sum>v\<in>V. exp (L v / T)) \<le> Max (L ` V) + T * ln (real (card V))"
proof -
  have s_mem: "Max (L ` V) \<in> L ` V" using finV neV by (intro Max_in) auto
  have s_attained: "\<exists>u\<in>V. L u = Max (L ` V)" using s_mem by auto
  obtain u where s_obt: "u \<in> V \<and> L u = Max (L ` V)" using s_attained by blast
  have s_uV: "u \<in> V" using s_obt by simp
  have s_Lu: "L u = Max (L ` V)" using s_obt by simp
  have s_memle: "exp (L u / T) \<le> (\<Sum>v\<in>V. exp (L v / T))" using s_uV finV by (intro member_le_sum) auto
  have s_lestar: "exp (Max (L ` V) / T) \<le> (\<Sum>v\<in>V. exp (L v / T))" using s_memle s_Lu by simp
  have s_pos: "0 < (\<Sum>v\<in>V. exp (L v / T))" using finV neV by (simp add: sum_pos)
  have s_key: "Max (L ` V) / T \<le> ln (\<Sum>v\<in>V. exp (L v / T))" using s_lestar s_pos by (simp add: ln_ge_iff)
  have s_lower: "Max (L ` V) \<le> T * ln (\<Sum>v\<in>V. exp (L v / T))" using s_key Tpos by (simp add: pos_divide_le_eq mult.commute)
  have s_ucard: "0 < real (card V)" using finV neV by (simp add: card_gt_0_iff)
  have s_ub: "\<And>v. v \<in> V \<Longrightarrow> exp (L v / T) \<le> exp (Max (L ` V) / T)" using finV Tpos by (simp add: Max_ge divide_right_mono)
  have s_bound: "(\<Sum>v\<in>V. exp (L v / T)) \<le> real (card V) * exp (Max (L ` V) / T)" using s_ub by (simp add: sum_bounded_above)
  have s_lnbound: "ln (\<Sum>v\<in>V. exp (L v / T)) \<le> ln (real (card V) * exp (Max (L ` V) / T))" using s_bound s_pos by simp
  have s_lnsplit: "ln (real (card V) * exp (Max (L ` V) / T)) = ln (real (card V)) + Max (L ` V) / T" using s_ucard by (simp add: ln_mult)
  have s_key2: "ln (\<Sum>v\<in>V. exp (L v / T)) \<le> ln (real (card V)) + Max (L ` V) / T" using s_lnbound s_lnsplit by simp
  have s_tmul: "T * ln (\<Sum>v\<in>V. exp (L v / T)) \<le> T * (ln (real (card V)) + Max (L ` V) / T)" using s_key2 Tpos by (simp add: mult_left_mono)
  have s_tsimp: "T * (ln (real (card V)) + Max (L ` V) / T) = Max (L ` V) + T * ln (real (card V))" using Tpos by (simp add: field_simps)
  have s_upper: "T * ln (\<Sum>v\<in>V. exp (L v / T)) \<le> Max (L ` V) + T * ln (real (card V))" using s_tmul s_tsimp by simp
  show "(\<exists>u\<in>V. L u = Max (L ` V)) \<and> Max (L ` V) \<le> T * ln (\<Sum>v\<in>V. exp (L v / T)) \<and> T * ln (\<Sum>v\<in>V. exp (L v / T)) \<le> Max (L ` V) + T * ln (real (card V))" using s_attained s_lower s_upper by blast
qed

end
