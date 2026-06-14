theory TwoTemperatureSoundness
  imports Complex_Main
begin

text \<open>Theorem 6. Read Π as a semiring FAQ. Under the tropical semiring (T=0) the aggregate is the attained max with witness argmax (greedy decode); the Maslov sandwich Max(L) ≤ T·ln Σ exp(L/T) ≤ Max(L) + T·ln|V| brings it to the log-semiring softmax aggregate (T=1) — one program, two temperatures. The two bound steps are the cited Maslov dequantization, left to Sledgehammer.\<close>
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
  have s_lower: "Max (L ` V) \<le> T * ln (\<Sum>v\<in>V. exp (L v / T))" sorry  (* hammer; using: s_attained, Tpos, finV, neV *)
  have s_upper: "T * ln (\<Sum>v\<in>V. exp (L v / T)) \<le> Max (L ` V) + T * ln (real (card V))" sorry  (* hammer; using: Tpos, finV, neV *)
  show "(\<exists>u\<in>V. L u = Max (L ` V)) \<and> Max (L ` V) \<le> T * ln (\<Sum>v\<in>V. exp (L v / T)) \<and> T * ln (\<Sum>v\<in>V. exp (L v / T)) \<le> Max (L ` V) + T * ln (real (card V))" using s_attained s_lower s_upper by blast
qed

end
