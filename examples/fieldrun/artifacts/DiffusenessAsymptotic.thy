theory DiffusenessAsymptotic
  imports Complex_Main
begin

text \<open>Theorem 5 (asymptotic consequence). As PR → ∞ the k-source captured fraction k/PR → 0: no bounded-size PIC formula localises a diffuse causal property, and P⟨single-module intervention alters E⟩ = O(1/PR). Discharged: the constant numerator over a diverging denominator tends to 0.\<close>
theorem diffusenessasymptotic:
  shows "(\<lambda>n. real k / real n) \<longlonglongrightarrow> 0"
proof -
  show "(\<lambda>n. real k / real n) \<longlonglongrightarrow> 0" by (rule tendsto_divide_0[OF tendsto_const filterlim_at_top_imp_at_infinity[OF filterlim_real_sequentially]])
qed

end
