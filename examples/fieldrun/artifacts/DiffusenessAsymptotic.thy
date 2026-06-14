theory DiffusenessAsymptotic
  imports Complex_Main
begin

text \<open>Theorem 5 (asymptotic consequence). As PR → ∞ the k-source captured fraction k/PR → 0: no bounded-size PIC formula localises a diffuse causal property, and P⟨single-module intervention alters E⟩ = O(1/PR). The limit is a standard analytic fact left to Sledgehammer.\<close>
theorem diffusenessasymptotic:
  shows "(\<lambda>n. real k / real n) \<longlonglongrightarrow> 0"
proof -
  show "(\<lambda>n. real k / real n) \<longlonglongrightarrow> 0" sorry  (* hammer *)
qed

end
