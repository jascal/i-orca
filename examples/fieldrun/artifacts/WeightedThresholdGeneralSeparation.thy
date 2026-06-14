theory WeightedThresholdGeneralSeparation
  imports Complex_Main
begin

text \<open>Theorem 3 (general half, OPEN per the paper). Whether every μ_t = 0 conclusion is in general inexpressible in the Horn / ∩–∪ fragment yet expressible with the weighted-threshold connective is left open ("proving the separation in general rather than only on the measured μ_t = 0 set is left open"). i-orca records it as an explicit frontier hole.\<close>
theorem weightedthresholdgeneralseparation:
  shows "horn_expressible t \<longrightarrow> mu_t t \<noteq> (0::nat)"
proof -
  show "horn_expressible t \<longrightarrow> mu_t t \<noteq> (0::nat)" sorry  (* sketched *)
qed

end
