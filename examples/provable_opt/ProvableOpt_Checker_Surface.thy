theory ProvableOpt_Checker_Surface
  imports ProvableOpt_Checker
begin

text \<open>FAITHFULNESS. The executable checker `echeck` decides exactly the syntactic demand-closure condition on the abstracted program — sound AND complete. So the Python tool's check has a precise kernel meaning. Cites `echeck_iff`.\<close>
theorem echeckiff:
  shows "echeck ER KD = syn_demand_closed (prog_of ER) (set KD)"
proof -
  show "echeck ER KD = syn_demand_closed (prog_of ER) (set KD)" by (rule echeck_iff)
qed

text \<open>A PASS from the executable checker yields the lossless decode guarantee directly — through the kernel bridge and ProvableOpt_Common, with no hand proof of demand-closure. Cites `echeck_lossless`.\<close>
theorem echecklossless:
  shows "echeck ER KD \<Longrightarrow> Q \<subseteq> set KD \<Longrightarrow> lfp (T_P (prog_of ER)) \<inter> Q = lfp (restrict_op (T_P (prog_of ER)) (set KD)) \<inter> Q"
proof -
  show "echeck ER KD \<Longrightarrow> Q \<subseteq> set KD \<Longrightarrow> lfp (T_P (prog_of ER)) \<inter> Q = lfp (restrict_op (T_P (prog_of ER)) (set KD)) \<inter> Q" by (rule echeck_lossless)
qed

text \<open>THE PAYOFF. The lossless decode guarantee for the concrete `lastpos` program, obtained by EXECUTING the verified checker (`by eval` inside the proof) — the verdict is computed by kernel-trusted code, not asserted by an external tool. Cites `executable_checker_certifies_lossless`.\<close>
theorem executablecheckercertifieslossless:
  shows "lfp (T_P (dprog 5)) \<inter> {DLogit} = lfp (restrict_op (T_P (dprog 5)) (dkeep 5)) \<inter> {DLogit}"
proof -
  show "lfp (T_P (dprog 5)) \<inter> {DLogit} = lfp (restrict_op (T_P (dprog 5)) (dkeep 5)) \<inter> {DLogit}" by (rule executable_checker_certifies_lossless)
qed

end
