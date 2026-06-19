theory Recoverability_Surface
  imports Recoverability
begin

text \<open>ALLOCATION thresholds on VARIANCE. The reverse-water-filling rate of a Gaussian mode is zero exactly when its variance is at or below the water level — a low-variance mode gets no rate, i.e. the SAE spends nothing reconstructing it. Cites `rd_rate_zero_iff`.\<close>
theorem waterfillingdrop:
  shows "th > 0 \<Longrightarrow> (rd_rate lam th = 0) = (lam \<le> th)"
proof -
  show "th > 0 \<Longrightarrow> (rd_rate lam th = 0) = (lam \<le> th)" by (rule rd_rate_zero_iff)
qed

text \<open>THE BRIDGE. Reconstruction-relevance (var_share) is detectability (fisher) scaled by the direction's OWN variance — so the two functionals are linked ONLY through that variance. Cites `fisher_var_share_bridge`.\<close>
theorem fishervarsharebridge:
  shows "s2 > 0 \<Longrightarrow> var_share c p V = fisher c s2 * (p * (1 - p) * s2 / V)"
proof -
  show "s2 > 0 \<Longrightarrow> var_share c p V = fisher c s2 * (p * (1 - p) * s2 / V)" by (rule fisher_var_share_bridge)
qed

text \<open>THE DIVERGENCE — "compression is variance-greedy, meaning is variance-cheap". For ANY target detectability F and ANY reconstruction-relevance threshold th, there is a feature exactly that detectable (fisher = F, a probe reads it) whose reconstruction-relevance falls below th (var_share < th, the variance-greedy SAE drops it). Detectability does NOT imply recoverability. Cites `present_not_allocated`.\<close>
theorem presentnotallocated:
  shows "F > 0 \<Longrightarrow> th > 0 \<Longrightarrow> 0 < p \<Longrightarrow> p < 1 \<Longrightarrow> V > 0 \<Longrightarrow> (\<exists>c s2. s2 > 0 \<and> c > 0 \<and> fisher c s2 = F \<and> var_share c p V < th)"
proof -
  show "F > 0 \<Longrightarrow> th > 0 \<Longrightarrow> 0 < p \<Longrightarrow> p < 1 \<Longrightarrow> V > 0 \<Longrightarrow> (\<exists>c s2. s2 > 0 \<and> c > 0 \<and> fisher c s2 = F \<and> var_share c p V < th)" by (rule present_not_allocated)
qed

text \<open>The asymmetry that names the mechanism: two features with the SAME detectability can sit on OPPOSITE sides of the water line — one dropped, one kept — ordered entirely by their variance. Detectability does not order recoverability. Cites `same_fisher_opposite_allocation`.\<close>
theorem samefisheroppositeallocation:
  shows "th > 0 \<Longrightarrow> 0 < p \<Longrightarrow> p < 1 \<Longrightarrow> F > 0 \<Longrightarrow> (\<exists>c1 s21 c2 s22. s21 > 0 \<and> s22 > 0 \<and> fisher c1 s21 = F \<and> fisher c2 s22 = F \<and> rd_rate (var_share c1 p 1) th = 0 \<and> rd_rate (var_share c2 p 1) th > 0)"
proof -
  show "th > 0 \<Longrightarrow> 0 < p \<Longrightarrow> p < 1 \<Longrightarrow> F > 0 \<Longrightarrow> (\<exists>c1 s21 c2 s22. s21 > 0 \<and> s22 > 0 \<and> fisher c1 s21 = F \<and> fisher c2 s22 = F \<and> rd_rate (var_share c1 p 1) th = 0 \<and> rd_rate (var_share c2 p 1) th > 0)" by (rule same_fisher_opposite_allocation)
qed

end
