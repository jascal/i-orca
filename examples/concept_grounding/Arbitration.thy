(*
  Arbitration.thy -- C10: ARBITRATION DOMINANCE (support-weighted cover, made a theorem over its
  honest premise).

  Follow-on from the Wyly rule-library arc (pil wyly_lm_v5, "support-weighted cover"): replacing
  the runtime's fixed tier priority with per-answer confidence arbitration was worth more than
  every added rule family combined (+0.03..+0.05 on natural text, a DOUBLING of the certified
  core on code). This theory states exactly when and why that must happen -- and exactly what can
  void it, which is what the val-variance episodes observed.

  The structure is deliberately finite and elementary. Inputs are grouped into CELLS (the
  arbitration keys: for table rules, the fired key; in the limit, single inputs); w is a
  nonnegative weight per cell (the empirical evaluation measure); app gives the rules applicable
  in a cell; acc r c is rule r's TRUE accuracy on cell c under that measure. A POLICY chooses an
  applicable rule per cell; its value is the weighted sum of chosen accuracies -- i.e., expected
  agreement.

    * ARGMAX_POLICY_OPTIMAL: the policy that picks a per-cell accuracy maximizer dominates EVERY
      policy -- in particular every fixed priority order (PRIORITY_DOMINATED). This is the
      support-weighted cover's guarantee, and its premise is CALIBRATION: the arbiter must rank
      rules by their true per-cell accuracy.
    * MISCALIBRATION_BOUND: if the arbiter instead maximizes an ESTIMATE chat with
      |chat - acc| <= eps per (rule, cell), its value is within 2*eps*(total weight) of optimal.
      The bound is the val-variance lesson as algebra: eps is exactly what low-support estimated
      confidences inflate, and at large eps the guarantee is vacuous -- which is why support
      pre-gates and per-family thresholds were needed empirically.

  Honest scope: calibration is per (rule, cell) ON THE EVALUATION MEASURE -- a strong premise,
  approximated in practice by per-key Laplace-shrunk determinism (tables) and held-out
  fired-accuracy (scalar kinds); nothing is claimed about generalization from the estimation
  measure to a different test measure beyond the eps envelope; abstention is modeled by including
  a "soft fallback" rule in app.
*)
theory Arbitration
  imports Complex_Main
begin

section \<open>Policies over cells and their value\<close>

definition polvalue :: "('c \<Rightarrow> real) \<Rightarrow> ('r \<Rightarrow> 'c \<Rightarrow> real) \<Rightarrow> ('c \<Rightarrow> 'r) \<Rightarrow> 'c set \<Rightarrow> real" where
  "polvalue w acc pol C = (\<Sum>c\<in>C. w c * acc (pol c) c)"

section \<open>C10(i): calibrated argmax dominates every policy\<close>

theorem argmax_policy_optimal:
  assumes wnn: "\<And>c. c \<in> C \<Longrightarrow> w c \<ge> 0"
      and pol_app: "\<And>c. c \<in> C \<Longrightarrow> pol c \<in> app c"
      and opt_app: "\<And>c. c \<in> C \<Longrightarrow> opt c \<in> app c"
      and opt_max: "\<And>c r. c \<in> C \<Longrightarrow> r \<in> app c \<Longrightarrow> acc r c \<le> acc (opt c) c"
  shows "polvalue w acc pol C \<le> polvalue w acc opt C"
  unfolding polvalue_def
proof (rule sum_mono)
  fix c assume c: "c \<in> C"
  have "acc (pol c) c \<le> acc (opt c) c"
    using c pol_app opt_max by blast
  then show "w c * acc (pol c) c \<le> w c * acc (opt c) c"
    using wnn[OF c] by (rule mult_left_mono)
qed

text \<open>A fixed priority order is one particular policy (choose the first applicable rule in a
  fixed list); it is therefore dominated. We state the corollary abstractly: ANY selection that
  is a function of the cell is dominated -- priority orders, tier orders, and the learned judge's
  own history included.\<close>

corollary priority_dominated:
  assumes "\<And>c. c \<in> C \<Longrightarrow> w c \<ge> 0"
      and "\<And>c. c \<in> C \<Longrightarrow> priority c \<in> app c"
      and "\<And>c. c \<in> C \<Longrightarrow> opt c \<in> app c"
      and "\<And>c r. c \<in> C \<Longrightarrow> r \<in> app c \<Longrightarrow> acc r c \<le> acc (opt c) c"
  shows "polvalue w acc priority C \<le> polvalue w acc opt C"
  using assms by (rule argmax_policy_optimal)

section \<open>C10(ii): the miscalibration envelope\<close>

theorem miscalibration_bound:
  assumes fin: "finite C"
      and wnn: "\<And>c. c \<in> C \<Longrightarrow> w c \<ge> 0"
      and sel_app: "\<And>c. c \<in> C \<Longrightarrow> sel c \<in> app c"
      and opt_app: "\<And>c. c \<in> C \<Longrightarrow> opt c \<in> app c"
      and sel_argmax: "\<And>c r. c \<in> C \<Longrightarrow> r \<in> app c \<Longrightarrow> chat r c \<le> chat (sel c) c"
      and cal: "\<And>c r. c \<in> C \<Longrightarrow> r \<in> app c \<Longrightarrow> \<bar>chat r c - acc r c\<bar> \<le> eps"
  shows "polvalue w acc opt C - polvalue w acc sel C \<le> 2 * eps * (\<Sum>c\<in>C. w c)"
proof -
  have cellwise: "acc (opt c) c - acc (sel c) c \<le> 2 * eps" if c: "c \<in> C" for c
  proof -
    have "acc (opt c) c \<le> chat (opt c) c + eps"
      using cal[OF c opt_app[OF c]] by auto
    also have "\<dots> \<le> chat (sel c) c + eps"
      using sel_argmax[OF c opt_app[OF c]] by simp
    also have "\<dots> \<le> (acc (sel c) c + eps) + eps"
      using cal[OF c sel_app[OF c]] by auto
    finally show ?thesis by simp
  qed
  have "polvalue w acc opt C - polvalue w acc sel C
      = (\<Sum>c\<in>C. w c * acc (opt c) c - w c * acc (sel c) c)"
    by (simp add: polvalue_def sum_subtractf)
  also have "\<dots> = (\<Sum>c\<in>C. w c * (acc (opt c) c - acc (sel c) c))"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> (\<Sum>c\<in>C. w c * (2 * eps))"
  proof (rule sum_mono)
    fix c assume c: "c \<in> C"
    show "w c * (acc (opt c) c - acc (sel c) c) \<le> w c * (2 * eps)"
      using cellwise[OF c] wnn[OF c] by (rule mult_left_mono)
  qed
  also have "\<dots> = (\<Sum>c\<in>C. 2 * eps * w c)"
    by (rule sum.cong[OF refl]) (rule mult.commute)
  also have "\<dots> = 2 * eps * (\<Sum>c\<in>C. w c)"
    by (rule sum_distrib_left[symmetric])
  finally show ?thesis .
qed

end
