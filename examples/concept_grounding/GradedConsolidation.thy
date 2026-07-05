(*
  GradedConsolidation.thy -- C8: the graded stability-plasticity certificate (the middle of the
  omega axis), plus why anchoring -- not gradient scaling -- is the mechanism that can carry it.

  Follow-on conjecture from the Wyly review (pil PR #10). Wyly replaces C4's binary freeze with one
  incidence-importance field omega per concept: protection is the quadratic anchor
  lam * omega * (param - consolidated)^2, the binary freeze is the omega -> infinity limit, and
  dropping below THETA is the prune. Consolidation.thy proved the limit; pic_krein's PIC_Prune
  proved the drop side. This theory proves the middle regime:

    * ANCHORED DRIFT BOUND: at any stationary point of task-loss + anchor -- where the task force
      gL balances the anchor force 2*lam*omega*(p - pbar) -- the drift obeys
      norm (p - pbar) <= G / (2*lam*omega) for any task-gradient bound G. Drift shrinks as 1/omega;
      the FREEZE LIMIT makes it explicit: omega >= G/(2*lam*eps) forces drift <= eps.
    * DRIFT-vs-MARGIN CERTIFICATES: a concept whose direction drifted by at most D keeps every
      membership whose margin exceeds D * norm r, and an argmax decode with margin > 2*D*norm r is
      preserved exactly -- the PIC_Quant/PIC_Prune triangle-budget shape, with drift as the
      perturbation. Composed (graded_membership_stability): stationarity + gradient bound + margin
      give EXACT per-input stability at finite omega -- C4's zero forgetting degrades gracefully
      into a certified, margin-gated regime, recovering C4 as omega -> infinity.
    * WHY NOT GRADIENT SCALING (the PR's Adam finding, made a theorem over its stated domain): for
      sign-normalized updates -- signSGD, the zeroth-order idealization of Adam -- multiplicative
      "protection" is a NO-OP: scaling the gradient by any positive factor leaves the entire
      trajectory unchanged (sign_updates_ignore_scaling), whereas a plain gradient step shrinks
      linearly with the factor (plain_update_scales). Protection must enter the LOSS (the anchor),
      not the gradient magnitude.

  Honest scope: stationarity is the stated regime -- nothing is claimed about whether or how fast
  training reaches it, nor about Adam's moment estimates beyond the sign idealization; margins are
  per-input (global stability needs the sup over inputs, as in PIC_Prune); the theta/gamma-turnstile
  correspondence is theorem-backed at the drop end (PIC_Prune) and the freeze end (C4 + this),
  `empirical` in between.
*)
theory GradedConsolidation
  imports Consolidation ConceptCells
begin

subsection \<open>Drift perturbs scores by at most D * norm r\<close>

lemma inner_drift_bound:
  fixes v v' :: "'a::real_inner"
  assumes "norm (v' - v) \<le> D"
  shows "\<bar>v' \<bullet> r - v \<bullet> r\<bar> \<le> D * norm r"
proof -
  have "\<bar>v' \<bullet> r - v \<bullet> r\<bar> = \<bar>(v' - v) \<bullet> r\<bar>" by (simp add: inner_diff_left)
  also have "\<dots> \<le> norm (v' - v) * norm r" by (rule Cauchy_Schwarz_ineq2)
  also have "\<dots> \<le> D * norm r" by (rule mult_right_mono[OF assms norm_ge_zero])
  finally show ?thesis .
qed

subsection \<open>The anchored drift bound and the freeze limit\<close>

text \<open>At a stationary point of task-loss + quadratic anchor, the anchor force balances the task
      force, so the drift is at most the task-gradient bound over the anchor stiffness.\<close>
theorem anchored_drift_bound:
  fixes p pbar gL :: "'a::real_normed_vector" and lam om G :: real
  assumes stat: "gL + (2 * lam * om) *\<^sub>R (p - pbar) = 0"
      and gb: "norm gL \<le> G" and lam: "0 < lam" and om: "0 < om"
  shows "norm (p - pbar) \<le> G / (2 * lam * om)"
proof -
  have pos: "0 < 2 * lam * om" using lam om by simp
  have "(2 * lam * om) *\<^sub>R (p - pbar) = - gL"
    using stat by (simp add: add_eq_0_iff)
  hence "norm ((2 * lam * om) *\<^sub>R (p - pbar)) = norm gL" by simp
  hence "\<bar>2 * lam * om\<bar> * norm (p - pbar) = norm gL" by simp
  hence key: "2 * lam * om * norm (p - pbar) \<le> G" using pos gb by simp
  thus ?thesis using pos by (simp add: pos_le_divide_eq mult.commute)
qed

text \<open>The explicit freeze schedule: incidence importance omega >= G/(2*lam*eps) caps the drift at
      eps -- the binary freeze (drift zero) is the omega -> infinity limit, quantitatively.\<close>
corollary freeze_limit:
  fixes p pbar gL :: "'a::real_normed_vector" and lam om G eps :: real
  assumes stat: "gL + (2 * lam * om) *\<^sub>R (p - pbar) = 0"
      and gb: "norm gL \<le> G" and lam: "0 < lam" and om: "0 < om"
      and eps: "0 < eps" and big: "G / (2 * lam * eps) \<le> om"
  shows "norm (p - pbar) \<le> eps"
proof -
  have p1: "0 < 2 * lam * eps" using lam eps by simp
  have p2: "0 < 2 * lam * om" using lam om by simp
  have "norm (p - pbar) \<le> G / (2 * lam * om)"
    by (rule anchored_drift_bound[OF stat gb lam om])
  also have "\<dots> \<le> eps"
  proof -
    have "G \<le> om * (2 * lam * eps)" using big p1 by (simp add: pos_divide_le_eq)
    hence "G \<le> eps * (2 * lam * om)" by (simp add: algebra_simps)
    thus ?thesis using p2 by (simp add: pos_divide_le_eq)
  qed
  finally show ?thesis .
qed

subsection \<open>Drift-vs-margin certificates: membership and decode\<close>

text \<open>A membership whose margin beats the drift budget D * norm r is preserved exactly.\<close>
theorem drifted_membership_preserved:
  fixes u u' :: "'c \<Rightarrow> 'a::real_inner"
  assumes drift: "norm (u' c - u c) \<le> D"
      and margin: "D * norm r < \<bar>u c \<bullet> r - b c\<bar>"
  shows "fires u' b c r = fires u b c r"
proof -
  have pert: "\<bar>u' c \<bullet> r - u c \<bullet> r\<bar> \<le> D * norm r" by (rule inner_drift_bound[OF drift])
  have up: "u' c \<bullet> r - u c \<bullet> r \<le> D * norm r" by (rule abs_le_D1[OF pert])
  have lo: "- (u' c \<bullet> r - u c \<bullet> r) \<le> D * norm r" by (rule abs_le_D2[OF pert])
  show ?thesis
  proof (cases "b c \<le> u c \<bullet> r")
    case True
    hence m: "D * norm r < u c \<bullet> r - b c" using margin by simp
    have "b c \<le> u' c \<bullet> r" using lo m by linarith
    thus ?thesis using True unfolding fires_def by simp
  next
    case False
    hence neg: "u c \<bullet> r - b c < 0" by linarith
    have m: "D * norm r < b c - u c \<bullet> r" using margin abs_of_neg[OF neg] by simp
    have "\<not> b c \<le> u' c \<bullet> r" using up m by linarith
    thus ?thesis using False unfolding fires_def by simp
  qed
qed

text \<open>A strict winner stays the unique argmax.\<close>
lemma amax_strict_winner:
  fixes U :: "'v \<Rightarrow> 'a::real_inner"
  assumes v0: "v0 \<in> V"
      and str: "\<And>w. w \<in> V \<Longrightarrow> w \<noteq> v0 \<Longrightarrow> U w \<bullet> r < U v0 \<bullet> r"
  shows "amax V U r = {v0}"
proof (rule set_eqI)
  fix v
  show "v \<in> amax V U r \<longleftrightarrow> v \<in> {v0}"
  proof
    assume vin: "v \<in> amax V U r"
    hence vV: "v \<in> V" and best: "\<forall>w\<in>V. U w \<bullet> r \<le> U v \<bullet> r" unfolding amax_def by auto
    show "v \<in> {v0}"
    proof (cases "v = v0")
      case True thus ?thesis by simp
    next
      case False
      have "U v \<bullet> r < U v0 \<bullet> r" by (rule str[OF vV False])
      moreover have "U v0 \<bullet> r \<le> U v \<bullet> r" using best v0 by auto
      ultimately have False by linarith
      thus ?thesis ..
    qed
  next
    assume "v \<in> {v0}"
    hence v: "v = v0" by simp
    have all: "\<forall>w\<in>V. U w \<bullet> r \<le> U v0 \<bullet> r"
    proof
      fix w assume wV: "w \<in> V"
      show "U w \<bullet> r \<le> U v0 \<bullet> r"
      proof (cases "w = v0")
        case True thus ?thesis by simp
      next
        case False show ?thesis using str[OF wV False] by linarith
      qed
    qed
    show "v \<in> amax V U r" using v0 all unfolding amax_def v by simp
  qed
qed

text \<open>The decode certificate: if every readout direction drifted by at most D and the winner's
      margin beats twice the drift budget, the argmax decision is IDENTICAL before and after --
      the PIC_Prune/PIC_Quant triangle shape with drift as the perturbation.\<close>
theorem drifted_decode_preserved:
  fixes U U' :: "'v \<Rightarrow> 'a::real_inner"
  assumes drift: "\<And>v. v \<in> V \<Longrightarrow> norm (U' v - U v) \<le> D"
      and v0: "v0 \<in> V"
      and win: "\<And>w. w \<in> V \<Longrightarrow> w \<noteq> v0 \<Longrightarrow> U w \<bullet> r + 2 * (D * norm r) < U v0 \<bullet> r"
  shows "amax V U' r = {v0} \<and> amax V U r = {v0}"
proof -
  have D0: "0 \<le> D" by (rule order_trans[OF norm_ge_zero drift[OF v0]])
  have Dr0: "0 \<le> D * norm r" using D0 by (simp add: mult_nonneg_nonneg)
  have old: "amax V U r = {v0}"
  proof (rule amax_strict_winner[OF v0])
    fix w assume "w \<in> V" and "w \<noteq> v0"
    from win[OF this] Dr0 show "U w \<bullet> r < U v0 \<bullet> r" by linarith
  qed
  have new: "amax V U' r = {v0}"
  proof (rule amax_strict_winner[OF v0])
    fix w assume wV: "w \<in> V" and wne: "w \<noteq> v0"
    have pw: "\<bar>U' w \<bullet> r - U w \<bullet> r\<bar> \<le> D * norm r"
      by (rule inner_drift_bound[OF drift[OF wV]])
    have p0: "\<bar>U' v0 \<bullet> r - U v0 \<bullet> r\<bar> \<le> D * norm r"
      by (rule inner_drift_bound[OF drift[OF v0]])
    from win[OF wV wne] abs_le_D1[OF pw] abs_le_D2[OF p0]
    show "U' w \<bullet> r < U' v0 \<bullet> r" by linarith
  qed
  from new old show ?thesis by (rule conjI)
qed

subsection \<open>The composed graded-stability certificate\<close>

text \<open>Stationarity of the omega-anchored objective + task-gradient bound + membership margin give
      EXACT preservation at finite omega: C4's zero forgetting, margin-gated. As omega grows the
      required margin G/(2*lam*om) * norm r shrinks to zero -- the binary freeze is the limit.\<close>
corollary graded_membership_stability:
  fixes u u' :: "'c \<Rightarrow> 'a::real_inner" and gL :: 'a
  assumes stat: "gL + (2 * lam * om) *\<^sub>R (u' c - u c) = 0"
      and gb: "norm gL \<le> G" and lam: "0 < lam" and om: "0 < om"
      and margin: "G / (2 * lam * om) * norm r < \<bar>u c \<bullet> r - b c\<bar>"
  shows "fires u' b c r = fires u b c r"
proof -
  have drift: "norm (u' c - u c) \<le> G / (2 * lam * om)"
    by (rule anchored_drift_bound[OF stat gb lam om])
  show ?thesis
  proof (rule drifted_membership_preserved[where D = "G / (2 * lam * om)"])
    show "norm (u' c - u c) \<le> G / (2 * lam * om)" by (rule drift)
    show "G / (2 * lam * om) * norm r < \<bar>u c \<bullet> r - b c\<bar>" by (rule margin)
  qed
qed

subsection \<open>Why gradient scaling cannot protect under sign-normalized updates\<close>

text \<open>Scaling a gradient by any positive factor does not change its sign.\<close>
lemma sgn_scale_invariant:
  fixes x c :: real
  assumes "0 < c"
  shows "sgn (c * x) = sgn x"
  using assms by (simp add: sgn_mult)

text \<open>The PR's Adam finding, over its stated domain: for sign-normalized updates (signSGD, the
      zeroth-order idealization of Adam) an ARBITRARY positive per-step protection factor on the
      gradient leaves the entire training trajectory unchanged -- multiplicative protection is a
      provable no-op, which is why a 0.05x-scaled "protected" parameter still drifted freely.\<close>
theorem sign_updates_ignore_scaling:
  fixes p q :: "nat \<Rightarrow> real" and grad :: "nat \<Rightarrow> real \<Rightarrow> real"
    and c :: "nat \<Rightarrow> real" and eta :: real
  assumes init: "q 0 = p 0"
      and pos: "\<And>n. 0 < c n"
      and pstep: "\<And>n. p (Suc n) = p n - eta * sgn (grad n (p n))"
      and qstep: "\<And>n. q (Suc n) = q n - eta * sgn (c n * grad n (q n))"
  shows "q n = p n"
proof (induction n)
  case 0 show ?case by (rule init)
next
  case (Suc n)
  have "q (Suc n) = q n - eta * sgn (c n * grad n (q n))" by (rule qstep)
  also have "\<dots> = p n - eta * sgn (c n * grad n (p n))" by (simp add: Suc.IH)
  also have "\<dots> = p n - eta * sgn (grad n (p n))"
    by (simp add: sgn_scale_invariant[OF pos])
  also have "\<dots> = p (Suc n)" by (rule pstep[symmetric])
  finally show ?case .
qed

text \<open>The contrast: a PLAIN gradient step does shrink linearly with the protection factor -- the
      mechanism gradient scaling was (wrongly) expected to provide under Adam.\<close>
lemma plain_update_scales:
  fixes p eta c g :: real
  shows "\<bar>(p - eta * (c * g)) - p\<bar> = \<bar>c\<bar> * \<bar>eta * g\<bar>"
proof -
  have "(p - eta * (c * g)) - p = - (c * (eta * g))" by (simp add: algebra_simps)
  thus ?thesis by (simp add: abs_mult)
qed

end
