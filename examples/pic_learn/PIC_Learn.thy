(*
  PIC_Learn.thy -- T-traj: TRAJECTORY DECISION PRESERVATION for a frame-learning loop.

  Context: the picard loop (PICARD_GOAL.md / PICARD_PROOF_PLAN.md, workspace root) alternates a
  placement step (encoder, frame frozen) with a frame step P3 that updates BOTH the frame U and
  the biases b (pil trains bias as a parameter -- pil/pil/learner.py), under the invariant that
  decisions on visited contexts are inviolable (PIC_SPEC sec 6 invariant S1).  This theory makes
  S1 a checkable certificate over a whole learning TRAJECTORY, not just one static perturbation.

  The design (extends pic_krein/PIC_Quant.thy, which holds b fixed -- a learning step does not):
    * step_logit_drift      -- Cauchy-Schwarz + triangle: a frame step with ||U'_v - U_v|| <= eps
                               AND |b'_v - b_v| <= beta perturbs each logit by at most rho*eps + beta
                               (rho = ||r|| bound).  The bias term is NOT optional: a certificate
                               that budgets only the frame silently validates while a trained bias
                               walks the decision across a facet.
    * margin_transfer       -- a delta-bounded logit perturbation degrades a UNIFORM margin m to
                               at least m - 2*delta.  No positivity needed: the inequality
                               telescopes through zero, so the trajectory induction is
                               unconditional and strictness enters only at the end.
    * step_decode_preserved -- the per-step runtime engine: if the CURRENT margin exceeds
                               2*(rho*eps + beta), this step preserves the decision.  With beta = 0
                               this is exactly PIC_Quant.quant_decode_preserved.
    * traj_decode_margin    -- telescoping: after tau steps the surviving uniform margin is
                               >= m - 2 * (SUM_{s<tau} rho*eps_s + beta_s).  Induction on tau.
    * traj_decode_preserved -- THE a-priori certificate: if the total drift budget satisfies
                               2 * (SUM_{s<T} rho*eps_s + beta_s) < m, every visited decision is
                               preserved at EVERY point of the trajectory.

  Honest scope: local (per context r, per visited target t) and silent below the budget -- the
  exact analogue of the 2*delta margin certificate's scope (proved tight in ProvableOpt_Margin).
  It says decisions SURVIVE the trajectory; it says nothing about margins improving (invariant
  S2 / certified-mass monotonicity is a separate, open target).  Discharging the premises on a
  real run = log max_v ||Delta U_v||, max_v |Delta b_v|, and the min visited margin at every P3
  step; the per-step engine is the runtime check, the budget theorem the a-priori one.
*)
theory PIC_Learn
  imports "HOL-Analysis.Analysis"
begin

text \<open>ONE LEARNING STEP -> LOGIT DRIFT.  A joint (frame, bias) update moves each logit by at most
  \<rho>*\<epsilon> + \<beta>: Cauchy-Schwarz on the frame part, triangle inequality to add the bias part.\<close>
lemma step_logit_drift:
  fixes r U U' :: "'a::real_inner" and b b' :: real
  assumes rbound: "norm r \<le> \<rho>" and rho0: "0 \<le> \<rho>"
      and ubound: "norm (U' - U) \<le> \<epsilon>"
      and bbound: "\<bar>b' - b\<bar> \<le> \<beta>"
  shows "\<bar>(inner r U' + b') - (inner r U + b)\<bar> \<le> \<rho> * \<epsilon> + \<beta>"
proof -
  have frame: "\<bar>inner r U' - inner r U\<bar> \<le> \<rho> * \<epsilon>"
  proof -
    have "\<bar>inner r U' - inner r U\<bar> = \<bar>inner r (U' - U)\<bar>" by (simp add: inner_diff_right)
    also have "\<dots> \<le> norm r * norm (U' - U)" by (rule Cauchy_Schwarz_ineq2)
    also have "\<dots> \<le> \<rho> * \<epsilon>"
      using rbound ubound rho0 by (intro mult_mono norm_ge_zero) auto
    finally show ?thesis .
  qed
  have "(inner r U' + b') - (inner r U + b) = (inner r U' - inner r U) + (b' - b)" by simp
  moreover have "\<bar>(inner r U' - inner r U) + (b' - b)\<bar>
                   \<le> \<bar>inner r U' - inner r U\<bar> + \<bar>b' - b\<bar>"
    by (rule abs_triangle_ineq)
  ultimately show ?thesis using frame bbound by linarith
qed

text \<open>MARGIN TRANSFER.  A \<delta>-bounded logit perturbation degrades a uniform margin m to m - 2*\<delta>.
  Crucially this needs NO sign condition on m - 2*\<delta>, so it can be iterated unconditionally;
  strict decode preservation is recovered at the end when the surviving margin is positive.\<close>
lemma margin_transfer:
  fixes L L' :: "'v \<Rightarrow> real"
  assumes win:  "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> L v + m \<le> L t"
      and pert: "\<forall>v\<in>V. \<bar>L' v - L v\<bar> \<le> \<delta>"
      and tV:   "t \<in> V"
  shows "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> L' v + (m - 2 * \<delta>) \<le> L' t"
proof (intro ballI impI)
  fix v assume vV: "v \<in> V" and vt: "v \<noteq> t"
  have wv: "L v + m \<le> L t" using win vV vt by blast
  have pv: "\<bar>L' v - L v\<bar> \<le> \<delta>" using pert vV by blast
  have pt: "\<bar>L' t - L t\<bar> \<le> \<delta>" using pert tV by blast
  from wv pv pt show "L' v + (m - 2 * \<delta>) \<le> L' t" unfolding abs_le_iff by linarith
qed

text \<open>SURVIVING MARGIN, ONE STEP.  After one joint (U, b) learning step the uniform margin
  degrades by at most twice the drift budget: m survives as m - 2*(\<rho>*\<epsilon> + \<beta>).  Needs no sign
  condition, and is useful on its own even when only positivity is ultimately wanted (it is the
  quantity a P3 loop should LOG each iteration, not just threshold).\<close>
theorem step_margin_survives:
  fixes U U' :: "'v \<Rightarrow> 'a::real_inner" and b b' :: "'v \<Rightarrow> real" and r :: 'a
  assumes tV:     "t \<in> V"
      and rbound: "norm r \<le> \<rho>" and rho0: "0 \<le> \<rho>"
      and ubound: "\<forall>v\<in>V. norm (U' v - U v) \<le> \<epsilon>"
      and bbound: "\<forall>v\<in>V. \<bar>b' v - b v\<bar> \<le> \<beta>"
      and margin: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> (inner r (U v) + b v) + m \<le> (inner r (U t) + b t)"
  shows "\<forall>v\<in>V. v \<noteq> t \<longrightarrow>
           (inner r (U' v) + b' v) + (m - 2 * (\<rho> * \<epsilon> + \<beta>)) \<le> (inner r (U' t) + b' t)"
proof -
  have pert: "\<forall>v\<in>V. \<bar>(inner r (U' v) + b' v) - (inner r (U v) + b v)\<bar> \<le> \<rho> * \<epsilon> + \<beta>"
  proof (intro ballI)
    fix v assume vV: "v \<in> V"
    show "\<bar>(inner r (U' v) + b' v) - (inner r (U v) + b v)\<bar> \<le> \<rho> * \<epsilon> + \<beta>"
      by (rule step_logit_drift[OF rbound rho0 ubound[rule_format, OF vV]
                                   bbound[rule_format, OF vV]])
  qed
  show ?thesis by (rule margin_transfer[OF margin pert tV])
qed

text \<open>PER-STEP RUNTIME ENGINE.  One joint (U, b) learning step preserves the decision whenever the
  current margin exceeds twice the step's drift budget \<rho>*\<epsilon> + \<beta>.  With \<beta> = 0 this is
  PIC_Quant.quant_decode_preserved; the \<beta> term is what a TRAINED bias adds.  This is the
  inequality a picard P3 loop checks at every iteration.\<close>
theorem step_decode_preserved:
  fixes U U' :: "'v \<Rightarrow> 'a::real_inner" and b b' :: "'v \<Rightarrow> real" and r :: 'a
  assumes tV:     "t \<in> V"
      and rbound: "norm r \<le> \<rho>" and rho0: "0 \<le> \<rho>"
      and ubound: "\<forall>v\<in>V. norm (U' v - U v) \<le> \<epsilon>"
      and bbound: "\<forall>v\<in>V. \<bar>b' v - b v\<bar> \<le> \<beta>"
      and margin: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> (inner r (U v) + b v) + m \<le> (inner r (U t) + b t)"
      and tol:    "2 * (\<rho> * \<epsilon> + \<beta>) < m"
  shows "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> (inner r (U' v) + b' v) < (inner r (U' t) + b' t)"
proof (intro ballI impI)
  fix v assume vV: "v \<in> V" and vt: "v \<noteq> t"
  from step_margin_survives[OF tV rbound rho0 ubound bbound margin] vV vt tol
  show "(inner r (U' v) + b' v) < (inner r (U' t) + b' t)" by fastforce
qed

text \<open>TELESCOPING MARGIN SURVIVAL.  Along a trajectory (U^s, b^s), s = 0..T, with per-step drift
  bounds \<epsilon> s and \<beta> s on the visited vocabulary V, an initial uniform margin m degrades after
  \<tau> steps to at least m - 2 * (\<Sum>s<\<tau>. \<rho>*\<epsilon> s + \<beta> s).  Pure induction via margin_transfer;
  no positivity anywhere, so the bound holds even past the point where it goes vacuous.\<close>
theorem traj_decode_margin:
  fixes U :: "nat \<Rightarrow> 'v \<Rightarrow> 'a::real_inner" and b :: "nat \<Rightarrow> 'v \<Rightarrow> real" and r :: 'a
    and \<epsilon> \<beta> :: "nat \<Rightarrow> real"
  assumes tV:      "t \<in> V"
      and rbound:  "norm r \<le> \<rho>" and rho0: "0 \<le> \<rho>"
      and ubound:  "\<And>s v. s < T \<Longrightarrow> v \<in> V \<Longrightarrow> norm (U (Suc s) v - U s v) \<le> \<epsilon> s"
      and bbound:  "\<And>s v. s < T \<Longrightarrow> v \<in> V \<Longrightarrow> \<bar>b (Suc s) v - b s v\<bar> \<le> \<beta> s"
      and margin0: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> (inner r (U 0 v) + b 0 v) + m \<le> (inner r (U 0 t) + b 0 t)"
      and tauT:    "\<tau> \<le> T"
  shows "\<forall>v\<in>V. v \<noteq> t \<longrightarrow>
           (inner r (U \<tau> v) + b \<tau> v) + (m - 2 * (\<Sum>s<\<tau>. \<rho> * \<epsilon> s + \<beta> s))
             \<le> (inner r (U \<tau> t) + b \<tau> t)"
  using tauT
proof (induction \<tau>)
  case 0
  then show ?case using margin0 by simp
next
  case (Suc \<tau>)
  then have sT: "\<tau> < T" and tle: "\<tau> \<le> T" by simp_all
  have IH: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow>
              (inner r (U \<tau> v) + b \<tau> v) + (m - 2 * (\<Sum>s<\<tau>. \<rho> * \<epsilon> s + \<beta> s))
                \<le> (inner r (U \<tau> t) + b \<tau> t)"
    using Suc.IH tle by blast
  have pert: "\<forall>v\<in>V. \<bar>(inner r (U (Suc \<tau>) v) + b (Suc \<tau>) v)
                       - (inner r (U \<tau> v) + b \<tau> v)\<bar> \<le> \<rho> * \<epsilon> \<tau> + \<beta> \<tau>"
  proof (intro ballI)
    fix v assume vV: "v \<in> V"
    show "\<bar>(inner r (U (Suc \<tau>) v) + b (Suc \<tau>) v) - (inner r (U \<tau> v) + b \<tau> v)\<bar>
            \<le> \<rho> * \<epsilon> \<tau> + \<beta> \<tau>"
      by (rule step_logit_drift[OF rbound rho0 ubound[OF sT vV] bbound[OF sT vV]])
  qed
  have step: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow>
                (inner r (U (Suc \<tau>) v) + b (Suc \<tau>) v)
                  + ((m - 2 * (\<Sum>s<\<tau>. \<rho> * \<epsilon> s + \<beta> s)) - 2 * (\<rho> * \<epsilon> \<tau> + \<beta> \<tau>))
                \<le> (inner r (U (Suc \<tau>) t) + b (Suc \<tau>) t)"
    by (rule margin_transfer[OF IH pert tV])
  have msum: "m - 2 * (\<Sum>s<Suc \<tau>. \<rho> * \<epsilon> s + \<beta> s)
                = (m - 2 * (\<Sum>s<\<tau>. \<rho> * \<epsilon> s + \<beta> s)) - 2 * (\<rho> * \<epsilon> \<tau> + \<beta> \<tau>)"
    by (simp add: algebra_simps)
  show ?case unfolding msum by (rule step)
qed

text \<open>THE A-PRIORI TRAJECTORY CERTIFICATE (T-traj).  If the TOTAL drift budget of the whole
  trajectory is below half the initial margin, then at EVERY point of the trajectory every
  visited decision is preserved (strict argmax) -- the frame-learning loop's invariant S1 as a
  theorem.  The drift bounds are stated as nonneg budgets (they bound norms, so this is free in
  any instantiation); nonnegativity is what lets the partial sum be dominated by the total.\<close>
theorem traj_decode_preserved:
  fixes U :: "nat \<Rightarrow> 'v \<Rightarrow> 'a::real_inner" and b :: "nat \<Rightarrow> 'v \<Rightarrow> real" and r :: 'a
    and \<epsilon> \<beta> :: "nat \<Rightarrow> real"
  assumes tV:      "t \<in> V"
      and rbound:  "norm r \<le> \<rho>" and rho0: "0 \<le> \<rho>"
      and eps0:    "\<And>s. s < T \<Longrightarrow> 0 \<le> \<epsilon> s"
      and beta0:   "\<And>s. s < T \<Longrightarrow> 0 \<le> \<beta> s"
      and ubound:  "\<And>s v. s < T \<Longrightarrow> v \<in> V \<Longrightarrow> norm (U (Suc s) v - U s v) \<le> \<epsilon> s"
      and bbound:  "\<And>s v. s < T \<Longrightarrow> v \<in> V \<Longrightarrow> \<bar>b (Suc s) v - b s v\<bar> \<le> \<beta> s"
      and margin0: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> (inner r (U 0 v) + b 0 v) + m \<le> (inner r (U 0 t) + b 0 t)"
      and budget:  "2 * (\<Sum>s<T. \<rho> * \<epsilon> s + \<beta> s) < m"
      and tauT:    "\<tau> \<le> T"
  shows "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> (inner r (U \<tau> v) + b \<tau> v) < (inner r (U \<tau> t) + b \<tau> t)"
proof (intro ballI impI)
  fix v assume vV: "v \<in> V" and vt: "v \<noteq> t"
  have surv: "(inner r (U \<tau> v) + b \<tau> v) + (m - 2 * (\<Sum>s<\<tau>. \<rho> * \<epsilon> s + \<beta> s))
                \<le> (inner r (U \<tau> t) + b \<tau> t)"
    using traj_decode_margin[OF tV rbound rho0 ubound bbound margin0 tauT] vV vt by blast
  have "(\<Sum>s<\<tau>. \<rho> * \<epsilon> s + \<beta> s) \<le> (\<Sum>s<T. \<rho> * \<epsilon> s + \<beta> s)"
  proof (rule sum_mono2)
    show "finite {..<T}" by simp
    show "{..<\<tau>} \<subseteq> {..<T}" using tauT by auto
    show "\<And>s. s \<in> {..<T} - {..<\<tau>} \<Longrightarrow> 0 \<le> \<rho> * \<epsilon> s + \<beta> s"
      using eps0 beta0 rho0 by (auto intro!: add_nonneg_nonneg mult_nonneg_nonneg)
  qed
  with budget surv show "(inner r (U \<tau> v) + b \<tau> v) < (inner r (U \<tau> t) + b \<tau> t)" by linarith
qed

end
