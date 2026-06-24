(*
  KreinPrecond.thy -- SCHEME A: Krein in the TUNABLE FRAME only (the optimizer's metric), not in the
  encoder or decoder.

  The scheme.  Keep the forward pass and the loss Euclidean (plain <r, U_v>, standard softmax, standard
  cross-entropy -- so neither the loss nor the training DATA changes).  Put the indefinite fundamental
  symmetry J only in the FRAME UPDATE, as a preconditioner on the frame gradient:

        U  <-  U  -  eta * J (grad_U L).

  Along the spacelike subspace (J = +1) this is ordinary descent; along the timelike subspace (J = -1)
  the update sign FLIPS (ascent) -- "backprop allowed to send values negative" -- so the frame can grow
  suppressive / anti-correlated structure that pure descent is biased away from.  This is the purest
  form of the pil thesis: Krein lives only on the MOVABLE side (the frame), and KreinDecode's
  definitization guarantees the Euclidean decode never sees it.

  The question this file settles: is Scheme A just disguised vanilla SGD?  NO.  A linear reparametrization
  V = M U turns vanilla gradient descent in V into descent in U preconditioned by (M^T M)^{-1} -- and
  M^T M is ALWAYS positive semidefinite.  An indefinite J (a fundamental symmetry with a timelike vector,
  <t, J t> < 0) is symmetric but not PSD, so it equals no Gram M^T M.  Hence indefinite-preconditioned
  frame flow is NOT the U-image of vanilla SGD under any real reparametrization.

  This is the OPTIMIZER-SIDE companion of the FORWARD-SIDE absorb-J triviality
  (KreinDecode.kinner_majorant): J in the forward INCIDENCE is absorbable (a relabeled Euclidean frame);
  J in the update METRIC is not.  So Scheme A escapes the collapse that made a fixed forward J trivial.

  RESULTS:
    gram_form_nonneg         : every Gram quadratic form x |-> <M x, M x> is >= 0 (the realizable,
                               PSD preconditioners -- exactly those a reparametrization can induce).
    indefinite_not_gram_form : if J has a timelike vector (<t, J t> < 0), no M satisfies
                               <x, J x> = <M x, M x> for all x -- J's quadratic form is NOT a Gram form.
    precond_not_reparam      : packaging -- an indefinite preconditioner is induced by no real linear
                               reparametrization of the parameters (Scheme A is genuinely new dynamics).

  Tag (pic discipline): all [proved] here.  That an indefinite preconditioner HELPS -- reaches better
  frames than plain SGD -- is [open/empirical]; pil sec 6.1 found no theory-guided frame knob yet beats
  plain SGD on the synthetic benchmarks, so the benefit is a hypothesis, the non-triviality is a theorem.
*)
theory KreinPrecond
  imports "HOL-Analysis.Analysis"
begin

text \<open>Every Gram quadratic form @{term "\<lambda>x. inner (M x) (M x)"} is nonnegative: these are exactly the
  preconditioners a linear reparametrization can realize (the PSD ones, M^T M).\<close>
lemma gram_form_nonneg: "inner (M x) (M x) \<ge> 0"
  by (rule inner_ge_zero)

text \<open>An indefinite fundamental symmetry @{term J} -- one with a TIMELIKE vector @{term t},
  @{term "inner t (J t) < 0"} -- has a quadratic form that is NOT a Gram form: no map @{term M} can
  satisfy @{term "inner x (J x) = inner (M x) (M x)"} for all @{term x}.  The timelike vector witnesses
  a strictly negative value that no nonnegative Gram form can match.\<close>
theorem indefinite_not_gram_form:
  fixes J :: "'a::real_inner \<Rightarrow> 'a"
  assumes tl: "inner t (J t) < 0"
  shows "\<not> (\<exists>M. \<forall>x. inner x (J x) = inner (M x) (M x))"
proof
  assume "\<exists>M. \<forall>x. inner x (J x) = inner (M x) (M x)"
  then show False
  proof (elim exE)
    fix M assume M: "\<forall>x. inner x (J x) = inner (M x) (M x)"
    have "inner t (J t) = inner (M t) (M t)" by (rule M[rule_format])
    moreover have "inner (M t) (M t) \<ge> 0" by (rule inner_ge_zero)
    ultimately show False using tl by simp
  qed
qed

text \<open>Packaging.  Reading @{term "inner x (J x) = inner (M x) (M x)"} as "J is the Gram M^T M
  at the level of quadratic forms" (polarization makes this equivalent to J = M^T M for
  self-adjoint J), an indefinite J is realized by no such M.  Hence the indefinite-preconditioned frame
  update is not the parameter-image of vanilla gradient descent under any linear reparametrization
  @{term "V = M U"} -- Scheme A is genuinely new optimization geometry, not a relabeling of SGD.\<close>
corollary precond_not_reparam:
  fixes J :: "'a::real_inner \<Rightarrow> 'a"
  assumes "inner t (J t) < 0"
  shows "\<nexists>M. \<forall>x. inner x (J x) = inner (M x) (M x)"
proof
  assume "\<exists>M. \<forall>x. inner x (J x) = inner (M x) (M x)"
  then show False
  proof (elim exE)
    fix M assume M: "\<forall>x. inner x (J x) = inner (M x) (M x)"
    have "inner t (J t) = inner (M t) (M t)" by (rule M[rule_format])
    moreover have "inner (M t) (M t) \<ge> 0" by (rule inner_ge_zero)
    ultimately show False using assms by simp
  qed
qed

text \<open>DYNAMICAL READING -- the J-flow is NOT a descent flow.  Treat the Euclidean loss gradient as a
  free vector g = grad_U L.  The J-preconditioned update direction is -(J g), and the first-order change
  in L along it is  inner g (-(J g)) = - inner g (J g)  -- this is dL/dt for the flow U' = -J grad L.
  A DESCENT step needs inner g (-(J g)) <= 0, i.e. inner g (J g) >= 0.  So a PSD J always descends, but
  an INDEFINITE J has a gradient (any timelike vector) at which the update is a strict ASCENT: the flow
  can increase the loss.  Dynamical companion to precond_not_reparam.\<close>

lemma psd_precond_descends:
  fixes J :: "'a::real_inner \<Rightarrow> 'a"
  assumes psd: "\<And>x. 0 \<le> inner x (J x)"
  shows "inner g (- (J g)) \<le> 0"
  using psd[of g] by (simp add: inner_minus_right)

theorem indefinite_precond_not_descent:
  fixes J :: "'a::real_inner \<Rightarrow> 'a"
  assumes tl: "inner t (J t) < 0"
  shows "\<exists>g. 0 < inner g (- (J g))"
proof (rule exI[of _ t])
  show "0 < inner t (- (J t))" using tl by (simp add: inner_minus_right)
qed

text \<open>THE LEARNED-J DICHOTOMY.  Suppose we make J adaptive (learned, or computed from curvature) and
  ask it to keep DESCENDING for every gradient.  Then it must be PSD: "descends for all g" is exactly
  "J is positive-semidefinite".  Equivalently (contrapositive, via precond_not_reparam): a genuinely
  indefinite learned J is neither always-descent NOR a reparametrization.  So an adaptive J cannot be
  both genuinely Krein AND a reliable minimizer -- adaptivity that preserves descent collapses it to the
  PSD / reparametrization class (ordinary second-order preconditioning, e.g. the |H| of saddle-free
  Newton); keeping it indefinite keeps it saddle-seeking.  The indefiniteness is only a resource when
  minimization is NOT the goal (min-max spread, basin escape).  See LEARNED_J.md.\<close>
lemma descends_all_iff_psd:
  fixes J :: "'a::real_inner \<Rightarrow> 'a"
  shows "(\<forall>g. inner g (- (J g)) \<le> 0) \<longleftrightarrow> (\<forall>x. 0 \<le> inner x (J x))"
  by (auto simp: inner_minus_right)

text \<open>INSTABILITY OF MINIMA -- the isotropic core, kernel-checked.  Near a strict minimum the gradient is
  grad L ~ H u (Hessian H positive-definite).  Whitening v = H^{1/2} u turns H into the identity, so it
  suffices to analyse the ISOTROPIC minimum H = I, where the Scheme-A update with step eta and gradient u
  is  kstep J eta u = u - eta *R J u.  On a timelike axis (J t = - t, i.e. t in the negative eigenspace
  H_-) the update MULTIPLIES t by (1 + eta): the iterate diverges geometrically away from the minimum,
  and in continuous time -J has eigenvalue +1 there.  So the whole timelike subspace is unstable.\<close>

definition kstep :: "('a::real_inner \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> 'a" where
  "kstep J \<eta> u = u - \<eta> *\<^sub>R J u"

text \<open>The Scheme-A update at an isotropic minimum multiplies a timelike axis by (1 + eta): the iterate
  is repelled from the minimum, growing by the factor (1 + eta) > 1 each step.\<close>
lemma kstep_grows_on_timelike:
  assumes Jt: "J t = - t"
  shows "kstep J \<eta> t = (1 + \<eta>) *\<^sub>R t"
  unfolding kstep_def using Jt by (simp add: scaleR_add_left)

corollary kstep_norm_grows:
  assumes Jt: "J t = - t" and nn: "0 \<le> \<eta>"
  shows "norm (kstep J \<eta> t) = (1 + \<eta>) * norm t"
proof -
  have nn1: "0 \<le> 1 + \<eta>" using nn by simp
  have eq: "kstep J \<eta> t = (1 + \<eta>) *\<^sub>R t"
    unfolding kstep_def using Jt by (simp add: scaleR_add_left)
  have "norm (kstep J \<eta> t) = \<bar>1 + \<eta>\<bar> * norm t" by (simp add: eq norm_scaleR)
  also have "\<dots> = (1 + \<eta>) * norm t" using nn1 by simp
  finally show ?thesis .
qed

text \<open>Continuous-time form: the flow Jacobian -J has eigenvalue +1 on every timelike axis, so the whole
  timelike eigenspace H_- (dimension q) is the unstable manifold of the isotropic minimum.\<close>
lemma flow_unstable_on_timelike:
  fixes J :: "'a::real_inner \<Rightarrow> 'a"
  assumes "J x = - x"
  shows "- (J x) = x"
  using assms by simp

text \<open>CONSEQUENCE -- the general (non-isotropic) Hessian (stated; the spectral count needs the spectral
  theorem + Sylvester, beyond this HOL-Analysis session): linearizing U' = -J grad L at a strict min
  gives Jacobian -J H, similar (via H^{1/2}) to the SYMMETRIC -H^{1/2} J H^{1/2}, which by Sylvester's
  law of inertia (congruence by H^{1/2}) has the inertia of -J -- so q POSITIVE eigenvalues.  The minimum
  is thus an unstable fixed point with a q-dim unstable manifold; the isotropic lemmas above are the
  H = I instance, kernel-checked.  Hence Scheme A is sound only (a) as a min-max -- route the
  maximize-objective (push features apart) into the timelike subspace, the data-fit into the spacelike
  one -- or (b) transiently, annealing J -> I so the final phase is genuine descent.  See SCHEME_A.md.\<close>

text \<open>OPEN: does an indefinite frame preconditioner actually HELP (reach better frames than plain SGD)?
  Untested -- no numbers exist for this knob; pil sec 6.1 found no theory-guided frame knob has yet beaten
  plain SGD on the synthetic benchmarks, so the prior is cautious.  The non-triviality above is a theorem;
  the benefit is a hypothesis.\<close>

text \<open>OPEN: extending the indefinite preconditioner to the encoder WRITE directions a_k (not just the
  frame U) moves off the movable-frame side into the encode/generator regime, where the O(p,q)
  non-compactness bites harder (unconstrained writes) and a damping constraint is needed.  Scheme A as
  scoped here leaves the encoder and the forward pass Euclidean.\<close>

end
