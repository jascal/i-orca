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

end
