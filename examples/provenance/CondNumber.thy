(*
  CondNumber.thy -- the Hessian-conditioning limit on influence-function
  attribution (Problem 2, hard limit #1).

  Training-data attribution estimates the influence of a training point z on a
  response R by the influence function

        I(z,R)  ~  - grad_R L(theta_star)^T  H^-1  grad_z L(theta_star),
        H = Hessian of L at theta_star.

  Computing it solves a linear system in the Hessian H. In the eigenbasis H is
  diagonal with eigenvalues in [lo, hi]; the relative error of the solve is
  amplified by the condition number kappa = hi/lo. In transformers kappa routinely
  exceeds 1e6-1e10, so the error bars -- and even the SIGN -- of an influence score
  are unreliable.

  We pin the worst case exactly. Put the SIGNAL along the largest-eigenvalue
  direction and a small NOISE perturbation along the smallest. Then the relative
  output error divided by the relative input error equals kappa EXACTLY
  (condition_number_tight): the amplification bound is achieved, not pessimistic.

  Corollaries: kappa >= 1 always (kappa_ge_one); a perfectly conditioned problem
  (lo = hi, an isolated coherent bucket) has kappa = 1 and NO amplification
  (kappa_one). This is the formal content of "tighter inside well-isolated buckets".
*)

theory CondNumber
  imports Complex_Main
begin

definition kappa :: "real \<Rightarrow> real \<Rightarrow> real" where
  "kappa lo hi = hi / lo"

lemma kappa_one:
  assumes "0 < lo"
  shows "kappa lo lo = 1"
  using assms by (simp add: kappa_def)

lemma kappa_ge_one:
  assumes "0 < lo" "lo \<le> hi"
  shows "1 \<le> kappa lo hi"
  using assms by (simp add: kappa_def)

text \<open>Worst-case amplification is achieved exactly. Signal: input hi along the
  hi-eigenvalue direction gives solved component hi/hi = 1. Noise: input eps*hi
  along the lo-eigenvalue direction gives solved component (eps*hi)/lo. The
  relative output error ((eps*hi)/lo)/1 over the relative input error (eps*hi)/hi
  equals kappa lo hi.\<close>

theorem condition_number_tight:
  assumes "0 < lo" "0 < hi" "0 < eps"
  shows "(((eps * hi) / lo) / 1) / ((eps * hi) / hi) = kappa lo hi"
  using assms by (simp add: kappa_def field_simps)

end
