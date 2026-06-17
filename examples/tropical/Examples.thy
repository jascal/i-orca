(*
  Examples.thy -- a concrete ReLU network rendered as a tropical rational expression.

  A worked, kernel-checked instance of the Zhang-Naitzat-Lim picture (ReLUNet.thy):
  the two-neuron ReLU network

        x  |->  relu x + relu (-x)

  computes the absolute value, which is exactly the tropical polynomial
  max x (-x) = x oplus (-x) -- a max of the two tropical monomials x and -x. So this
  network is literally a tropical polynomial (abs_troppoly), hence a tropical rational
  function (abs_network_troprat). A small, fully concrete witness for Theorem 5.4.
*)

theory Examples
  imports ReLUNet
begin

text \<open>The two-neuron network computes the absolute value.\<close>

lemma relu_plus_relu_neg: "relu x + relu (- x) = \<bar>x\<bar>"
  by (simp add: relu_def max_def)

text \<open>Absolute value is the tropical sum of the monomials x and -x.\<close>

lemma abs_eq_tropmax: "\<bar>x::real\<bar> = max x (- x)"
proof (cases "x \<le> - x")
  case True
  hence "x \<le> 0" by linarith
  thus ?thesis using True by (simp add: max_def abs_of_nonpos)
next
  case False
  hence "0 \<le> x" by linarith
  thus ?thesis using False by (simp add: max_def abs_of_nonneg)
qed

text \<open>Absolute value is a tropical polynomial: a max of two affine monomials.\<close>

lemma abs_troppoly: "troppoly (\<lambda>x::real. \<bar>x\<bar>)"
proof -
  have "troppoly (\<lambda>x::real. max (inner 1 x + 0) (inner (- 1) x + 0))"
    by (intro troppoly.maxp troppoly.affine)
  moreover have "(\<lambda>x::real. max (inner 1 x + 0) (inner (- 1) x + 0)) = (\<lambda>x. \<bar>x\<bar>)"
    by (simp add: fun_eq_iff max_def)
  ultimately show ?thesis by simp
qed

text \<open>Hence the network is a tropical rational function.\<close>

theorem abs_network_troprat: "troprat (\<lambda>x::real. relu x + relu (- x))"
proof -
  have "(\<lambda>x::real. relu x + relu (- x)) = (\<lambda>x. \<bar>x\<bar>)"
    by (simp add: fun_eq_iff relu_plus_relu_neg)
  thus ?thesis using abs_troppoly troppoly_imp_troprat by simp
qed

end
