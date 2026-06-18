(*
  Examples.thy -- a concrete distortion figure.

  A concrete operating point for the MSE bound. At a bit-width of 4, the closed-form upper
  bound is (sqrt 3 * pi / 2) / 256, which the near-optimality constant pins below 0.011 --
  matching the paper's reported small-bit-width distortion (~0.009 at b = 4). A concrete,
  kernel-checked numeric distortion guarantee.
*)

theory Examples
  imports DistortionRate
begin

theorem example_four_bit_distortion: "mse_ub 4 < 0.011"
proof -
  have "mse_ub 4 = (sqrt 3 * pi / 2) / 256" by (simp add: mse_ub_def)
  also have "\<dots> < 2.73 / 256"
    using mse_const_approx by (intro divide_strict_right_mono) auto
  also have "\<dots> < 0.011" by simp
  finally show ?thesis .
qed

end
