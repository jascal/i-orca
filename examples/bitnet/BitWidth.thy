(*
  BitWidth.thy -- the "1.58 bits".

  BitNet b1.58 is named for the information content of a ternary symbol: a value in
  {-1, 0, 1} carries log2(3) bits. We bracket this constant, 1.5 < log2 3 < 1.6 (the true
  value is ~1.585), and record the packing fact behind the upper bound: five trits fit in a
  byte, since 3^5 = 243 <= 256 = 2^8. (Indeed log2 3 < 1.6 IS the statement 3^5 < 2^8.)
*)

theory BitWidth
  imports Complex_Main
begin

text \<open>A ternary symbol carries log2(3) bits, between 1.5 and 1.6 (true value ~1.585).\<close>

theorem log2_3_approx: "1.5 < log 2 3 \<and> log 2 3 < 1.6"
proof
  have key1: "(2::real) powr 1.5 < 3"
  proof -
    have "((2::real) powr 1.5) ^ 2 = 2 powr (1.5 * 2)"
      by (simp add: powr_realpow[symmetric] powr_powr)
    also have "\<dots> = 2 ^ 3" by (simp add: powr_realpow)
    finally have "((2::real) powr 1.5) ^ 2 < 3 ^ 2" by simp
    thus ?thesis by (rule power_less_imp_less_base) simp
  qed
  have "(1.5 < log 2 3) = ((2::real) powr 1.5 < 3)" by (rule less_log_iff) simp_all
  thus "1.5 < log 2 3" using key1 by simp
next
  have key2: "(3::real) < 2 powr 1.6"
  proof -
    have "((2::real) powr 1.6) ^ 5 = 2 powr (1.6 * 5)"
      by (simp add: powr_realpow[symmetric] powr_powr)
    also have "\<dots> = 2 ^ 8" by (simp add: powr_realpow)
    finally have "(3::real) ^ 5 < ((2::real) powr 1.6) ^ 5" by simp
    thus ?thesis by (rule power_less_imp_less_base) simp
  qed
  have "(log 2 3 < 1.6) = ((3::real) < 2 powr 1.6)" by (rule log_less_iff) simp_all
  thus "log 2 3 < 1.6" using key2 by simp
qed

text \<open>Five trits pack into one byte: 3^5 = 243 fits in 2^8 = 256.\<close>

theorem five_trits_per_byte: "(3::nat) ^ 5 \<le> 2 ^ 8"
  by simp

end
