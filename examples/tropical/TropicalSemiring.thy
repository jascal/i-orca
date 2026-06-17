(*
  TropicalSemiring.thy -- the max-plus (tropical) semiring.

  Foundation for the tropical-geometry-of-DNNs corpus (Zhang, Naitzat & Lim, ICML
  2018; surrounding literature Pachter-Sturmfels 2004 and Maragos-Charisopoulos-
  Theodosis 2021). The tropical semiring is (R cup {-inf}, oplus, odot) with

        a oplus b = max a b,        a odot b = a + b.

  We work over R (the additive identity -inf is adjoined separately; over R the
  additive monoid (max) has no identity, which is exactly why -inf is needed). We
  prove the semiring axioms that hold on R: oplus is associative, commutative and
  idempotent; odot is associative, commutative, with identity 0; and odot
  distributes over oplus -- the single law (max a b) + c = max (a+c) (b+c) that makes
  ReLU networks tropical (TropicalPoly / ReLUNet).
*)

theory TropicalSemiring
  imports Complex_Main
begin

definition tadd :: "real \<Rightarrow> real \<Rightarrow> real" where "tadd a b = max a b"
definition tmul :: "real \<Rightarrow> real \<Rightarrow> real" where "tmul a b = a + b"

lemma tadd_assoc:    "tadd (tadd a b) c = tadd a (tadd b c)" by (simp add: tadd_def)
lemma tadd_commute:  "tadd a b = tadd b a"                   by (simp add: tadd_def max.commute)
lemma tadd_idem:     "tadd a a = a"                          by (simp add: tadd_def)

lemma tmul_assoc:    "tmul (tmul a b) c = tmul a (tmul b c)" by (simp add: tmul_def)
lemma tmul_commute:  "tmul a b = tmul b a"                   by (simp add: tmul_def)
lemma tmul_left_id:  "tmul 0 a = a"                          by (simp add: tmul_def)
lemma tmul_right_id: "tmul a 0 = a"                          by (simp add: tmul_def)

text \<open>The load-bearing law: tropical multiplication distributes over tropical
  addition. This is what turns a sum-of-maxes (a ReLU network) into a max-of-sums
  (a tropical polynomial).\<close>

lemma tmul_tadd_distrib_left:
  "tmul a (tadd b c) = tadd (tmul a b) (tmul a c)"
  by (simp add: tmul_def tadd_def max_def)

lemma tmul_tadd_distrib_right:
  "tmul (tadd a b) c = tadd (tmul a c) (tmul b c)"
  by (simp add: tmul_def tadd_def max_def)

end
