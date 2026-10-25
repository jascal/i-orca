theory PDC_Derive
  imports "PIC_Core.PIC_Logic"
begin

text \<open>Finite body identifiers retain multiplicity even when brackets coincide.
  None denotes the additive zero (negative infinity), never a real score of zero.
  The single-position vocabulary fragment is interpreted in the PIC locale below;
  no read operation or external theory is present in that fragment.\<close>

definition pdc_mar :: "real \<Rightarrow> ('b \<Rightarrow> real) \<Rightarrow> 'b set \<Rightarrow> real option" where
  "pdc_mar T score B = (if B = {} then None
    else Some (T * ln (\<Sum>p\<in>B. exp (score p / T))))"

definition pdc_vit :: "('b \<Rightarrow> real) \<Rightarrow> 'b set \<Rightarrow> real option" where
  "pdc_vit score B = (if B = {} then None else Some (Max (score ` B)))"

lemma mar_singleton:
  assumes "0 < T"
  shows "pdc_mar T score {p} = Some (score p)"
  using assms by (simp add: pdc_mar_def)

lemma vit_singleton: "pdc_vit score {p} = Some (score p)"
  by (simp add: pdc_vit_def)

fun pdc_le :: "real option \<Rightarrow> real option \<Rightarrow> bool" where
  "pdc_le None y = True"
| "pdc_le (Some x) None = False"
| "pdc_le (Some x) (Some y) = (x \<le> y)"

definition pdc_argmax :: "'a set \<Rightarrow> ('a \<Rightarrow> real option) \<Rightarrow> 'a set" where
  "pdc_argmax A f = {a \<in> A. f a \<noteq> None \<and> (\<forall>b\<in>A. pdc_le (f b) (f a))}"

definition pdc_fragile where
  "pdc_fragile T A bodies score \<longleftrightarrow>
    pdc_argmax A (\<lambda>a. pdc_vit (score a) (bodies a)) \<noteq>
    pdc_argmax A (\<lambda>a. pdc_mar T (score a) (bodies a))"

theorem one_body_agreement:
  assumes "0 < T" "B = {} \<or> (\<exists>p. B = {p})"
  shows "pdc_mar T score B = pdc_vit score B"
  using assms mar_singleton vit_singleton
  by (auto simp: pdc_mar_def pdc_vit_def)

theorem one_body_temperature_invariance:
  assumes "0 < T" "0 < T'"
    "\<And>a. a \<in> A \<Longrightarrow> bodies a = {} \<or> (\<exists>p. bodies a = {p})"
  shows "pdc_argmax A (\<lambda>a. pdc_mar T (score a) (bodies a)) =
    pdc_argmax A (\<lambda>a. pdc_mar T' (score a) (bodies a))"
proof -
  have eq: "\<And>a. a \<in> A \<Longrightarrow>
    pdc_mar T (score a) (bodies a) = pdc_mar T' (score a) (bodies a)"
  proof -
    fix a assume a: "a \<in> A"
    have "pdc_mar T (score a) (bodies a) = pdc_vit (score a) (bodies a)"
      by (rule one_body_agreement[OF assms(1) assms(3)[OF a]])
    also have "\<dots> = pdc_mar T' (score a) (bodies a)"
      by (rule sym, rule one_body_agreement[OF assms(2) assms(3)[OF a]])
    finally show "pdc_mar T (score a) (bodies a) = pdc_mar T' (score a) (bodies a)" .
  qed
  show ?thesis unfolding pdc_argmax_def using eq by auto
qed

lemma ln_two_gt_half: "(1/2::real) < ln 2"
proof -
  have "ln (1::real) - ln 2 < (1 - 2) / 2"
    by (rule ln_diff_less) simp_all
  then show ?thesis by simp
qed

definition witness_bodies :: "bool \<Rightarrow> bool set" where
  "witness_bodies a = (if a then {True, False} else {True})"

definition witness_score :: "bool \<Rightarrow> bool \<Rightarrow> real" where
  "witness_score a p = (if a then 0 else 1/2)"

lemma witness_viterbi:
  "pdc_argmax UNIV (\<lambda>a. pdc_vit (witness_score a) (witness_bodies a)) = {False}"
proof -
  have scores: "\<And>a. pdc_vit (witness_score a) (witness_bodies a) =
    Some (if a then 0 else 1/2)"
    by (simp add: pdc_vit_def witness_score_def witness_bodies_def)
  show ?thesis by (auto simp: pdc_argmax_def scores split: if_splits)
qed

lemma witness_marginal:
  "pdc_argmax UNIV (\<lambda>a. pdc_mar 1 (witness_score a) (witness_bodies a)) = {True}"
proof -
  have scores: "\<And>a. pdc_mar 1 (witness_score a) (witness_bodies a) =
    Some (if a then ln 2 else 1/2)"
    by (simp add: pdc_mar_def witness_score_def witness_bodies_def)
  show ?thesis using ln_two_gt_half
    by (auto simp: pdc_argmax_def scores split: if_splits)
qed

theorem witness_fragile: "pdc_fragile 1 UNIV witness_bodies witness_score"
  unfolding pdc_fragile_def using witness_viterbi witness_marginal by simp

context pic
begin

text \<open>Bias is included once in each complete body, matching PIC's Lt.
  A unit body identifier denotes the full source coalition.\<close>

theorem specialization_alpha_eq_logit:
  assumes "0 < T"
  shows "pdc_mar T (\<lambda>(_::unit). Lc S v + b v) {()} = Some (Lt v)"
  using mar_singleton[OF assms] by (simp add: Lt_def)

theorem specialization_alpha_eq_residual:
  assumes "0 < T"
  shows "pdc_mar T (\<lambda>(_::unit). Lc S v + b v) {()} =
    Some (inner (\<Sum>j\<in>S. d j) (U v) + b v)"
  using specialization_alpha_eq_logit[OF assms] logit_is_residual_reading by simp

end

text \<open>Softmax normalization is common to all candidates, so it cancels
  from comparisons. This states PIC section 3.1 for its actual biased logit.\<close>
context pic
begin

theorem specialization_softmax_order:
  assumes "0 < T"
  shows "exp ((Lt v - Z) / T) \<le> exp ((Lt w - Z) / T) \<longleftrightarrow> Lt v \<le> Lt w"
  using assms by (simp add: divide_le_cancel)

theorem specialization_softmax_argmax:
  assumes "0 < T"
  shows "pdc_argmax V (\<lambda>v. Some (exp ((Lt v - Z) / T))) =
    pdc_argmax V (\<lambda>v. Some (Lt v))"
  using specialization_softmax_order[OF assms]
  by (simp add: pdc_argmax_def)

end

end
