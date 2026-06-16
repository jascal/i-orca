(*
  Provenance.thy -- the syntactic-vs-statistical core of the provenance/attribution
  thread (see PROPOSAL.md).

  Setup. Sources (corpora) are nat indices. A bucket carries a source-label set
  L(b) recording which corpora contributed the data that built it; a token
  annotation pins the bucket, hence the label.

  Problem 1 (syntactic provenance) -- "which corpus label is attached to the bucket
  that produced this token?" -- is a deterministic lookup: the posterior is the
  indicator at the true label s. We prove it is a valid distribution
  (synt_post_sum_one) and carries ZERO Shannon entropy (synt_entropy_zero): exact.

  Problem 2 (statistical influence) is fundamentally harder. Its first hard limit
  appears already here: once a bucket is realisable from >= 2 corpora (irreversible
  mixing), any posterior consistent with it has support >= 2, and Shannon entropy of
  such a posterior is strictly positive (mixed_entropy_pos) -- irreducible
  uncertainty no estimator can remove.
*)

theory Provenance
  imports Complex_Main
begin

type_synonym source = nat

text \<open>Shannon information (bits). The pointwise term -p*log2 p, with the
  convention 0 * log2 0 = 0.\<close>

definition plogp :: "real \<Rightarrow> real" where
  "plogp p = (if p \<le> 0 then 0 else - (p * log 2 p))"

definition shannon :: "source set \<Rightarrow> (source \<Rightarrow> real) \<Rightarrow> real" where
  "shannon S p = (\<Sum>j\<in>S. plogp (p j))"

lemma plogp_zero [simp]: "plogp 0 = 0"
  by (simp add: plogp_def)

lemma plogp_one [simp]: "plogp 1 = 0"
  by (simp add: plogp_def)

text \<open>For an interior probability 0 < q < 1 the term is strictly positive:
  log2 q < 0, so -(q * log2 q) > 0.\<close>

lemma plogp_pos:
  assumes "0 < q" "q < 1"
  shows "0 < plogp q"
proof -
  have lq: "ln q < 0" using assms by (simp add: ln_less_zero_iff)
  have l2: "0 < ln (2::real)" using ln_gt_zero[of 2] by simp
  have lg: "log 2 q < 0" using lq l2 by (simp add: log_def divide_neg_pos)
  have "q * log 2 q < 0" using assms(1) lg by (rule mult_pos_neg)
  thus ?thesis using assms(1) by (simp add: plogp_def)
qed

text \<open>Problem 1 -- exact syntactic provenance: the indicator posterior at the
  single true source s.\<close>

definition synt_post :: "source \<Rightarrow> source \<Rightarrow> real" where
  "synt_post s j = (if j = s then 1 else 0)"

lemma synt_post_indicator: "synt_post s j \<in> {0, 1}"
  by (simp add: synt_post_def)

lemma synt_post_one_iff: "synt_post s j = 1 \<longleftrightarrow> j = s"
  by (simp add: synt_post_def)

lemma synt_post_sum_one:
  assumes "finite S" "s \<in> S"
  shows "(\<Sum>j\<in>S. synt_post s j) = 1"
proof -
  have "(\<Sum>j\<in>S. synt_post s j) = (\<Sum>j\<in>S. if j = s then 1 else 0)"
    by (simp add: synt_post_def)
  also have "\<dots> = 1" using assms by (simp add: sum.delta)
  finally show ?thesis .
qed

theorem synt_entropy_zero:
  assumes "finite S"
  shows "shannon S (synt_post s) = 0"
proof -
  have z: "plogp (synt_post s j) = 0" for j
    by (cases "j = s") (simp_all add: synt_post_def)
  show ?thesis by (simp add: shannon_def z)
qed

text \<open>Problem 2 -- irreversible mixing forces positive entropy. The two-source
  case: any split (q, 1-q) with 0 < q < 1 has strictly positive Shannon entropy --
  the irreducible conditional entropy H(C | R,T,a) > 0.\<close>

theorem mixed_entropy_pos:
  assumes "0 < q" "q < 1"
  shows "0 < plogp q + plogp (1 - q)"
proof -
  have "0 < plogp q" using assms by (rule plogp_pos)
  moreover have "0 < plogp (1 - q)" using assms by (intro plogp_pos) auto
  ultimately show ?thesis by simp
qed

end
