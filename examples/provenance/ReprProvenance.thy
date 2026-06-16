(*
  ReprProvenance.thy -- the realistic scenario (ii): only the BUCKETING-PASS data is
  known, NOT the model's training data.

  In scenario (i) (lab-only) the buckets are built over the model's training data, so
  a bucket label is genuine TRAINING provenance and Problem 2 (influence functions,
  CondNumber.thy) is the real question. In scenario (ii) the bucketing pass runs a
  KNOWN analysis corpus through the ALREADY-TRAINED model; a bucket label is then only
  REPRESENTATIONAL provenance -- "this token was emitted from a region of feature
  space that, in my known data, is occupied by corpus C_j" -- not a claim about which
  corpus shaped the weights.

  Provenance.thy/Attribution.thy carry over verbatim to (ii) (they are statements
  about the bucketing, which is fully known): representational provenance is exact
  (synt_entropy_zero) and the support bound holds (provenance_support_bound). What
  (ii) cannot do is reach GENERATIVE (training) provenance. This theory pins the
  gap with three results:

    RECOVERY   faithful_posterior_agreement : where the bucketing pass is faithful,
               representational provenance == generative provenance -- (ii) recovers (i).
    WEAKENING  generative_underdetermined_off_used : outside the covered region the
               generative label is provably ambiguous (two training worlds agree with
               the bucketing pass everywhere it measured, yet disagree off it).
    HONESTY    uncovered_forces_abstention : a token whose buckets are entirely
               uncovered admits no normalised posterior -- the sound output is
               "unknown", never a guess.
*)

theory ReprProvenance
  imports Provenance Attribution
begin

type_synonym bucket = nat

text \<open>The bucketing pass (known data) gives an observed label map obs; the
  (unknown in scenario ii) training truth is a generative label map g. Faithfulness
  on a bucket set U: the two agree on every bucket in U.\<close>

definition faithful :: "bucket set \<Rightarrow> (bucket \<Rightarrow> source) \<Rightarrow> (bucket \<Rightarrow> source) \<Rightarrow> bool" where
  "faithful U obs g \<longleftrightarrow> (\<forall>b\<in>U. obs b = g b)"

text \<open>RECOVERY. Where the bucketing pass is faithful, representational provenance
  (from obs) coincides with generative provenance (g): scenario (ii) recovers (i).\<close>

lemma faithful_agreement:
  assumes "faithful U obs g" "b \<in> U"
  shows "obs b = g b"
  using assms by (auto simp: faithful_def)

lemma faithful_posterior_agreement:
  assumes "faithful U obs g" "b \<in> U"
  shows "synt_post (obs b) = synt_post (g b)"
proof -
  have "obs b = g b" using assms by (auto simp: faithful_def)
  thus ?thesis by simp
qed

text \<open>WEAKENING. Outside the covered region the generative label is
  underdetermined: two training worlds agree with the bucketing pass on every
  measured bucket U yet disagree on an unmeasured bucket b. So a token that fires a
  bucket the pass never covered has provably ambiguous generative provenance,
  however exact its representational provenance.\<close>

lemma generative_underdetermined_off_used:
  assumes "b \<notin> U"
  shows "\<exists>g1 g2. faithful U obs g1 \<and> faithful U obs g2 \<and> g1 b \<noteq> g2 b"
proof -
  have "faithful U obs obs" by (simp add: faithful_def)
  moreover have "faithful U obs (obs(b := Suc (obs b)))"
    using assms by (auto simp: faithful_def)
  moreover have "obs b \<noteq> (obs(b := Suc (obs b))) b" by simp
  ultimately show ?thesis by blast
qed

text \<open>HONESTY (closed world). If the response's buckets are entirely uncovered by
  the bucketing pass (candidate set empty), no normalised posterior exists -- the
  sum is 0, never 1 -- so the only sound output is "unknown" (abstain).\<close>

lemma uncovered_no_distribution:
  assumes "candidates bs = {}"
  shows "(\<Sum>j\<in>candidates bs. p j) = 0"
  using assms by simp

lemma uncovered_forces_abstention:
  assumes "consistent bs p" "candidates bs = {}"
  shows "p j = 0"
  using assms by (auto simp: consistent_def)

end
