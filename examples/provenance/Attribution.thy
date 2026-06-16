(*
  Attribution.thy -- ties the pieces together (Problem 2, the architecture payoff).

  A response R is built from a list of buckets, each carrying a source-label set.
  The candidate sources for R are the union of those label sets (candidates).

  Data-processing shadow. Because R depends on the corpora ONLY through the buckets
  (the Markov chain C -> buckets -> R), any posterior consistent with the bucket
  provenance gives ZERO mass to every source outside the used buckets
  (provenance_support_bound). This is the discrete, exactly-provable shadow of the
  mutual-information bound I(R; C_j | T,a) <= (information through buckets): a sound
  containment, deliberately LOOSE in general (the union can be large).

  Isolation payoff. When every used bucket carries the same single source s (a
  perfectly isolated, high-density response), the candidate set collapses to {s},
  and a consistent posterior normalised to 1 is forced to be EXACTLY the syntactic
  indicator synt_post s (isolated_attribution_exact). Here the hard statistical
  question (Problem 2) degenerates into the trivial syntactic one (Problem 1): zero
  uncertainty. This is "tight inside well-isolated, verified buckets" -- the best
  practical handle the architecture provides.
*)

theory Attribution
  imports Provenance
begin

definition candidates :: "source set list \<Rightarrow> source set" where
  "candidates bs = \<Union> (set bs)"

definition consistent :: "source set list \<Rightarrow> (source \<Rightarrow> real) \<Rightarrow> bool" where
  "consistent bs p \<longleftrightarrow> (\<forall>j. j \<notin> candidates bs \<longrightarrow> p j = 0)"

text \<open>The data-processing support bound: no influence mass lands outside the
  buckets the response actually used.\<close>

theorem provenance_support_bound:
  assumes "consistent bs p" "j \<notin> candidates bs"
  shows "p j = 0"
  using assms by (simp add: consistent_def)

text \<open>A response all of whose buckets carry the single source s has candidate set
  exactly {s}.\<close>

lemma candidates_single:
  assumes "bs \<noteq> []" "\<forall>b\<in>set bs. b = {s}"
  shows "candidates bs = {s}"
proof
  show "candidates bs \<subseteq> {s}"
    using assms(2) by (auto simp: candidates_def)
next
  from assms(1) obtain b where "b \<in> set bs" by (cases bs) auto
  with assms(2) show "{s} \<subseteq> candidates bs"
    by (auto simp: candidates_def)
qed

text \<open>Isolation payoff: inside an isolated single-source response, a consistent,
  normalised attribution posterior IS the exact syntactic indicator.\<close>

theorem isolated_attribution_exact:
  assumes ne: "bs \<noteq> []"
      and single: "\<forall>b\<in>set bs. b = {s}"
      and cons: "consistent bs p"
      and norm: "(\<Sum>j\<in>candidates bs. p j) = 1"
  shows "p = synt_post s"
proof (rule ext)
  fix j
  have cand: "candidates bs = {s}"
    using ne single by (rule candidates_single)
  have ps: "p s = 1"
    using norm cand by simp
  show "p j = synt_post s j"
  proof (cases "j = s")
    case True
    thus ?thesis using ps by (simp add: synt_post_def)
  next
    case False
    hence "j \<notin> candidates bs" using cand by simp
    hence "p j = 0" using cons by (simp add: consistent_def)
    thus ?thesis using False by (simp add: synt_post_def)
  qed
qed

end
