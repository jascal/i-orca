theory MinimalDecider
  imports Characterization Density_Minimization
begin

text \<open>GAP #1 (executable minimal decider) + a clean slice of GAP #2 (end-to-end
  single-token composition). Two objects, and the honest gap between them:

  (A) `minimal_decider` -- an EXECUTABLE greedy: while some single source can be
      dropped with the coalition still deciding, drop one; stop when no single
      removal helps. Each step is the poly single-removal test (= the contrapositive
      of `all_necessary`). It provably returns a deciding SUBSET that is LOCALLY
      MINIMAL (`all_necessary`: no one source is droppable).

  (B) `irreducible_core_exists` / `decomposes_exists` -- every deciding finite
      coalition contains a GENUINELY irreducible deciding sub-coalition (an atom).
      This is unconditional and is what the end-to-end theorem rests on.

  THE GAP (kernel-filtered correction of "greedy => irreducible"): local minimality
  is NOT global irreducibility. The `c4` witness on `main` is `all_necessary` AND
  decided by the full set AND yet REDUCIBLE -- the pair {1,2} decides, reached only
  by removing TWO sources at once. So the cheap greedy certificate (A) under-approxes
  the hard global notion (B); closing that gap is exactly the conjectured-hard
  REDUCIBLE problem. We make this explicit below (`all_necessary_not_irreducible`).\<close>


section \<open>(A) The executable greedy minimal decider\<close>

text \<open>One greedy step: pick (Hilbert-choice) a source whose removal keeps the
  coalition deciding. Well-defined exactly when such a source exists.\<close>

definition drop_one :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat" where
  "drop_one c t V S = (SOME j. j \<in> S \<and> decides c (S - {j}) V t)"

lemma drop_one_props:
  assumes "\<exists>j\<in>S. decides c (S - {j}) V t"
  shows "drop_one c t V S \<in> S \<and> decides c (S - {drop_one c t V S}) V t"
proof -
  from assms have "\<exists>j. j \<in> S \<and> decides c (S - {j}) V t" by blast
  from someI_ex[OF this] show ?thesis unfolding drop_one_def .
qed

text \<open>The greedy itself. The recursive branch is guarded by `finite S` so the
  `card S` measure strictly decreases (an infinite S has `card S = 0` and would not
  decrease); the correctness theorems assume `finite S`, so the infinite fall-through
  is never exercised.\<close>

function minimal_decider ::
  "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat set" where
  "minimal_decider c t V S =
     (if finite S \<and> (\<exists>j\<in>S. decides c (S - {j}) V t)
      then minimal_decider c t V (S - {drop_one c t V S})
      else S)"
  by pat_completeness auto

termination
proof (relation "measure (\<lambda>(c,t,V,S). card S)", goal_cases)
  case 1 show ?case by (rule wf_measure)
next
  case (2 c t V S)
  from 2 have finS: "finite S" and ex: "\<exists>j\<in>S. decides c (S - {j}) V t" by auto
  from drop_one_props[OF ex] have mem: "drop_one c t V S \<in> S" by simp
  have "card (S - {drop_one c t V S}) < card S" by (rule card_Diff1_less[OF finS mem])
  then show ?case by simp
qed

text \<open>Keep the recursive equation OUT of the default simpset (it would loop on a
  symbolic argument); unfold it only in the two controlled step lemmas below.\<close>
declare minimal_decider.simps[simp del]

lemma md_step:
  assumes "finite S \<and> (\<exists>j\<in>S. decides c (S - {j}) V t)"
  shows "minimal_decider c t V S = minimal_decider c t V (S - {drop_one c t V S})"
  by (subst minimal_decider.simps) (simp only: if_P[OF assms])

lemma md_stop:
  assumes "\<not> (finite S \<and> (\<exists>j\<in>S. decides c (S - {j}) V t))"
  shows "minimal_decider c t V S = S"
  by (subst minimal_decider.simps) (simp only: if_not_P[OF assms])


subsection \<open>Correctness of the greedy\<close>

text \<open>(A1) The result is a subset of the input coalition.\<close>

lemma minimal_decider_subset:
  "finite S \<Longrightarrow> minimal_decider c t V S \<subseteq> S"
proof (induction "card S" arbitrary: S rule: less_induct)
  case less
  show ?case
  proof (cases "\<exists>j\<in>S. decides c (S - {j}) V t")
    case True
    with less.prems have cond: "finite S \<and> (\<exists>j\<in>S. decides c (S - {j}) V t)" by simp
    from drop_one_props[OF True]
      have mem: "drop_one c t V S \<in> S" by simp
    have lt: "card (S - {drop_one c t V S}) < card S"
      by (rule card_Diff1_less[OF less.prems mem])
    have fin': "finite (S - {drop_one c t V S})" using less.prems by simp
    have "minimal_decider c t V S = minimal_decider c t V (S - {drop_one c t V S})"
      by (rule md_step[OF cond])
    also have "\<dots> \<subseteq> S - {drop_one c t V S}" using less.hyps[OF lt fin'] .
    also have "\<dots> \<subseteq> S" by auto
    finally show ?thesis .
  next
    case False
    hence "\<not> (finite S \<and> (\<exists>j\<in>S. decides c (S - {j}) V t))" by blast
    from md_stop[OF this] show ?thesis by simp
  qed
qed

text \<open>(A2) The result still decides t (each greedy step preserves deciding by
  construction).\<close>

lemma minimal_decider_decides:
  "finite S \<Longrightarrow> decides c S V t \<Longrightarrow> decides c (minimal_decider c t V S) V t"
proof (induction "card S" arbitrary: S rule: less_induct)
  case less
  show ?case
  proof (cases "\<exists>j\<in>S. decides c (S - {j}) V t")
    case True
    with less.prems(1) have cond: "finite S \<and> (\<exists>j\<in>S. decides c (S - {j}) V t)" by simp
    from drop_one_props[OF True]
      have conj: "drop_one c t V S \<in> S \<and> decides c (S - {drop_one c t V S}) V t" .
    have mem: "drop_one c t V S \<in> S" using conj by simp
    have dd: "decides c (S - {drop_one c t V S}) V t" using conj by simp
    have lt: "card (S - {drop_one c t V S}) < card S"
      by (rule card_Diff1_less[OF less.prems(1) mem])
    have fin': "finite (S - {drop_one c t V S})" using less.prems(1) by simp
    have "minimal_decider c t V S = minimal_decider c t V (S - {drop_one c t V S})"
      by (rule md_step[OF cond])
    moreover have "decides c (minimal_decider c t V (S - {drop_one c t V S})) V t"
      by (rule less.hyps[OF lt fin' dd])
    ultimately show ?thesis by simp
  next
    case False
    hence "\<not> (finite S \<and> (\<exists>j\<in>S. decides c (S - {j}) V t))" by blast
    from md_stop[OF this] show ?thesis using less.prems(2) by simp
  qed
qed

text \<open>(A3) The result is LOCALLY MINIMAL: no single source can be removed while still
  deciding. This is exactly the greedy's stopping condition, = `all_necessary`.\<close>

lemma minimal_decider_all_necessary:
  "finite S \<Longrightarrow> all_necessary c (minimal_decider c t V S) V t"
proof (induction "card S" arbitrary: S rule: less_induct)
  case less
  show ?case
  proof (cases "\<exists>j\<in>S. decides c (S - {j}) V t")
    case True
    with less.prems have cond: "finite S \<and> (\<exists>j\<in>S. decides c (S - {j}) V t)" by simp
    from drop_one_props[OF True]
      have mem: "drop_one c t V S \<in> S" by simp
    have lt: "card (S - {drop_one c t V S}) < card S"
      by (rule card_Diff1_less[OF less.prems mem])
    have fin': "finite (S - {drop_one c t V S})" using less.prems by simp
    have "minimal_decider c t V S = minimal_decider c t V (S - {drop_one c t V S})"
      by (rule md_step[OF cond])
    moreover have "all_necessary c (minimal_decider c t V (S - {drop_one c t V S})) V t"
      by (rule less.hyps[OF lt fin'])
    ultimately show ?thesis by simp
  next
    case False
    hence notcond: "\<not> (finite S \<and> (\<exists>j\<in>S. decides c (S - {j}) V t))" by blast
    from md_stop[OF notcond] have md: "minimal_decider c t V S = S" by simp
    from False have "all_necessary c S V t" by (auto simp: all_necessary_def)
    thus ?thesis using md by simp
  qed
qed

text \<open>(A4) Density payoff of the greedy: a subset fires no more neurons, so the
  greedy never increases the firing count on any sample (Density.total_firing_mono).\<close>

lemma minimal_decider_firing_bound:
  assumes "finite S"
  shows "(\<Sum>x\<in>Es. card (active_on a \<theta> x (minimal_decider c t V S)))
         \<le> (\<Sum>x\<in>Es. card (active_on a \<theta> x S))"
  by (rule total_firing_mono[OF minimal_decider_subset[OF assms] assms])


section \<open>(B) Genuine irreducible cores exist (the global object)\<close>

text \<open>Every deciding finite coalition decomposes (in the sense of Density_Minimization)
  to an irreducible atom: strong induction on card S -- if S is already irreducible we
  are done (base), otherwise a proper deciding subset P exists (has_suff_sub), it is
  smaller and deciding, so it has an atom by IH, and `step` lifts it back to S.\<close>

lemma decomposes_exists:
  assumes "finite S" and "decides c S V t" and "\<exists>v\<in>V. v \<noteq> t"
  shows "\<exists>A. decomposes c t V S A"
  using assms
proof (induction "card S" arbitrary: S rule: less_induct)
  case less
  show ?case
  proof (cases "irreducible c S V t")
    case True
    thus ?thesis by (blast intro: decomposes.base)
  next
    case False
    with less.prems(2) have "has_suff_sub c S V t" by (simp add: irreducible_def)
    then obtain P where P: "P \<noteq> {}" "P \<subset> S" "decides c P V t"
      by (auto simp: has_suff_sub_def)
    have finP: "finite P" using P(2) less.prems(1)
      by (meson finite_subset psubset_imp_subset)
    have "card P < card S" by (rule psubset_card_mono[OF less.prems(1) P(2)])
    from less.hyps[OF this finP P(3) less.prems(3)]
      obtain A where A: "decomposes c t V P A" by blast
    have "decomposes c t V S A"
      by (rule decomposes.step[OF P(2) P(1) P(3) A])
    thus ?thesis by blast
  qed
qed

text \<open>Read off the atom's three properties from the existing decomposes lemmas.\<close>

lemma irreducible_core_exists:
  assumes "finite S" and "decides c S V t" and "\<exists>v\<in>V. v \<noteq> t"
  shows "\<exists>A. A \<subseteq> S \<and> decides c A V t \<and> irreducible c A V t"
proof -
  from decomposes_exists[OF assms] obtain A where A: "decomposes c t V S A" by blast
  have "A \<subseteq> S" by (rule decomposes_subset[OF A])
  moreover have "decides c A V t" by (rule decomposes_decides[OF A])
  moreover have "irreducible c A V t" by (rule decomposes_atom[OF A])
  ultimately show ?thesis by blast
qed


section \<open>End-to-end single-token composition (slice of GAP #2)\<close>

text \<open>Every deciding token has an IRREDUCIBLE atom that (i) is a sub-coalition,
  (ii) still decides the same outcome, and (iii) fires no more neurons than the
  original on ANY input sample. This is the single-token form of "the pipeline
  yields bits such that every token is still decided and per-token active density
  does not go up" -- the density-minimisation guarantee, proved end to end.\<close>

theorem every_deciding_token_has_firing_minimal_irreducible_atom:
  assumes "finite S" and "decides c S V t" and "\<exists>v\<in>V. v \<noteq> t"
  shows "\<exists>A. A \<subseteq> S \<and> decides c A V t \<and> irreducible c A V t
             \<and> (\<forall>a \<theta> Es. (\<Sum>x\<in>Es. card (active_on a \<theta> x A))
                          \<le> (\<Sum>x\<in>Es. card (active_on a \<theta> x S)))"
proof -
  from irreducible_core_exists[OF assms] obtain A
    where A: "A \<subseteq> S" "decides c A V t" "irreducible c A V t" by blast
  have "\<forall>a \<theta> Es. (\<Sum>x\<in>Es. card (active_on a \<theta> x A))
                  \<le> (\<Sum>x\<in>Es. card (active_on a \<theta> x S))"
    using total_firing_mono[OF A(1) assms(1)] by blast
  thus ?thesis using A by blast
qed


section \<open>End-to-end MULTI-token composition (the pipeline theorem, GAP #2)\<close>

text \<open>A clean, hub-aware subadditivity bound on the per-token active count for ANY
  shared core H: active neurons of a coalition X split into those inside the hub H
  (at most card H) and the private remainder (X - H). This is the honest content of
  Hub.per_token_active_bound, restated for an arbitrary finite set so it instantiates
  directly at each token's atom (no higher-order matching needed).\<close>

lemma active_hub_bound:
  assumes finX: "finite X" and finH: "finite H"
  shows "card (active_on a \<theta> x X) \<le> card H + card (X - H)"
proof -
  have sub: "active_on a \<theta> x X \<subseteq> X" by (auto simp: active_on_def)
  have "(X \<inter> H) \<union> (X - H) = X" by auto
  moreover have "(X \<inter> H) \<inter> (X - H) = {}" by auto
  ultimately have eq: "card X = card (X \<inter> H) + card (X - H)"
    using finX by (metis card_Un_disjoint finite_Diff finite_Int)
  have "card (X \<inter> H) \<le> card H" by (meson card_mono finH inf_le2)
  hence "card X \<le> card H + card (X - H)" using eq by simp
  moreover have "card (active_on a \<theta> x X) \<le> card X"
    using finX sub by (simp add: card_mono)
  ultimately show ?thesis by simp
qed

text \<open>The pipeline theorem. Given a finite token sample E where every token e is
  decided by its (finite) source coalition S e over outcomes V e, the pipeline
  assigns each token an IRREDUCIBLE atom M e such that, simultaneously for every
  token: (i) M e is a sub-coalition of S e, (ii) M e still decides the same outcome,
  (iii) M e is irreducible (a genuine entangled bit, not further splittable), (iv) on
  every input x the atom fires no more neurons than the original coalition, and (v)
  for any shared core H the per-token active count is bounded by
  card H + card (M e - H). A single existential choice (bchoice) selects the whole
  family of atoms at once.\<close>

theorem pipeline_composition:
  assumes E_props: "\<forall>e\<in>E. finite (S e) \<and> decides c (S e) (V e) (t e) \<and> (\<exists>v\<in>V e. v \<noteq> t e)"
  shows "\<exists>M. \<forall>e\<in>E. M e \<subseteq> S e
                 \<and> decides c (M e) (V e) (t e)
                 \<and> irreducible c (M e) (V e) (t e)
                 \<and> (\<forall>a \<theta> x. card (active_on a \<theta> x (M e)) \<le> card (active_on a \<theta> x (S e)))
                 \<and> (\<forall>a \<theta> x H. finite H \<longrightarrow>
                       card (active_on a \<theta> x (M e)) \<le> card H + card (M e - H))"
proof -
  have core_ex: "\<forall>e\<in>E. \<exists>A. A \<subseteq> S e \<and> decides c A (V e) (t e) \<and> irreducible c A (V e) (t e)"
  proof
    fix e assume e: "e \<in> E"
    with E_props have "finite (S e)" "decides c (S e) (V e) (t e)" "\<exists>v\<in>V e. v \<noteq> t e"
      by auto
    thus "\<exists>A. A \<subseteq> S e \<and> decides c A (V e) (t e) \<and> irreducible c A (V e) (t e)"
      by (rule irreducible_core_exists)
  qed
  have ex: "\<exists>M. \<forall>e\<in>E. M e \<subseteq> S e \<and> decides c (M e) (V e) (t e) \<and> irreducible c (M e) (V e) (t e)"
    using core_ex by (rule bchoice)
  then obtain M where
    M: "\<forall>e\<in>E. M e \<subseteq> S e \<and> decides c (M e) (V e) (t e) \<and> irreducible c (M e) (V e) (t e)" ..
  have "\<forall>e\<in>E. M e \<subseteq> S e \<and> decides c (M e) (V e) (t e) \<and> irreducible c (M e) (V e) (t e)
              \<and> (\<forall>a \<theta> x. card (active_on a \<theta> x (M e)) \<le> card (active_on a \<theta> x (S e)))
              \<and> (\<forall>a \<theta> x H. finite H \<longrightarrow>
                    card (active_on a \<theta> x (M e)) \<le> card H + card (M e - H))"
  proof
    fix e assume e: "e \<in> E"
    have core: "M e \<subseteq> S e \<and> decides c (M e) (V e) (t e) \<and> irreducible c (M e) (V e) (t e)"
      using M e by (rule bspec)
    have finSe: "finite (S e)" using E_props e by auto
    have MsubS: "M e \<subseteq> S e" using core by simp
    have finMe: "finite (M e)" using MsubS finSe by (rule finite_subset)
    have fb: "\<forall>a \<theta> x. card (active_on a \<theta> x (M e)) \<le> card (active_on a \<theta> x (S e))"
      using active_count_mono[OF MsubS finSe] by blast
    have hb: "\<forall>a \<theta> x H. finite H \<longrightarrow>
                 card (active_on a \<theta> x (M e)) \<le> card H + card (M e - H)"
      using active_hub_bound[OF finMe] by blast
    from core fb hb
    show "M e \<subseteq> S e \<and> decides c (M e) (V e) (t e) \<and> irreducible c (M e) (V e) (t e)
              \<and> (\<forall>a \<theta> x. card (active_on a \<theta> x (M e)) \<le> card (active_on a \<theta> x (S e)))
              \<and> (\<forall>a \<theta> x H. finite H \<longrightarrow>
                    card (active_on a \<theta> x (M e)) \<le> card H + card (M e - H))" by blast
  qed
  thus ?thesis by blast
qed

text \<open>Specialisation to the literal "shared core" budget: per-token active count is at
  most card H + max over the sample of the private sizes card (M e - H). This is the
  form Grok stated -- per-token active density bounded by the hub size plus the largest
  private remainder -- now discharged against the kernel.\<close>

corollary pipeline_density_max_bound:
  assumes E_props: "\<forall>e\<in>E. finite (S e) \<and> decides c (S e) (V e) (t e) \<and> (\<exists>v\<in>V e. v \<noteq> t e)"
      and finE: "finite E"
  shows "\<exists>M. (\<forall>e\<in>E. M e \<subseteq> S e \<and> decides c (M e) (V e) (t e) \<and> irreducible c (M e) (V e) (t e))
            \<and> (\<forall>e\<in>E. \<forall>a \<theta> x. \<forall>H::nat set. finite H \<longrightarrow>
                  card (active_on a \<theta> x (M e))
                    \<le> card H + Max ((\<lambda>i. card (M i - H)) ` E))"
proof -
  from pipeline_composition[OF E_props] obtain M :: "'a \<Rightarrow> nat set" where
    M: "\<forall>e\<in>E. M e \<subseteq> S e \<and> decides c (M e) (V e) (t e) \<and> irreducible c (M e) (V e) (t e)
            \<and> (\<forall>a \<theta> x. card (active_on a \<theta> x (M e)) \<le> card (active_on a \<theta> x (S e)))
            \<and> (\<forall>a \<theta> x. \<forall>H::nat set. finite H \<longrightarrow>
                  card (active_on a \<theta> x (M e)) \<le> card H + card (M e - H))" by blast
  have core: "\<forall>e\<in>E. M e \<subseteq> S e \<and> decides c (M e) (V e) (t e) \<and> irreducible c (M e) (V e) (t e)"
    using M by blast
  have bnd: "\<forall>e\<in>E. \<forall>a \<theta> x. \<forall>H::nat set. finite H \<longrightarrow>
              card (active_on a \<theta> x (M e)) \<le> card H + Max ((\<lambda>i. card (M i - H)) ` E)"
  proof (intro ballI allI impI)
    fix e a \<theta> x and H :: "nat set"
    assume e: "e \<in> E" and finH: "finite H"
    have step1: "card (active_on a \<theta> x (M e)) \<le> card H + card (M e - H)"
      using M e finH by blast
    have step2: "card (M e - H) \<le> Max ((\<lambda>i. card (M i - H)) ` E)"
      by (rule Max_ge) (use finE e in auto)
    show "card (active_on a \<theta> x (M e)) \<le> card H + Max ((\<lambda>i. card (M i - H)) ` E)"
      using step1 step2 by linarith
  qed
  from core bnd show ?thesis by blast
qed


section \<open>The honest gap: local minimality is NOT global irreducibility\<close>

text \<open>Kernel-filtered correction of "single-removal greedy => irreducible". The greedy
  delivers `all_necessary` (A3), but `all_necessary` does NOT entail `irreducible`:
  the `c4` token from the n=3 sharpness proof on `main` is `all_necessary` (every
  triple S-{j} fails) yet REDUCIBLE -- the pair {1,2} decides, reachable only by a
  TWO-source removal the greedy never tries. So `minimal_decider` is a sound poly
  UNDER-approximation of the irreducible core, and the residual `irreducible_core_exists`
  (which may need multi-source removals) is the genuinely hard part.\<close>

lemma all_necessary_not_irreducible:
  "all_necessary c4 {1,2,3,4} {0,1,2} 0 \<and> \<not> irreducible c4 {1,2,3,4} {0,1,2} 0"
  using c4_all_necessary c4_reducible by blast

end
