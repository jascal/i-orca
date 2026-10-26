theory PDC_Admission
  imports PDC_Derive
begin

text \<open>Admission packaging of PIC's pointwise margin certificate. The bound
  covers the target as well as every rival. A common offset is immaterial to
  a decision, but the candidate set must be the same on both sides.\<close>

theorem admitted_source_preserves_decision:
  fixes coalition source :: "'a \<Rightarrow> real"
  assumes target: "t \<in> V"
    and margin: "\<And>v. v \<in> V \<Longrightarrow> v \<noteq> t \<Longrightarrow> coalition t - coalition v > \<gamma>"
    and guard: "\<gamma> > 2 * \<delta>"
    and fidelity: "\<And>v. v \<in> V \<Longrightarrow> abs (source v - coalition v - \<kappa>) \<le> \<delta>"
  shows "decodes_to source V t"
proof -
  have certified: "decodes_to (\<lambda>v. source v - \<kappa>) V t"
  proof (rule decode_margin_certified[where L = coalition and \<delta> = \<delta>])
    show "\<And>v. v \<in> V \<Longrightarrow> abs (source v - \<kappa> - coalition v) \<le> \<delta>"
      using fidelity by (simp add: algebra_simps)
    show "t \<in> V" by (rule target)
    show "\<And>v. v \<in> V \<Longrightarrow> v \<noteq> t \<Longrightarrow> 2 * \<delta> < coalition t - coalition v"
      using margin guard by fastforce
  qed
  show ?thesis using certified by (simp add: decodes_to_def)
qed

context pic
begin

theorem crystallization_admitted_write:
  assumes target: "t \<in> V"
    and margin: "\<And>v. v \<in> V \<Longrightarrow> v \<noteq> t \<Longrightarrow> (Lc P t + b t) - (Lc P v + b v) > \<gamma>"
    and guard: "\<gamma> > 2 * \<delta>"
    and fidelity: "\<And>v. v \<in> V \<Longrightarrow> abs ((inner s (U v) + b v) - (Lc P v + b v) - \<kappa>) \<le> \<delta>"
  shows "decodes_to (\<lambda>v. inner s (U v) + b v) V t"
  by (rule admitted_source_preserves_decision[where coalition = "\<lambda>v. Lc P v + b v" and \<gamma> = \<gamma> and \<delta> = \<delta> and \<kappa> = \<kappa>])
    (rule target, rule margin, assumption+, rule guard, rule fidelity, assumption)

text \<open>The original complement form: adding the omitted sources preserves
  the coalition decision when their incidences are flat within delta.\<close>

theorem crystallization_complement_certified:
  assumes target: "t \<in> V"
    and margin: "\<And>v. v \<in> V \<Longrightarrow> v \<noteq> t \<Longrightarrow> (Lc P t + b t) - (Lc P v + b v) > \<gamma>"
    and guard: "\<gamma> > 2 * \<delta>"
    and partition: "finite P" "finite Q" "P \<inter> Q = {}" "S = P \<union> Q"
    and tail: "\<And>v. v \<in> V \<Longrightarrow> abs (Lc Q v - \<kappa>) \<le> \<delta>"
  shows "decodes_to Lt V t"
proof (rule admitted_source_preserves_decision[where coalition = "\<lambda>v. Lc P v + b v" and \<gamma> = \<gamma> and \<delta> = \<delta> and \<kappa> = \<kappa>, OF target])
  show "\<And>v. v \<in> V \<Longrightarrow> v \<noteq> t \<Longrightarrow> \<gamma> < (Lc P t + b t) - (Lc P v + b v)"
    by (rule margin)
  show "2 * \<delta> < \<gamma>" by (rule guard)
next
  fix v assume v: "v \<in> V"
  have split: "Lc S v = Lc P v + Lc Q v"
    using Lc_union[OF partition(1,2,3), of v] partition(4) by simp
  show "abs (Lt v - (Lc P v + b v) - \<kappa>) \<le> \<delta>"
    using tail[OF v] split by (simp add: Lt_def)
qed

end

text \<open>A finite candidate-wise certificate avoids a uniform whole-vocabulary
  radius: each body gap covers its own measured difference-of-differences.\<close>

theorem pairwise_source_preserves_decision:
  fixes coalition source :: "'a \<Rightarrow> real"
  assumes target: "t \<in> V"
    and guard: "\<And>v. v \<in> V \<Longrightarrow> v \<noteq> t \<Longrightarrow>
      abs ((source t - coalition t) - (source v - coalition v)) < coalition t - coalition v"
  shows "decodes_to source V t"
  unfolding decodes_to_def
proof (intro conjI ballI impI)
  show "t \<in> V" by (rule target)
next
  fix v assume v: "v \<in> V" and ne: "v \<noteq> t"
  have g: "abs ((source t - coalition t) - (source v - coalition v)) < coalition t - coalition v"
    by (rule guard[OF v ne])
  have lower: "- ((source t - coalition t) - (source v - coalition v)) \<le>
      abs ((source t - coalition t) - (source v - coalition v))"
    by simp
  show "source v < source t" using g lower by linarith
qed

text \<open>When outside rows stay fixed, one outside maximum per context is
  an exact decision reduction. A partition function is not that maximum.\<close>

theorem decode_fixed_outside_max:
  fixes L :: "'a \<Rightarrow> real"
  assumes "finite Outs" "Outs \<noteq> {}" "t \<in> C" "t \<notin> Outs"
  shows "decodes_to L (C \<union> Outs) t \<longleftrightarrow>
    decodes_to L C t \<and> Max (L ` Outs) < L t"
  using assms by (auto simp: decodes_to_def Max_less_iff)


text \<open>The absolute pairwise-drift sufficient guard requires more than
  agreement of the two positive gaps. It also bounds their relative scale.\<close>
lemma pairwise_gap_guard_iff:
  fixes host_gap body_gap :: real
  shows "abs (host_gap - body_gap) < body_gap \<longleftrightarrow>
    0 < host_gap \<and> host_gap < 2 * body_gap"
  by (simp only: abs_less_iff; linarith)

end
