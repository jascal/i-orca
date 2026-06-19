theory ProvableOpt_Margin_Surface
  imports ProvableOpt_Margin
begin

text \<open>PO-T3 (general, pointwise). If a transform perturbs each logit by at most δ and every competitor of t trails it by more than 2δ under L, then t is still the strict argmax under L′ — the decode is preserved. Cites `decode_margin_certified` in ProvableOpt_Common.thy.\<close>
theorem decodemargincertified:
  shows "(\<And>v. v \<in> V \<Longrightarrow> abs (L' v - L v) \<le> \<delta>) \<Longrightarrow> t \<in> V \<Longrightarrow> (\<And>v. v \<in> V \<Longrightarrow> v \<noteq> t \<Longrightarrow> L t - L v > 2 * \<delta>) \<Longrightarrow> decodes_to L' V t"
proof -
  show "(\<And>v. v \<in> V \<Longrightarrow> abs (L' v - L v) \<le> \<delta>) \<Longrightarrow> t \<in> V \<Longrightarrow> (\<And>v. v \<in> V \<Longrightarrow> v \<noteq> t \<Longrightarrow> L t - L v > 2 * \<delta>) \<Longrightarrow> decodes_to L' V t" by (rule decode_margin_certified)
qed

text \<open>PO-T3 (general, margin form). The same with the margin written as the gap to the best competitor (`margin L V t > 2δ`), for a finite token set. Cites `decode_margin_Max_certified`.\<close>
theorem decodemarginmaxcertified:
  shows "finite V \<Longrightarrow> V - {t} \<noteq> {} \<Longrightarrow> t \<in> V \<Longrightarrow> (\<And>v. v \<in> V \<Longrightarrow> abs (L' v - L v) \<le> \<delta>) \<Longrightarrow> margin L V t > 2 * \<delta> \<Longrightarrow> decodes_to L' V t"
proof -
  show "finite V \<Longrightarrow> V - {t} \<noteq> {} \<Longrightarrow> t \<in> V \<Longrightarrow> (\<And>v. v \<in> V \<Longrightarrow> abs (L' v - L v) \<le> \<delta>) \<Longrightarrow> margin L V t > 2 * \<delta> \<Longrightarrow> decodes_to L' V t" by (rule decode_margin_Max_certified)
qed

text \<open>The concrete instance: dropping a margin-dominated neuron (perturbation ≤ δ=1) leaves the big-margin token A (margin 12 > 2δ) as the decode. Cites `margin_drop_decode_preserved`.\<close>
theorem margindropdecodepreserved:
  shows "decodes_to Lbase UNIV A"
proof -
  show "decodes_to Lbase UNIV A" by (rule margin_drop_decode_preserved)
qed

text \<open>The honest boundedness: a small-margin token (margin = 1 ≤ 2δ) where an equally-δ-bounded perturbation FLIPS the decode A→B. The 2δ guard is necessary, not cosmetic — the certificate (soundly) refuses small-margin / forge-tax tokens. Cites `small_margin_decode_can_flip`.\<close>
theorem smallmargindecodecanflip:
  shows "margin Lsmall UNIV A = 1 \<and> (\<forall>v. abs (Lflip v - Lsmall v) \<le> 1) \<and> decodes_to Lsmall UNIV A \<and> \<not> decodes_to Lflip UNIV A \<and> decodes_to Lflip UNIV B"
proof -
  show "margin Lsmall UNIV A = 1 \<and> (\<forall>v. abs (Lflip v - Lsmall v) \<le> 1) \<and> decodes_to Lsmall UNIV A \<and> \<not> decodes_to Lflip UNIV A \<and> decodes_to Lflip UNIV B" by (rule small_margin_decode_can_flip)
qed

end
