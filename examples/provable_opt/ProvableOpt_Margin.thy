theory ProvableOpt_Margin
  imports ProvableOpt_Common
begin

text \<open>PO-T3 instance: a margin-dominated neuron drop. The full model's logit is a
  base plus one neuron's per-token contribution \<open>cneuron\<close> with \<open>\<bar>cneuron v\<bar> \<le> 1\<close>;
  the transform DROPS that neuron, so \<open>\<bar>L' v - L v\<bar> \<le> 1 = \<delta>\<close> everywhere. On a token
  whose margin exceeds \<open>2\<delta>\<close> the decode is certified unchanged by
  ``decode_margin_Max_certified``.

  We then exhibit the HONEST BOUNDEDNESS: a small-margin token (margin \<open>= 1 \<le> 2\<delta>\<close>)
  where an equally-\<open>\<delta>\<close>-bounded perturbation FLIPS the decode. So the \<open>2\<delta>\<close> guard is
  necessary, not cosmetic -- exactly the small-margin / forge-tax tokens the
  certificate (soundly) refuses to cover.\<close>

datatype tok = A | B

lemma UNIV_tok: "(UNIV :: tok set) = {A, B}"
  using tok.exhaust by auto

section \<open>Big-margin token: the decode is certified preserved\<close>

definition Lbase   :: "tok \<Rightarrow> real" where "Lbase x   = (if x = A then 10 else 0)"
definition cneuron :: "tok \<Rightarrow> real" where "cneuron x = (if x = A then 1 else - 1)"
definition Lfull   :: "tok \<Rightarrow> real" where "Lfull x   = Lbase x + cneuron x"

text \<open>The transform is "drop the neuron": \<open>L' = Lbase\<close>. Its per-token perturbation is
  bounded by \<open>\<delta> = 1\<close>, and the full model's margin at \<open>A\<close> is \<open>11 - (-1) = 12 > 2\<delta>\<close>.\<close>

lemma drop_neuron_pert: "\<bar>Lbase v - Lfull v\<bar> \<le> 1"
  by (simp add: Lbase_def Lfull_def cneuron_def)

lemma margin_full_A: "margin Lfull UNIV A = 12"
  by (simp add: margin_def UNIV_tok Lfull_def Lbase_def cneuron_def)

theorem margin_drop_decode_preserved: "decodes_to Lbase UNIV A"
proof (rule decode_margin_Max_certified[where L = Lfull and \<delta> = 1])
  show "finite (UNIV :: tok set)" by (simp add: UNIV_tok)
  show "UNIV - {A} \<noteq> {}" by (simp add: UNIV_tok)
  show "A \<in> UNIV" by simp
  show "\<And>v. v \<in> UNIV \<Longrightarrow> \<bar>Lbase v - Lfull v\<bar> \<le> 1" by (rule drop_neuron_pert)
  show "margin Lfull UNIV A > 2 * 1" by (simp add: margin_full_A)
qed

section \<open>Small-margin token: an equally-bounded perturbation can flip the decode\<close>

definition Lsmall :: "tok \<Rightarrow> real" where "Lsmall x = (if x = A then 1 else 0)"
definition Lflip  :: "tok \<Rightarrow> real" where "Lflip x  = (if x = A then 0 else 1)"

text \<open>\<open>margin Lsmall UNIV A = 1 \<le> 2\<delta>\<close> for \<open>\<delta> = 1\<close>; the perturbation \<open>Lsmall \<leadsto> Lflip\<close> is
  \<open>\<delta>\<close>-bounded yet the decode flips \<open>A \<leadsto> B\<close>. This is the certificate's boundary, made
  explicit.\<close>

theorem small_margin_decode_can_flip:
  "margin Lsmall UNIV A = 1
 \<and> (\<forall>v. \<bar>Lflip v - Lsmall v\<bar> \<le> 1)
 \<and> decodes_to Lsmall UNIV A
 \<and> \<not> decodes_to Lflip UNIV A
 \<and> decodes_to Lflip UNIV B"
proof (intro conjI)
  show "margin Lsmall UNIV A = 1"
    by (simp add: margin_def UNIV_tok Lsmall_def)
  show "\<forall>v. \<bar>Lflip v - Lsmall v\<bar> \<le> 1"
    by (simp add: Lflip_def Lsmall_def)
  show "decodes_to Lsmall UNIV A"
    by (auto simp: decodes_to_def UNIV_tok Lsmall_def)
  show "\<not> decodes_to Lflip UNIV A"
    by (auto simp: decodes_to_def Lflip_def)
  show "decodes_to Lflip UNIV B"
    by (auto simp: decodes_to_def UNIV_tok Lflip_def)
qed

text \<open>TIGHTNESS of the \<open>2\<delta>\<close> threshold: the guard \<open>margin > 2\<delta>\<close> cannot be weakened
  to \<open>margin \<ge> 2\<delta>\<close>. At \<open>margin = 2\<delta>\<close> exactly (here \<open>\<delta> = 1/2\<close>) a \<open>\<delta>\<close>-bounded
  perturbation can drive the two logits to a TIE, so the decode is no longer
  determined (\<open>t\<close> is not the STRICT argmax) -- preservation fails. So the strict
  inequality in ``decode_margin_certified`` is exactly right, not conservative.\<close>

definition Lhalf :: "tok \<Rightarrow> real" where "Lhalf x = 1/2"

theorem margin_guard_tight:
  "margin Lsmall UNIV A = 2 * (1/2)             \<comment> \<open>margin = 2\<delta> exactly, for \<delta> = 1/2\<close>
 \<and> (\<forall>v. \<bar>Lhalf v - Lsmall v\<bar> \<le> 1/2)            \<comment> \<open>the perturbation is \<delta>-bounded\<close>
 \<and> \<not> decodes_to Lhalf UNIV A                    \<comment> \<open>yet preservation FAILS (a tie)\<close>
 \<and> \<not> decodes_to Lhalf UNIV B"
proof (intro conjI)
  show "margin Lsmall UNIV A = 2 * (1/2)"
    by (simp add: margin_def UNIV_tok Lsmall_def)
  show "\<forall>v. \<bar>Lhalf v - Lsmall v\<bar> \<le> 1/2"
    by (simp add: Lhalf_def Lsmall_def)
  show "\<not> decodes_to Lhalf UNIV A"
    by (simp add: decodes_to_def UNIV_tok Lhalf_def)
  show "\<not> decodes_to Lhalf UNIV B"
    by (simp add: decodes_to_def UNIV_tok Lhalf_def)
qed

end
