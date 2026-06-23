(*
  PIC_Logic.thy -- the semiring-Datalog (logic-programming) face of PIC.

  The next-token decision is a Datalog program (the one `fieldrun export --logic` emits and Soufflé
  runs): facts = the encoder's `contrib` rows, clauses = the rule incidences, query = `decide`. This
  theory gives that program its kernel semantics:

    Tp / answer            : the immediate-consequence operator and its least model (lfp) -- monotone,
                             closed under the clauses, least among closed sets.
    reach_all              : the lfp captures UNBOUNDED recursion (the induction-macro face), unlike a
                             single finite forward pass.
    demand_restrict_lfp    : magic-sets / demand transform is LOSSLESS (lfp of the demand-restricted
                             program = the demanded part of the answer). [self-contained copy of the
                             reusable PROVABLE_OPT core, ProvableOpt_Common]
    demand_closed_TpI      : the DECIDABLE rule-level criterion (every clause producing a demanded head
                             has a body inside the demand) implies the semantic demand-closure.
    decode_magic_sets_lossless : on a concrete decode program, the demand transform drops a dead atom
                             yet preserves the decode -- the LP face of "the decode needs only its cone"
                             (mass != causation as a program transform).

  Self-contained: imports PIC_Core only; 0 sorry, quick_and_dirty = false.
  Companion to the language spec pic/spec/PIC_LP.md.
*)
theory PIC_Logic
  imports PIC_Core
begin

section \<open>The immediate-consequence operator and the least model\<close>

text \<open>A PIC clause @{text "(B, h)"} fires head @{term h} once its body @{term B} is derived; a fact is
  a clause with empty body. The semiring weights (PIC\_SPEC \<section>2) annotate the atoms; this is the
  Boolean derivability backbone they ride on.\<close>

type_synonym 'atom clause = "'atom set \<times> 'atom"

definition Tp :: "('atom clause) set \<Rightarrow> 'atom set \<Rightarrow> 'atom set" where
  "Tp P I = I \<union> {h. \<exists>B. (B, h) \<in> P \<and> B \<subseteq> I}"

lemma Tp_mono: "mono (Tp P)"
  unfolding mono_def Tp_def by blast

definition answer :: "('atom clause) set \<Rightarrow> 'atom set" where
  "answer P = lfp (Tp P)"

text \<open>The answer is the LEAST MODEL: a fixpoint (closed under every clause) contained in every closed set.\<close>
lemma answer_unfold: "Tp P (answer P) = answer P"
  unfolding answer_def by (metis Tp_mono lfp_unfold)

lemma answer_closed:
  assumes "(B, h) \<in> P" and "B \<subseteq> answer P" shows "h \<in> answer P"
proof -
  have "h \<in> Tp P (answer P)" unfolding Tp_def using assms by blast
  thus ?thesis by (simp add: answer_unfold)
qed

lemma answer_least:
  assumes "Tp P M \<subseteq> M" shows "answer P \<subseteq> M"
  unfolding answer_def using assms by (rule lfp_lowerbound)

subsection \<open>Genuine recursion: the lfp captures unbounded depth\<close>

text \<open>Unlike a single finite (stratified) forward pass, the lfp captures UNBOUNDED recursion -- the LP
  face of the induction macro / arbitrary-depth copying. A one-rule recursive program derives an
  infinite set.\<close>
definition Preach :: "(nat clause) set" where
  "Preach = insert ({}, 0) {({n}, Suc n) | n. True}"

lemma reach_all: "n \<in> answer Preach"
proof (induct n)
  case 0
  have "({}, 0) \<in> Preach" by (simp add: Preach_def)
  thus ?case using answer_closed[of "{}" 0 Preach] by simp
next
  case (Suc n)
  have "({n}, Suc n) \<in> Preach" by (auto simp: Preach_def)
  thus ?case using answer_closed[of "{n}" "Suc n" Preach] Suc by simp
qed

section \<open>Magic-sets = demand-closure (the kernel-proved optimization, self-contained)\<close>

text \<open>The query-demand transform and its losslessness -- the metatheory of the language. Definitions and
  the @{text demand_restrict_lfp} proof are the reusable PROVABLE\_OPT core (i-orca
  @{text ProvableOpt_Common}), copied so PIC\_Logic stands alone.\<close>

definition restrict_op :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "restrict_op T D = (\<lambda>S. T S \<inter> D)"

definition demand_closed :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "demand_closed T D \<longleftrightarrow> (\<forall>S. T S \<inter> D = T (S \<inter> D) \<inter> D)"

lemma mono_restrict_op:
  assumes "mono T" shows "mono (restrict_op T D)"
  using assms by (auto simp: restrict_op_def mono_def)

theorem demand_restrict_lfp:
  assumes mono: "mono T" and dc: "demand_closed T D"
  shows "lfp (restrict_op T D) = lfp T \<inter> D"
proof -
  have monoT': "mono (restrict_op T D)" using mono by (rule mono_restrict_op)
  from dc have dcS: "\<And>S. T S \<inter> D = T (S \<inter> D) \<inter> D"
    by (simp add: demand_closed_def)
  have fixR: "restrict_op T D (lfp T \<inter> D) = lfp T \<inter> D"
  proof -
    have "restrict_op T D (lfp T \<inter> D) = T (lfp T \<inter> D) \<inter> D"
      by (simp add: restrict_op_def)
    also have "\<dots> = T (lfp T) \<inter> D" by (metis dcS)
    also have "\<dots> = lfp T \<inter> D" by (metis lfp_unfold[OF mono])
    finally show ?thesis .
  qed
  have le1: "lfp (restrict_op T D) \<subseteq> lfp T \<inter> D"
    by (rule lfp_lowerbound) (simp add: fixR)
  have subD: "lfp (restrict_op T D) \<subseteq> D"
  proof -
    have "lfp (restrict_op T D) = restrict_op T D (lfp (restrict_op T D))"
      by (metis lfp_unfold[OF monoT'])
    also have "\<dots> \<subseteq> D" by (simp add: restrict_op_def)
    finally show ?thesis .
  qed
  have pre: "T (lfp (restrict_op T D) \<union> (- D)) \<subseteq> lfp (restrict_op T D) \<union> (- D)"
  proof
    fix x assume x: "x \<in> T (lfp (restrict_op T D) \<union> (- D))"
    show "x \<in> lfp (restrict_op T D) \<union> (- D)"
    proof (cases "x \<in> D")
      case False thus ?thesis by simp
    next
      case True
      have "x \<in> T (lfp (restrict_op T D) \<union> (- D)) \<inter> D" using x True by simp
      also have "T (lfp (restrict_op T D) \<union> (- D)) \<inter> D
                   = T ((lfp (restrict_op T D) \<union> (- D)) \<inter> D) \<inter> D"
        by (rule dcS)
      also have "(lfp (restrict_op T D) \<union> (- D)) \<inter> D = lfp (restrict_op T D)"
        using subD by auto
      finally have "x \<in> T (lfp (restrict_op T D)) \<inter> D" .
      hence "x \<in> restrict_op T D (lfp (restrict_op T D))"
        by (simp add: restrict_op_def)
      also have "\<dots> = lfp (restrict_op T D)" by (metis lfp_unfold[OF monoT'])
      finally show ?thesis by simp
    qed
  qed
  have "lfp T \<subseteq> lfp (restrict_op T D) \<union> (- D)"
    by (rule lfp_lowerbound) (rule pre)
  hence le2: "lfp T \<inter> D \<subseteq> lfp (restrict_op T D)" using subD by auto
  from le1 le2 show ?thesis by auto
qed

text \<open>SYNTACTIC \<Longrightarrow> SEMANTIC demand-closure: if every clause that can produce a demanded head has its
  body inside the demand, the program is demand-closed -- the decidable, rule-level criterion a checker
  would use (the @{text ProvableOpt_Datalog} bridge, on the @{const Tp} operator).\<close>
lemma demand_closed_TpI:
  assumes "\<And>B h. (B, h) \<in> P \<Longrightarrow> h \<in> D \<Longrightarrow> B \<subseteq> D"
  shows "demand_closed (Tp P) D"
  unfolding demand_closed_def Tp_def using assms by blast

section \<open>The decode program: magic-sets drops the dead atom, keeps the decode\<close>

text \<open>A minimal decode over two candidates: facts @{term C0},@{term C1}; logit rules
  @{term L0}\<open>\<Leftarrow>\<close>@{term C0}, @{term L1}\<open>\<Leftarrow>\<close>@{term C1}; the decode @{term Dec}\<open>\<Leftarrow>\<close>@{text "{L0,L1}"}; plus a
  DEAD auxiliary @{term Aux}\<open>\<Leftarrow>\<close>@{term C0} that the query never needs. The decode demand omits @{term Aux};
  the program is demand-closed for it, so the demand-restricted run computes @{term Dec} WITHOUT deriving
  @{term Aux} -- the LP face of "the decode needs only its own cone".\<close>
datatype datom = C0 | C1 | L0 | L1 | Dec | Aux

definition Pdec :: "(datom clause) set" where
  "Pdec = {({}, C0), ({}, C1), ({C0}, L0), ({C1}, L1), ({L0, L1}, Dec), ({C0}, Aux)}"

definition Ddec :: "datom set" where
  "Ddec = {C0, C1, L0, L1, Dec}"   \<comment> \<open>everything decode-relevant; omits @{term Aux}\<close>

lemma Pdec_demand_closed: "demand_closed (Tp Pdec) Ddec"
  by (rule demand_closed_TpI) (auto simp: Pdec_def Ddec_def)

theorem decode_magic_sets_lossless:
  "lfp (restrict_op (Tp Pdec) Ddec) = lfp (Tp Pdec) \<inter> Ddec"
  by (rule demand_restrict_lfp[OF Tp_mono Pdec_demand_closed])

text \<open>Non-vacuous: the decode @{term Dec} is preserved, the dead @{term Aux} is never derived.\<close>
lemma Dec_in_answer: "Dec \<in> answer Pdec"
proof -
  have c0: "C0 \<in> answer Pdec" using answer_closed[of "{}" C0 Pdec] by (simp add: Pdec_def)
  have c1: "C1 \<in> answer Pdec" using answer_closed[of "{}" C1 Pdec] by (simp add: Pdec_def)
  have l0: "L0 \<in> answer Pdec" using answer_closed[of "{C0}" L0 Pdec] c0 by (auto simp: Pdec_def)
  have l1: "L1 \<in> answer Pdec" using answer_closed[of "{C1}" L1 Pdec] c1 by (auto simp: Pdec_def)
  show ?thesis using answer_closed[of "{L0, L1}" Dec Pdec] l0 l1 by (auto simp: Pdec_def)
qed

lemma Aux_dropped: "Aux \<notin> lfp (restrict_op (Tp Pdec) Ddec)"
  using decode_magic_sets_lossless by (simp add: Ddec_def)

section \<open>Decode robustness: how far a clause weight may drift (the margin certificate)\<close>

text \<open>The other half of the language's metatheory: a bounded perturbation of the logits preserves the
  query answer on every token whose margin exceeds @{text "2\<delta>"}. The bound is tight (a margin-@{text "2\<delta>"}
  token can be tied), and it is exactly the LP statement "how far a clause weight may drift before
  @{term decode} flips" -- the decision-side companion to demand-closure. (= ProvableOpt_Common PO-T3,
  self-contained.)\<close>

definition decodes_to :: "('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "decodes_to L V t \<longleftrightarrow> t \<in> V \<and> (\<forall>v\<in>V. v \<noteq> t \<longrightarrow> L v < L t)"

theorem decode_margin_certified:
  assumes pert: "\<And>v. v \<in> V \<Longrightarrow> \<bar>L' v - L v\<bar> \<le> \<delta>"
      and tV:   "t \<in> V"
      and marg: "\<And>v. v \<in> V \<Longrightarrow> v \<noteq> t \<Longrightarrow> L t - L v > 2 * \<delta>"
  shows "decodes_to L' V t"
  unfolding decodes_to_def
proof (intro conjI ballI impI)
  show "t \<in> V" by (rule tV)
next
  fix v assume v: "v \<in> V" and ne: "v \<noteq> t"
  have b1: "L' t - L t \<le> \<delta> \<and> - \<delta> \<le> L' t - L t" using pert[OF tV] by (simp add: abs_le_iff)
  have b2: "L' v - L v \<le> \<delta> \<and> - \<delta> \<le> L' v - L v" using pert[OF v] by (simp add: abs_le_iff)
  have b3: "L t - L v > 2 * \<delta>" by (rule marg[OF v ne])
  from b1 b2 b3 show "L' v < L' t" by linarith
qed

end
