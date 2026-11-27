theory Node_Mask_Clamp
  imports Main
begin

section \<open>A layered model with interventions on nodes\<close>

text \<open>Nodes are evaluated in a fixed order. A node reads the environment of earlier nodes' outputs
and either computes its value or is overridden by an intervention. A clamp is an intervention that
fixes a set of nodes to constants, and a swap writes node values taken from a run on another input.\<close>

type_synonym ('x, 'n, 'v) mechanisms = "'n \<Rightarrow> 'x \<Rightarrow> ('n \<Rightarrow> 'v) \<Rightarrow> 'v"

definition step :: "('x, 'n, 'v) mechanisms \<Rightarrow> 'x \<Rightarrow> ('n \<Rightarrow> 'v option) \<Rightarrow> 'n \<Rightarrow> ('n \<Rightarrow> 'v) \<Rightarrow> ('n \<Rightarrow> 'v)" where
  "step mech x ov n env = env(n := (case ov n of Some v \<Rightarrow> v | None \<Rightarrow> mech n x env))"

definition run_env :: "('x, 'n, 'v) mechanisms \<Rightarrow> 'n list \<Rightarrow> 'v \<Rightarrow> 'x \<Rightarrow> ('n \<Rightarrow> 'v option) \<Rightarrow> ('n \<Rightarrow> 'v)" where
  "run_env mech order d x ov = fold (step mech x ov) order (\<lambda>_. d)"

definition eval :: "('x, 'n, 'v) mechanisms \<Rightarrow> 'n list \<Rightarrow> (('n \<Rightarrow> 'v) \<Rightarrow> 'y) \<Rightarrow> 'v \<Rightarrow> 'x \<Rightarrow> ('n \<Rightarrow> 'v option) \<Rightarrow> 'y" where
  "eval mech order rd d x ov = rd (run_env mech order d x ov)"

definition clamp_ov :: "'n set \<Rightarrow> ('n \<Rightarrow> 'v) \<Rightarrow> ('n \<Rightarrow> 'v option) \<Rightarrow> ('n \<Rightarrow> 'v option)" where
  "clamp_ov C \<mu> ov n = (if n \<in> C then Some (\<mu> n) else ov n)"

definition nodeval :: "('x, 'n, 'v) mechanisms \<Rightarrow> 'n list \<Rightarrow> 'v \<Rightarrow> 'x \<Rightarrow> ('n \<Rightarrow> 'v option) \<Rightarrow> 'n \<Rightarrow> 'v" where
  "nodeval mech order d x ov n = run_env mech order d x ov n"

definition swap_ov :: "('x, 'n, 'v) mechanisms \<Rightarrow> 'n list \<Rightarrow> 'v \<Rightarrow> 'n set \<Rightarrow> 'x \<Rightarrow> ('n \<Rightarrow> 'v option) \<Rightarrow> ('n \<Rightarrow> 'v option)" where
  "swap_ov mech order d S b ov n = (if n \<in> S then Some (nodeval mech order d b ov n) else ov n)"

subsection \<open>Facts about evaluation\<close>

lemma fold_step_irrelevant:
  assumes "\<And>n. n \<in> set order \<Longrightarrow> ov n = None \<Longrightarrow> mech1 n = mech2 n"
  shows "fold (step mech1 x ov) order env = fold (step mech2 x ov) order env"
  using assms
proof (induct order arbitrary: env)
  case Nil show ?case by simp
next
  case (Cons n ns)
  have s: "step mech1 x ov n env = step mech2 x ov n env"
    using Cons.prems unfolding step_def by (cases "ov n") auto
  have ih: "\<And>e. fold (step mech1 x ov) ns e = fold (step mech2 x ov) ns e"
    by (rule Cons.hyps) (use Cons.prems in auto)
  show ?case using s ih by simp
qed

lemma fold_step_untouched:
  assumes "n \<notin> set xs"
  shows "fold (step mech x ov) xs env n = env n"
  using assms by (induct xs arbitrary: env) (auto simp: step_def)

lemma fold_step_overridden:
  assumes ov: "ov n = Some v" and mem: "n \<in> set xs"
  shows "fold (step mech x ov) xs env n = v"
  using mem
proof (induct xs arbitrary: env)
  case Nil then show ?case by simp
next
  case (Cons m ms)
  show ?case
  proof (cases "n \<in> set ms")
    case True then show ?thesis by (simp add: Cons.hyps)
  next
    case False
    with Cons.prems have nm: "n = m" by auto
    have "fold (step mech x ov) ms (step mech x ov m env) n = step mech x ov m env n"
      using False by (rule fold_step_untouched)
    also have "... = v" using nm ov unfolding step_def by simp
    finally show ?thesis by simp
  qed
qed

subsection \<open>Clamp and mask\<close>

text \<open>C1. If a set C of nodes is clamped to constants, the model's output does not depend on the
internal computation of any clamped node.\<close>

theorem clamped_nodes_irrelevant:
  assumes "\<And>n. n \<in> set order \<Longrightarrow> n \<notin> C \<Longrightarrow> mech1 n = mech2 n"
  shows "eval mech1 order rd d x (clamp_ov C \<mu> ov0) = eval mech2 order rd d x (clamp_ov C \<mu> ov0)"
proof -
  have "fold (step mech1 x (clamp_ov C \<mu> ov0)) order (\<lambda>_. d)
      = fold (step mech2 x (clamp_ov C \<mu> ov0)) order (\<lambda>_. d)"
  proof (rule fold_step_irrelevant)
    fix n assume "n \<in> set order" and "clamp_ov C \<mu> ov0 n = None"
    then have "n \<notin> C" unfolding clamp_ov_def by (auto split: if_splits)
    with \<open>n \<in> set order\<close> show "mech1 n = mech2 n" by (rule assms)
  qed
  then show ?thesis unfolding eval_def run_env_def by simp
qed

text \<open>C2. Swapping a clamped node is a no-op, so such a node's interchange score is null by
construction: its value on every input is the clamp constant.\<close>

lemma nodeval_clamped:
  assumes "n \<in> C" and "n \<in> set order"
  shows "nodeval mech order d x (clamp_ov C \<mu> ov0) n = \<mu> n"
  using assms unfolding nodeval_def run_env_def clamp_ov_def
  by (intro fold_step_overridden) auto

theorem clamped_swap_noop:
  assumes sC: "S \<subseteq> C" and sO: "S \<subseteq> set order"
  shows "eval mech order rd d a (swap_ov mech order d S b (clamp_ov C \<mu> ov0))
       = eval mech order rd d a (clamp_ov C \<mu> ov0)"
proof -
  have "swap_ov mech order d S b (clamp_ov C \<mu> ov0) = clamp_ov C \<mu> ov0"
  proof (rule ext)
    fix n show "swap_ov mech order d S b (clamp_ov C \<mu> ov0) n = clamp_ov C \<mu> ov0 n"
    proof (cases "n \<in> S")
      case True
      with sC sO have "n \<in> C" "n \<in> set order" by auto
      then show ?thesis using True nodeval_clamped[of n C order mech d b \<mu> ov0]
        unfolding swap_ov_def clamp_ov_def by simp
    next
      case False then show ?thesis unfolding swap_ov_def by simp
    qed
  qed
  then show ?thesis by simp
qed

text \<open>C3. The cost of clamping, as a counting bound. If a student f agrees with a clamped host g
on a set A of inputs, and the clamped host g differs from the host h on at most e inputs, then
the student agrees with the host on at least |A| - e inputs. With e = 0 the clamp is lossless.\<close>

theorem clamp_cost_bound:
  assumes "finite D"
  shows "card {x \<in> D. f x = g x} - card {x \<in> D. g x \<noteq> h x} \<le> card {x \<in> D. f x = h x}"
proof -
  have sub: "{x \<in> D. f x = g x} \<subseteq> {x \<in> D. f x = h x} \<union> {x \<in> D. g x \<noteq> h x}" by auto
  have fin: "finite ({x \<in> D. f x = h x} \<union> {x \<in> D. g x \<noteq> h x})" using assms by simp
  have "card {x \<in> D. f x = g x} \<le> card ({x \<in> D. f x = h x} \<union> {x \<in> D. g x \<noteq> h x})"
    by (rule card_mono[OF fin sub])
  also have "... \<le> card {x \<in> D. f x = h x} + card {x \<in> D. g x \<noteq> h x}" by (rule card_Un_le)
  finally show ?thesis by arith
qed

subsection \<open>Single-node inertness does not imply joint inertness\<close>

text \<open>C4. Two duplicate nodes each copy the input, and the output is true if either is true.
Ablating either node alone (to the constant False) changes nothing; ablating both changes the
output on input True. This is why a single-node screen can clamp both members of a redundant
pair, and why a pair screen exists.\<close>

definition dup_mech :: "(bool, bool, bool) mechanisms" where
  "dup_mech n x env = x"

definition dup_readout :: "(bool \<Rightarrow> bool) \<Rightarrow> bool" where
  "dup_readout env = (env False \<or> env True)"

definition ablate :: "bool set \<Rightarrow> bool \<Rightarrow> bool option" where
  "ablate C n = (if n \<in> C then Some False else None)"

abbreviation dup_eval :: "bool \<Rightarrow> (bool \<Rightarrow> bool option) \<Rightarrow> bool" where
  "dup_eval x ov \<equiv> eval dup_mech [False, True] dup_readout False x ov"

theorem single_inert_joint_not:
  shows "\<forall>x. dup_eval x (ablate {False}) = dup_eval x (\<lambda>_. None)"
    and "\<forall>x. dup_eval x (ablate {True}) = dup_eval x (\<lambda>_. None)"
    and "\<not> (\<forall>x. dup_eval x (ablate {False, True}) = dup_eval x (\<lambda>_. None))"
proof -
  show "\<forall>x. dup_eval x (ablate {False}) = dup_eval x (\<lambda>_. None)"
    by (auto simp: eval_def run_env_def step_def dup_mech_def dup_readout_def ablate_def)
  show "\<forall>x. dup_eval x (ablate {True}) = dup_eval x (\<lambda>_. None)"
    by (auto simp: eval_def run_env_def step_def dup_mech_def dup_readout_def ablate_def)
  show "\<not> (\<forall>x. dup_eval x (ablate {False, True}) = dup_eval x (\<lambda>_. None))"
    by (auto simp: eval_def run_env_def step_def dup_mech_def dup_readout_def ablate_def)
qed

end
