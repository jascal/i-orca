(*
  Equivalence.thy -- when do two engines compute the same thing?

  The question s-orca's `portable:` property asks, made precise. A pipeline is a
  list of operators; an ENGINE is the record of choices where two implementations
  may legitimately differ. The headline result is a congruence:

      compatible E1 E2 ps  ==>  run E1 ps xs = run E2 ps xs

  so per-OPERATOR agreement is enough for whole-PIPELINE agreement. That is what
  licenses s-orca checking portability construct by construct instead of reasoning
  about pipelines as wholes.

  The per-operator side conditions then split three ways, and the split is the
  useful part:

    UNCONDITIONAL   stateless_op_agrees -- filter and project are per-record maps
                      and cannot differ between engines. No side condition.

    DISCHARGEABLE   window_assignment_unique -- any epoch-aligned tumbling window
                      of width w containing t IS win_lo w t. Two engines that both
                      use epoch-aligned tumbling windows therefore cannot disagree
                      about which window an event belongs to. A strong assumption
                      ("same assignment") is reduced to a weak checkable one
                      ("both epoch-aligned").

    IRREDUCIBLE     dedup_horizons_differ_witness -- deduplication with an
                      unbounded key memory and deduplication with a bounded one
                      DEMONSTRABLY differ, and the witness is two records with the
                      same key far apart in event time. No condition on the
                      pipeline can reconcile them; only an assumption about the
                      DATA can (dedup_agree_on_clustered).

  That third case is why s-orca reports PORTABILITY_DEDUP_SEMANTICS as a warning
  requiring a human decision rather than an error the verifier can clear: the
  formalisation says there is nothing for the verifier to check. Likewise
  output_mode_is_semantic shows append and update are different functions, not
  different renderings, which is why an output-mode mismatch is an error.

  Scope, as in EventTime.thy: this is a statement about the model. Whether Flink
  and Spark instantiate `engine` the way the portability matrix says they do is an
  empirical claim tagged `documented`, never proved.
*)

theory Equivalence
  imports EventTime
begin

section \<open>Records, operators and engines\<close>

text \<open>A record is an event time paired with a key. Payload beyond the key plays
  no part in any of the distinctions below, so it is omitted.\<close>

type_synonym erec = "nat \<times> nat"

text \<open>An operator. @{term "Dedup w"} carries the DECLARED bound; how that bound is
  honoured is the engine's choice, which is exactly where the two disagree.\<close>

datatype eop =
    Filter "nat \<Rightarrow> bool"
  | Project "nat \<Rightarrow> nat"
  | Dedup nat

text \<open>An engine is the record of choices an implementation makes. Here the only
  such choice is the key-memory horizon used for deduplication: @{term None} is an
  unbounded memory, @{term "Some d"} forgets a key once event time has advanced
  @{term d} past it.\<close>

record engine =
  ded_horizon :: "nat \<Rightarrow> nat option"

section \<open>Deduplication under a horizon\<close>

definition seen_h :: "nat option \<Rightarrow> erec list \<Rightarrow> nat \<Rightarrow> bool" where
  "seen_h h xs i \<longleftrightarrow>
     (\<exists>j<i. snd (xs ! j) = snd (xs ! i) \<and>
            (case h of None \<Rightarrow> True | Some d \<Rightarrow> fst (xs ! i) \<le> fst (xs ! j) + d))"

definition dedup_list :: "nat option \<Rightarrow> erec list \<Rightarrow> erec list" where
  "dedup_list h xs = [xs ! i. i \<leftarrow> [0..<length xs], \<not> seen_h h xs i]"

definition kept :: "nat option \<Rightarrow> erec list \<Rightarrow> nat set" where
  "kept h xs = {i. i < length xs \<and> \<not> seen_h h xs i}"

text \<open>A bounded horizon suppresses no more than an unbounded one: whatever the
  unbounded memory keeps, the bounded memory keeps too. Operationally, the engine
  with the bounded memory may emit duplicates the other one removes.\<close>

theorem dedup_bounded_keeps_superset:
  "kept None xs \<subseteq> kept (Some d) xs"
proof
  fix i assume "i \<in> kept None xs"
  then have i: "i < length xs" and ns: "\<not> seen_h None xs i"
    by (simp_all add: kept_def)
  have "\<not> seen_h (Some d) xs i"
  proof
    assume "seen_h (Some d) xs i"
    then obtain j where "j < i" and "snd (xs ! j) = snd (xs ! i)"
      by (auto simp: seen_h_def)
    then have "seen_h None xs i" by (auto simp: seen_h_def)
    with ns show False ..
  qed
  with i show "i \<in> kept (Some d) xs" by (simp add: kept_def)
qed

text \<open>The two agree when every repeat of a key falls inside the horizon. This is a
  property of the DATA, not of the pipeline.\<close>

definition clustered :: "nat \<Rightarrow> erec list \<Rightarrow> bool" where
  "clustered d xs \<longleftrightarrow>
     (\<forall>i<length xs. \<forall>j<i. snd (xs ! j) = snd (xs ! i) \<longrightarrow> fst (xs ! i) \<le> fst (xs ! j) + d)"

theorem dedup_agree_on_clustered:
  assumes "clustered d xs"
  shows "dedup_list None xs = dedup_list (Some d) xs"
proof -
  have eq: "seen_h None xs i = seen_h (Some d) xs i" if i: "i < length xs" for i
  proof
    assume "seen_h None xs i"
    then obtain j where j: "j < i" and k: "snd (xs ! j) = snd (xs ! i)"
      by (auto simp: seen_h_def)
    from assms i j k have "fst (xs ! i) \<le> fst (xs ! j) + d"
      by (simp add: clustered_def)
    with j k show "seen_h (Some d) xs i" by (auto simp: seen_h_def)
  next
    assume "seen_h (Some d) xs i"
    then show "seen_h None xs i" by (auto simp: seen_h_def)
  qed
  have m: "map (\<lambda>i. if \<not> seen_h None xs i then [xs ! i] else []) [0..<length xs]
         = map (\<lambda>i. if \<not> seen_h (Some d) xs i then [xs ! i] else []) [0..<length xs]"
    by (rule map_cong) (auto simp: eq)
  show ?thesis unfolding dedup_list_def by (rule arg_cong[OF m])
qed

text \<open>But nothing about the PIPELINE can reconcile them. Two records sharing a key
  and separated by more than the horizon are kept by the bounded engine and dropped
  by the unbounded one.\<close>

theorem dedup_horizons_differ_witness:
  "dedup_list None [(0, 7), (100, 7)] \<noteq> dedup_list (Some 10) [(0, 7), (100, 7)]"
proof -
  have a: "dedup_list None [(0, 7), (100, 7)] = [(0, 7)]"
    by (simp add: dedup_list_def seen_h_def)
  have b: "dedup_list (Some 10) [(0, 7), (100, 7)] = [(0, 7), (100, 7)]"
    by (simp add: dedup_list_def seen_h_def)
  from a b show ?thesis by simp
qed

section \<open>Pipelines and engine agreement\<close>

fun sem :: "engine \<Rightarrow> eop \<Rightarrow> erec list \<Rightarrow> erec list" where
  "sem E (Filter p) xs = filter (\<lambda>r. p (snd r)) xs"
| "sem E (Project f) xs = map (\<lambda>r. (fst r, f (snd r))) xs"
| "sem E (Dedup w) xs = dedup_list (ded_horizon E w) xs"

fun run :: "engine \<Rightarrow> eop list \<Rightarrow> erec list \<Rightarrow> erec list" where
  "run E [] xs = xs"
| "run E (p # ps) xs = run E ps (sem E p xs)"

definition op_agrees :: "engine \<Rightarrow> engine \<Rightarrow> eop \<Rightarrow> bool" where
  "op_agrees E1 E2 p \<longleftrightarrow> (\<forall>xs. sem E1 p xs = sem E2 p xs)"

definition compatible :: "engine \<Rightarrow> engine \<Rightarrow> eop list \<Rightarrow> bool" where
  "compatible E1 E2 ps \<longleftrightarrow> (\<forall>p \<in> set ps. op_agrees E1 E2 p)"

text \<open>Stateless operators are per-record maps and cannot differ between engines.
  No side condition, for any pair of engines whatsoever.\<close>

theorem stateless_op_agrees:
  "op_agrees E1 E2 (Filter p)" "op_agrees E1 E2 (Project f)"
  by (simp_all add: op_agrees_def)

text \<open>The congruence. Agreement operator by operator lifts to the whole pipeline,
  which is what licenses checking portability construct by construct.\<close>

theorem compatible_implies_equivalent:
  assumes "compatible E1 E2 ps"
  shows "run E1 ps xs = run E2 ps xs"
  using assms
proof (induction ps arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  from Cons.prems have p: "op_agrees E1 E2 p" and rest: "compatible E1 E2 ps"
    by (simp_all add: compatible_def)
  from p have "sem E1 p xs = sem E2 p xs" by (simp add: op_agrees_def)
  then show ?case using Cons.IH[OF rest] by simp
qed

text \<open>A pipeline built only from stateless operators is portable unconditionally:
  the side-condition list for such a pipeline is empty.\<close>

corollary stateless_pipeline_portable:
  assumes "\<forall>p \<in> set ps. (\<exists>q. p = Filter q) \<or> (\<exists>f. p = Project f)"
  shows "run E1 ps xs = run E2 ps xs"
proof -
  have "compatible E1 E2 ps"
    using assms by (auto simp: compatible_def stateless_op_agrees)
  then show ?thesis by (rule compatible_implies_equivalent)
qed

section \<open>Window assignment is forced, so it is not a place engines can differ\<close>

text \<open>Any epoch-aligned tumbling window of width @{term w} that contains @{term t}
  is @{term "win_lo w t"}. So "the two engines assign events to the same windows",
  which as an assumption would be strong, follows from "both use epoch-aligned
  tumbling windows", which is checkable from documentation.\<close>

theorem window_containment:
  assumes "0 < w"
  shows "win_lo w t \<le> t \<and> t < win_lo w t + w"
  using win_lo_le[OF assms, of t] less_win_hi[OF assms, of t]
  by (simp add: win_hi_def win_lo_def)

theorem window_assignment_unique:
  assumes w:   "0 < w"
      and algn: "b mod w = 0"
      and lo:   "b \<le> t"
      and hi:   "t < b + w"
  shows "b = win_lo w t"
proof -
  from algn have "w dvd b" by auto
  then obtain q where q: "b = q * w" by (metis dvd_def mult.commute)
  from lo q have a: "w * q \<le> t" by (simp add: mult.commute)
  from hi q have b: "t < w * Suc q" by (simp add: mult.commute)
  from a b have "t div w = q" by (rule div_nat_eqI)
  then show ?thesis using q by (simp add: win_lo_def)
qed

section \<open>Output mode is semantic, not cosmetic\<close>

text \<open>An unwindowed aggregate emitted as a changelog and the same aggregate emitted
  once are different functions, not different renderings of one function. This is
  why s-orca treats an output-mode mismatch as an error rather than a warning.\<close>

definition update_out :: "nat list \<Rightarrow> nat list" where
  "update_out xs = map (\<lambda>i. sum_list (take (Suc i) xs)) [0..<length xs]"

definition append_out :: "nat list \<Rightarrow> nat list" where
  "append_out xs = (if xs = [] then [] else [sum_list xs])"

theorem output_mode_is_semantic:
  "update_out [1, 2] \<noteq> append_out [1, 2]"
  by (simp add: update_out_def append_out_def)

end
