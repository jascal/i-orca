(*
  GumbelSelect.thy -- the selection rule of Aaronson's LLM watermark.

  Canonical scheme (S. Aaronson, UT Austin / OpenAI, 2022-2023). At each step the
  model emits a probability vector p over the vocabulary V (p i > 0, sum 1). A secret
  key drives a pseudorandom function on the recent context, producing one uniform
  value r i in (0,1) for every token i. Instead of sampling from p, the watermark
  EMITS the token that maximises

        gscore (r i) (p i)  =  (r i) powr (1 / p i).

  Taking logs, this is the "exponential race": maximising (r i) powr (1/p i) is the
  same as MINIMISING erace (r i) (p i) = - ln (r i) / p i. Since - ln (r i) is an
  Exp(1) variate when r i ~ U(0,1), and - ln(r i)/p i ~ Exp(p i), the winner is the
  argmin of independent exponentials -- the classical competing-exponentials race
  that selects token k with probability p k (the distortion-free property proved in
  Unbiased.thy).

  This theory establishes the *deterministic* skeleton of the rule:
    gumbel_mono        : the max-of-powr ordering and the min-of-erace ordering agree
    selects_iff_erace  : the argmax selection equals the exponential-race argmin
    selects_unique     : the winner is unique -- selection is a deterministic function
                         of (key-derived r, p); the keyed detector reproduces it
    gscore_le_iff      : the per-coordinate pushforward CDF, P[gscore <= y] = y powr p
                         (the building block of the unbiasedness computation)
*)

theory GumbelSelect
  imports "HOL-Analysis.Analysis"
begin

type_synonym token = nat

text \<open>The quantity the watermark maximises, and its log-domain (exponential-race)
  counterpart that the same rule minimises.\<close>

definition gscore :: "real \<Rightarrow> real \<Rightarrow> real" where
  "gscore r p = r powr (1 / p)"

definition erace :: "real \<Rightarrow> real \<Rightarrow> real" where
  "erace r p = - ln r / p"

text \<open>Gumbel-max trick. For positive PRF values and probabilities, token 2 beats
  token 1 in the maximised score exactly when it has the smaller exponential-race
  statistic. So @{term gscore}-argmax and @{term erace}-argmin coincide.\<close>

lemma gumbel_mono:
  fixes r1 r2 p1 p2 :: real
  assumes "0 < r1" "0 < r2" "0 < p1" "0 < p2"
  shows "gscore r1 p1 < gscore r2 p2 \<longleftrightarrow> erace r2 p2 < erace r1 p1"
proof -
  have n1: "r1 \<noteq> 0" using assms(1) by simp
  have n2: "r2 \<noteq> 0" using assms(2) by simp
  have "gscore r1 p1 = exp ((1/p1) * ln r1)" using n1 by (simp add: gscore_def powr_def)
  moreover have "gscore r2 p2 = exp ((1/p2) * ln r2)" using n2 by (simp add: gscore_def powr_def)
  ultimately have "gscore r1 p1 < gscore r2 p2 \<longleftrightarrow> ln r1 / p1 < ln r2 / p2"
    by (simp add: mult.commute)
  thus ?thesis by (simp add: erace_def)
qed

text \<open>Strict-argmax selection: token @{term k} is emitted iff it strictly dominates
  every other candidate in the watermark score.\<close>

definition selects :: "token set \<Rightarrow> (token \<Rightarrow> real) \<Rightarrow> (token \<Rightarrow> real) \<Rightarrow> token \<Rightarrow> bool" where
  "selects V r p k \<longleftrightarrow> (\<forall>i\<in>V. i \<noteq> k \<longrightarrow> gscore (r i) (p i) < gscore (r k) (p k))"

definition erace_selects :: "token set \<Rightarrow> (token \<Rightarrow> real) \<Rightarrow> (token \<Rightarrow> real) \<Rightarrow> token \<Rightarrow> bool" where
  "erace_selects V r p k \<longleftrightarrow> (\<forall>i\<in>V. i \<noteq> k \<longrightarrow> erace (r k) (p k) < erace (r i) (p i))"

text \<open>The watermark's argmax rule is exactly the exponential-race argmin rule.\<close>

lemma selects_iff_erace:
  assumes "\<forall>i\<in>V. 0 < r i" "\<forall>i\<in>V. 0 < p i" "k \<in> V"
  shows "selects V r p k \<longleftrightarrow> erace_selects V r p k"
proof -
  have "(gscore (r i) (p i) < gscore (r k) (p k))
          = (erace (r k) (p k) < erace (r i) (p i))"
    if "i \<in> V" for i
    using gumbel_mono[of "r i" "r k" "p i" "p k"] assms that by auto
  thus ?thesis by (auto simp: selects_def erace_selects_def)
qed

text \<open>Determinism / reproducibility. Distinct scores cannot both be the maximum, so
  the emitted token is unique -- a deterministic function of the key-derived @{term r}
  and the model's @{term p}. The keyed detector, recomputing the same @{term r} from
  the same context, recovers the same winner.\<close>

lemma selects_unique:
  assumes "selects V r p k" "selects V r p l" "k \<in> V" "l \<in> V"
  shows "k = l"
proof (rule ccontr)
  assume kl: "k \<noteq> l"
  have "gscore (r l) (p l) < gscore (r k) (p k)"
    using assms(1) assms(4) kl by (auto simp: selects_def)
  moreover have "gscore (r k) (p k) < gscore (r l) (p l)"
    using assms(2) assms(3) kl by (auto simp: selects_def)
  ultimately show False by simp
qed

text \<open>Per-coordinate pushforward. Pushing a uniform r through \<open>\<lambda>r. gscore r p\<close>
  gives, for a threshold y in (0,1), the event \<open>r \<le> y powr p\<close>; under a uniform r
  that event has probability \<open>y powr p\<close>. This is the CDF the unbiasedness integral
  multiplies out. We prove the underlying order isomorphism: raising to the power p
  (resp. 1/p) is monotone and inverts the watermark map on the positives.\<close>

lemma gscore_le_iff:
  fixes r y p :: real
  assumes "0 < r" "0 < y" "0 < p"
  shows "gscore r p \<le> y \<longleftrightarrow> r \<le> y powr p"
proof -
  have pnz: "p \<noteq> 0" using assms(3) by simp
  have pnn: "0 \<le> p" using assms(3) by (rule less_imp_le)
  have rnn: "0 \<le> r" using assms(1) by (rule less_imp_le)
  have ipnn: "0 \<le> 1/p" using assms(3) by simp
  have A: "(r powr (1/p) \<le> y) = (r \<le> y powr p)"
  proof
    assume hle: "r powr (1/p) \<le> y"
    have "(r powr (1/p)) powr p \<le> y powr p"
      by (rule powr_mono2[OF pnn _ hle]) simp
    moreover have "(r powr (1/p)) powr p = r"
      using rnn pnz by (simp add: powr_powr)
    ultimately show "r \<le> y powr p" by simp
  next
    assume hle: "r \<le> y powr p"
    have "r powr (1/p) \<le> (y powr p) powr (1/p)"
      by (rule powr_mono2[OF ipnn rnn hle])
    moreover have "(y powr p) powr (1/p) = y"
      using assms(2) pnz by (simp add: powr_powr)
    ultimately show "r powr (1/p) \<le> y" by simp
  qed
  show ?thesis using A by (simp add: gscore_def)
qed

end
