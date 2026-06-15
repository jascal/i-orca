theory Density
  imports Complex_Main
begin

text \<open>The activation -> density bridge: the one new definition the density story needs.
  a x j = activation magnitude of source j on input/token x; \<theta> = firing threshold.
  This is the layer the static margin model lacks (margin c says nothing about which
  sources fire on a given input).\<close>

definition fires :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "fires a \<theta> x j \<longleftrightarrow> \<theta> < a x j"

definition active_on :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set" where
  "active_on a \<theta> x P = {j\<in>P. fires a \<theta> x j}"

definition density_on :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> real" where
  "density_on a \<theta> x P = real (card (active_on a \<theta> x P)) / real (card P)"

definition avg_density :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> real" where
  "avg_density a \<theta> Es P = (\<Sum>x\<in>Es. density_on a \<theta> x P) / real (card Es)"

text \<open>Rigorous backing of "each replacement reduces (or preserves) the sources
  involved": the COUNT of firing sources is monotone under shrinking the coalition.\<close>

lemma active_count_mono:
  assumes PQ: "P \<subseteq> Q" and finQ: "finite Q"
  shows "card (active_on a \<theta> x P) \<le> card (active_on a \<theta> x Q)"
proof -
  have sub: "active_on a \<theta> x P \<subseteq> active_on a \<theta> x Q" using PQ by (auto simp: active_on_def)
  have fin: "finite (active_on a \<theta> x Q)" using finQ by (simp add: active_on_def)
  show ?thesis by (rule card_mono[OF fin sub])
qed

text \<open>Hence the total firing count over a finite sample only drops when you shrink
  the coalition (the monotone objective the decomposition descends).\<close>

lemma total_firing_mono:
  assumes PQ: "P \<subseteq> Q" and finQ: "finite Q"
  shows "(\<Sum>x\<in>Es. card (active_on a \<theta> x P)) \<le> (\<Sum>x\<in>Es. card (active_on a \<theta> x Q))"
  by (intro sum_mono active_count_mono[OF PQ finQ])

text \<open>NOTE the subtlety the fraction hides: density_on is a RATIO (firing / card P),
  which is NOT monotone under subsets. So "minimise density" must mean either the
  total firing count above, or density at fixed coalition size; a smaller deciding
  sub-coalition lowers the *count*, not automatically the *fraction*. The objective
  to minimise over deciding coalitions is therefore total/average firing count, with
  the irreducible atoms as the floor (a minimal deciding coalition exists iff the
  current one is reducible).\<close>

end
