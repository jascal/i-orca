theory Density_Minimization
  imports Hardness Density
begin

text \<open>Top-down decomposition, the framing the kernel forced: repeatedly replace a
  REDUCIBLE deciding coalition by a strictly smaller deciding sub-coalition, bottoming
  out at irreducible ATOMS (you never split an irreducible coalition). This is the
  CORRECTED, kernel-checked version of the Density_Minimization draft, which did not
  type-check (imports Main while using real; undefined `irreducible`;
  `active_sources = {j. ...}` ranges over ALL naturals so its card is 0 and the
  density is identically 0; the per-input argument unused; the monotonicity lemma
  applies the density to a coalition argument it does not take). Here density is the
  coalition-restricted firing COUNT from Density.thy (the monotone objective; the
  ratio `density_on` is NOT monotone under subsets, so it is the wrong objective).\<close>

inductive decomposes ::
  "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> bool"
  for c :: "nat \<Rightarrow> nat \<Rightarrow> real" and t :: nat and V :: "nat set" where
  base: "irreducible c S V t \<Longrightarrow> decomposes c t V S S"
| step: "\<lbrakk> P \<subset> S; P \<noteq> {}; decides c P V t; decomposes c t V P A \<rbrakk>
          \<Longrightarrow> decomposes c t V S A"

text \<open>Soundness: the result is an irreducible atom, a subset of S, still deciding t.\<close>

lemma decomposes_atom:
  assumes "decomposes c t V S A" shows "irreducible c A V t"
  using assms by (induct rule: decomposes.induct) auto

lemma decomposes_subset:
  assumes "decomposes c t V S A" shows "A \<subseteq> S"
  using assms by (induct rule: decomposes.induct) (auto dest: psubset_imp_subset)

lemma decomposes_decides:
  assumes "decomposes c t V S A" shows "decides c A V t"
  using decomposes_atom[OF assms] by (simp add: irreducible_def)

text \<open>Density is non-increasing along the decomposition: each step passes to a
  sub-coalition, and the firing COUNT is monotone (Density.total_firing_mono).\<close>

lemma decomposes_firing_non_increasing:
  assumes "decomposes c t V S A" and "finite S"
  shows "(\<Sum>x\<in>Es. card (active_on a \<theta> x A)) \<le> (\<Sum>x\<in>Es. card (active_on a \<theta> x S))"
  using decomposes_subset[OF assms(1)] assms(2) by (rule total_firing_mono)

end
