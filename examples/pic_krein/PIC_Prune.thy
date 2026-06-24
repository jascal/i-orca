(*
  PIC_Prune.thy -- the source-side (generator) PRUNING certificate: dropping sources whose summed
  incidence stays under half the margin preserves the decode, exactly and certified.  The companion of
  PIC_Quant's quantization certificate; same margin certificate underneath, different perturbation bound.

  PIC logit from a source set S:  L_S v = (SUM_{j in S} c j v) + b v,  c j v = <d_j, U_v> the incidence.
  Pruning P (subset of S):  L_{S-P} = L_S - SUM_{j in P} c j v.  So the perturbation is exactly the
  DROPPED incidence SUM_{j in P} c j v.  Hence:

    prune_logit_delta            : the perturbation of pruning P equals the dropped incidence.
    prune_dropped_le_budget      : triangle bound -- |dropped| <= SUM_{j in P} beta_j, beta_j a per-source
                                   incidence bound (beta_j = sup_v |c j v|).  The greedy "budget".
    prune_budget_mono            : the budget SUM_{j in P} beta_j is monotone in P (beta >= 0), so the
                                   certifiable prune sets are downward-closed -- greedy is well-founded.
    prune_decode_preserved       : if |dropped| <= delta for all v and margin > 2*delta, decode preserved.
    prune_budget_decode_preserved: budget form -- if 2 * SUM_{j in P} beta_j < margin, decode preserved.

  These are value-system- and metric-agnostic (about scalar incidences), so they cover float / int /
  ternary and PIC / Krein alike.  The CERTIFICATE is method-agnostic (it is PIC_Quant.margin_certified);
  pruning, quantization, and rewriting can be MIXED under one budget by the triangle inequality
  (|dropped| + |quant drift| + ... <= total delta; certify 2*total < margin).  See PRUNE.md for the
  certificate-gated pruning algorithms with provable within-tolerance outcomes.

  Tag: all [proved] here.  Honest scope: local / per-input (delta and margin depend on the residual r and
  the candidate set V at that input; a global guarantee needs sup over the input distribution); the cert
  is argmax-lossless, not softmax-lossless (PIC_Quant / PIC_SPEC sec 5.5).
*)
theory PIC_Prune
  imports PIC_Quant
begin

text \<open>Pruning a source set P (subset of S) perturbs the logit by exactly the DROPPED incidence.\<close>
lemma prune_logit_delta:
  fixes c :: "'j \<Rightarrow> 'v \<Rightarrow> real"
  assumes finS: "finite S" and PS: "P \<subseteq> S"
  shows "((\<Sum>j\<in>S. c j v) + b v) - ((\<Sum>j\<in>S-P. c j v) + b v) = (\<Sum>j\<in>P. c j v)"
  by (simp add: sum.subset_diff[OF PS finS])

text \<open>Triangle budget: the dropped incidence is bounded by the sum of per-source bounds beta_j.\<close>
lemma prune_dropped_le_budget:
  fixes c :: "'j \<Rightarrow> 'v \<Rightarrow> real" and \<beta> :: "'j \<Rightarrow> real"
  assumes bnd: "\<And>j. j \<in> P \<Longrightarrow> \<bar>c j v\<bar> \<le> \<beta> j"
  shows "\<bar>\<Sum>j\<in>P. c j v\<bar> \<le> (\<Sum>j\<in>P. \<beta> j)"
proof -
  have "\<bar>\<Sum>j\<in>P. c j v\<bar> \<le> (\<Sum>j\<in>P. \<bar>c j v\<bar>)" by (rule sum_abs)
  also have "\<dots> \<le> (\<Sum>j\<in>P. \<beta> j)" using bnd by (intro sum_mono) blast
  finally show ?thesis .
qed

text \<open>The budget is monotone in P (for non-negative beta): pruning fewer sources costs no more, so the
  certifiable prune sets are downward-closed -- a greedy prune is well-founded.\<close>
lemma prune_budget_mono:
  fixes \<beta> :: "'j \<Rightarrow> real"
  assumes finP: "finite P" and PP: "Q \<subseteq> P" and nn: "\<And>j. j \<in> P \<Longrightarrow> 0 \<le> \<beta> j"
  shows "(\<Sum>j\<in>Q. \<beta> j) \<le> (\<Sum>j\<in>P. \<beta> j)"
  using finP PP nn by (intro sum_mono2) auto

text \<open>THE PRUNING CERTIFICATE.  Drop the sources in P (subset of S).  If for every candidate the dropped
  incidence is <= delta and the original margin exceeds 2*delta, the pruned decode equals the original --
  exactly, and certified.  (Source-side twin of PIC_Quant.quant_decode_preserved.)\<close>
theorem prune_decode_preserved:
  fixes c :: "'j \<Rightarrow> 'v \<Rightarrow> real" and b :: "'v \<Rightarrow> real"
  assumes finS:   "finite S" and PS: "P \<subseteq> S" and tV: "t \<in> V"
      and margin: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> ((\<Sum>j\<in>S. c j v) + b v) + m \<le> ((\<Sum>j\<in>S. c j t) + b t)"
      and dropped:"\<forall>v\<in>V. \<bar>\<Sum>j\<in>P. c j v\<bar> \<le> \<delta>"
      and gap:    "2 * \<delta> < m"
  shows "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> ((\<Sum>j\<in>S-P. c j v) + b v) < ((\<Sum>j\<in>S-P. c j t) + b t)"
proof -
  have pert: "\<forall>v\<in>V. \<bar>((\<Sum>j\<in>S-P. c j v) + b v) - ((\<Sum>j\<in>S. c j v) + b v)\<bar> \<le> \<delta>"
  proof (intro ballI)
    fix v assume vV: "v \<in> V"
    have "((\<Sum>j\<in>S-P. c j v) + b v) - ((\<Sum>j\<in>S. c j v) + b v) = - (\<Sum>j\<in>P. c j v)"
      by (simp add: sum.subset_diff[OF PS finS])
    thus "\<bar>((\<Sum>j\<in>S-P. c j v) + b v) - ((\<Sum>j\<in>S. c j v) + b v)\<bar> \<le> \<delta>"
      using dropped vV by simp
  qed
  show ?thesis by (rule margin_certified[OF margin pert tV gap])
qed

text \<open>BUDGET FORM (what the greedy algorithm uses): if 2 * SUM_{j in P} beta_j < margin and each source
  obeys |c j v| <= beta_j on V, pruning P preserves the decode.\<close>
theorem prune_budget_decode_preserved:
  fixes c :: "'j \<Rightarrow> 'v \<Rightarrow> real" and b :: "'v \<Rightarrow> real" and \<beta> :: "'j \<Rightarrow> real"
  assumes finS: "finite S" and PS: "P \<subseteq> S" and tV: "t \<in> V"
      and margin: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> ((\<Sum>j\<in>S. c j v) + b v) + m \<le> ((\<Sum>j\<in>S. c j t) + b t)"
      and bnd: "\<And>j v. j \<in> P \<Longrightarrow> v \<in> V \<Longrightarrow> \<bar>c j v\<bar> \<le> \<beta> j"
      and gap: "2 * (\<Sum>j\<in>P. \<beta> j) < m"
  shows "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> ((\<Sum>j\<in>S-P. c j v) + b v) < ((\<Sum>j\<in>S-P. c j t) + b t)"
proof -
  have dropped: "\<forall>v\<in>V. \<bar>\<Sum>j\<in>P. c j v\<bar> \<le> (\<Sum>j\<in>P. \<beta> j)"
  proof (intro ballI)
    fix v assume vV: "v \<in> V"
    show "\<bar>\<Sum>j\<in>P. c j v\<bar> \<le> (\<Sum>j\<in>P. \<beta> j)"
      by (rule prune_dropped_le_budget) (use bnd vV in blast)
  qed
  show ?thesis by (rule prune_decode_preserved[OF finS PS tV margin dropped gap])
qed

end
