(*
  PIC_Quant.thy -- WITHIN-TOLERANCE LOSSLESS compression for ANY PIC system (float / int / ternary),
  via geometry (packing / quantization) + the margin certificate.

  "Within-tolerance lossless" = DECODE-lossless: the argmax (the decoded token) is preserved EXACTLY,
  and certified, even though the frame is quantized (lossy at the bit/weight level).  Only the softmax
  probabilities move within tolerance; the DECISION does not.  This is value-system- AND metric-agnostic
  (it is about the scalar logits), so it covers PIC and Krein-PIC, and float, int, or ternary weights
  alike -- the number system is just the alphabet of the quantization cells; the GEOMETRY sets the rate.

  The design:
    * margin_certified        -- the proved PIC margin certificate (PIC_SPEC sec 5.5), self-contained:
                                 a delta-bounded logit perturbation cannot flip a token whose margin
                                 exceeds 2*delta.
    * frame_quant_logit_bound -- Cauchy-Schwarz: quantizing the frame U -> Ut with ||Ut_v - U_v|| <= eps
                                 perturbs each logit by at most ||r|| * eps.
    * quant_decode_preserved  -- COMPOSE them: quantize the frame to eps-cells (ANY grid -- float round,
                                 int, ternary), and if 2 * rho * eps < margin (rho = ||r|| bound) the
                                 decode is preserved.  THE within-tolerance lossless compression theorem.

  The rate (geometry / packing, [engineering], not formalized here): to place each frame vector within
  eps in a radius-rho ball needs ~ (rho/eps)^d cells = d * log2(rho/eps) bits/vector -- the eps-covering
  number (the packing bound of DecodeCapacity, Cor 5.1).  With eps tied to the margin (eps < margin/(2 rho))
  this is d * log2(2 rho^2 / margin): the COARSER the tolerance the margin allows, the fewer bits.  Small
  margins (the forge-tax / head-tail residue, PIC_SPEC sec 5.4) cost the most bits -- compression is
  heterogeneous, hardest exactly where the decode is least certain.  This BEATS bit-exact lossless because
  it spends bits only down to the margin budget, and unlike ternary_widen_lossless it is genuinely
  compressing (it is not bit-neutral -- it exploits the decode's tolerance).
*)
theory PIC_Quant
  imports "HOL-Analysis.Analysis"
begin

text \<open>THE MARGIN CERTIFICATE (PIC_SPEC sec 5.5), self-contained.  If t beats every competitor by a
  margin >= m, every logit is perturbed by at most delta, and 2*delta < m, then t is still the strict
  winner.  No finiteness needed -- m is the given uniform margin.\<close>
lemma margin_certified:
  fixes L L' :: "'v \<Rightarrow> real"
  assumes win:  "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> L v + m \<le> L t"
      and pert: "\<forall>v\<in>V. \<bar>L' v - L v\<bar> \<le> \<delta>"
      and tV:   "t \<in> V"
      and gap:  "2 * \<delta> < m"
  shows "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> L' v < L' t"
proof (intro ballI impI)
  fix v assume vV: "v \<in> V" and vt: "v \<noteq> t"
  have wv: "L v + m \<le> L t" using win vV vt by blast
  have pv: "\<bar>L' v - L v\<bar> \<le> \<delta>" using pert vV by blast
  have pt: "\<bar>L' t - L t\<bar> \<le> \<delta>" using pert tV by blast
  have a: "L' v - L v \<le> \<bar>L' v - L v\<bar>" by simp
  have b: "L t - L' t \<le> \<bar>L' t - L t\<bar>" by (simp add: abs_minus_commute)
  from a b wv pv pt gap show "L' v < L' t" by linarith
qed

text \<open>QUANTIZATION -> LOGIT PERTURBATION (Cauchy-Schwarz).  Replacing the frame vector U by a quantized
  Ut perturbs the logit inner r U by at most ||r|| * ||Ut - U||.\<close>
lemma frame_quant_logit_bound:
  fixes r U Ut :: "'a::real_inner"
  shows "\<bar>inner r Ut - inner r U\<bar> \<le> norm r * norm (Ut - U)"
proof -
  have up: "inner r (Ut - U) \<le> norm r * norm (Ut - U)" by (rule norm_cauchy_schwarz)
  have dn: "- inner r (Ut - U) \<le> norm r * norm (Ut - U)"
  proof -
    have "inner r (U - Ut) \<le> norm r * norm (U - Ut)" by (rule norm_cauchy_schwarz)
    thus ?thesis by (simp add: inner_diff_right norm_minus_commute)
  qed
  have "inner r Ut - inner r U = inner r (Ut - U)" by (simp add: inner_diff_right)
  thus ?thesis using up dn by (simp add: abs_le_iff)
qed

text \<open>WITHIN-TOLERANCE LOSSLESS COMPRESSION.  Quantize the frame U to Ut with per-token cell size
  ||Ut_v - U_v|| <= eps (ANY grid: float round, int, ternary), with residual ||r|| <= rho.  If the
  original margin exceeds 2*rho*eps, the quantized decode equals the original -- the decision is
  preserved exactly and certified.  Value-system- and metric-agnostic.\<close>
theorem quant_decode_preserved:
  fixes U Ut :: "'v \<Rightarrow> 'a::real_inner" and r :: 'a and b :: "'v \<Rightarrow> real"
  assumes tV:     "t \<in> V"
      and rbound: "norm r \<le> \<rho>" and rho0: "0 \<le> \<rho>"
      and quant:  "\<forall>v\<in>V. norm (Ut v - U v) \<le> \<epsilon>"
      and margin: "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> (inner r (U v) + b v) + m \<le> (inner r (U t) + b t)"
      and tol:    "2 * (\<rho> * \<epsilon>) < m"
  shows "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> (inner r (Ut v) + b v) < (inner r (Ut t) + b t)"
proof -
  have pert: "\<forall>v\<in>V. \<bar>(inner r (Ut v) + b v) - (inner r (U v) + b v)\<bar> \<le> \<rho> * \<epsilon>"
  proof (intro ballI)
    fix v assume vV: "v \<in> V"
    have "\<bar>(inner r (Ut v) + b v) - (inner r (U v) + b v)\<bar> = \<bar>inner r (Ut v) - inner r (U v)\<bar>"
      by simp
    also have "\<dots> \<le> norm r * norm (Ut v - U v)" by (rule frame_quant_logit_bound)
    also have "\<dots> \<le> \<rho> * \<epsilon>"
      using rbound quant[rule_format, OF vV] rho0 by (intro mult_mono norm_ge_zero) auto
    finally show "\<bar>(inner r (Ut v) + b v) - (inner r (U v) + b v)\<bar> \<le> \<rho> * \<epsilon>" .
  qed
  show ?thesis by (rule margin_certified[OF margin pert tV tol])
qed

end
