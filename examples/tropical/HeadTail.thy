(*
  HeadTail.thy -- the tropical HEAD/TAIL decode certificate.

  An LLM's next-token decode is argmax_v <x, U_v>, i.e. the evaluation of the max-plus (tropical) polynomial
  whose monomials are the unembedding rows: decode value = Max over v of the logit L v  (oplus = max = tadd).
  Split the vocabulary V = H \<union> T into a HEAD (a compact monomial set -- empirically the Zipf-frequent winners)
  and a TAIL (the open-class rest). We prove, purely in the max-plus semiring:

    (1) decode_partition      -- the decode tropical-sum SPLITS over the partition  (oplus over H \<union> T = (oplus H) oplus (oplus T)),
    (2) head_certifies_decode -- HEAD CERTIFICATE: when the head's tropical value dominates the tail's, the FULL decode
                                 EQUALS the head decode, and (head_argmax_in_head) its argmaximiser lies in H -- so the
                                 compact head reproduces the decode EXACTLY exactly there,
    (3) tail_is_residue       -- when the head does NOT dominate, the decode lies in T: the open-class TAIL is the
                                 explicit, uncertified residue.

  This is the formal face of the measured boundary (fieldrun lo3a/tropical_rank.py + pr_core_residual_gate.py): a
  compact head certifiably reproduces ~65% of real-model decodes; the ~35% open-class tail is irreducible in every
  algebra tried (linear SVD, Cauchy-Schwarz, max-plus). It is a partition-domination certificate -- the exact-decode
  sibling of the bounded-perturbation PO-T3 margin (../provable_opt/ProvableOpt_Common.decode_margin_certified).
*)
theory HeadTail
  imports Main TropicalSemiring
begin

text \<open>The decode value over a candidate set is the tropical sum (oplus = max) of the logits.\<close>
abbreviation decode :: "('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> real" where
  "decode L S \<equiv> Max (L ` S)"

text \<open>(1) The decode splits over the head/tail partition, with oplus realised as @{const tadd} (= max).\<close>
lemma decode_partition:
  assumes "finite H" "finite T" "H \<noteq> {}" "T \<noteq> {}"
  shows "decode L (H \<union> T) = tadd (decode L H) (decode L T)"
proof -
  have "finite (L ` H)" "finite (L ` T)" "L ` H \<noteq> {}" "L ` T \<noteq> {}" using assms by auto
  hence "Max (L ` H \<union> L ` T) = max (decode L H) (decode L T)" by (simp add: Max_Un)
  thus ?thesis by (simp add: tadd_def image_Un)
qed

text \<open>(2) HEAD CERTIFICATE: when the head's tropical value dominates the tail's, the full decode = the head decode.\<close>
theorem head_certifies_decode:
  assumes f: "finite H" "finite T" and ne: "H \<noteq> {}" "T \<noteq> {}"
      and dom: "decode L T \<le> decode L H"
  shows "decode L (H \<union> T) = decode L H"
  using decode_partition[OF f ne, of L] dom by (simp add: tadd_def max.absorb1)

text \<open>... and the argmaximiser then lies in the HEAD: a head token attains the full decode and beats every candidate.\<close>
theorem head_argmax_in_head:
  assumes f: "finite H" "finite T" and ne: "H \<noteq> {}" "T \<noteq> {}"
      and dom: "decode L T \<le> decode L H"
  shows "\<exists>h\<in>H. L h = decode L (H \<union> T) \<and> (\<forall>v\<in>H \<union> T. L v \<le> L h)"
proof -
  have eq: "decode L (H \<union> T) = decode L H" using f ne dom head_certifies_decode by blast
  have "finite (L ` H)" "L ` H \<noteq> {}" using f(1) ne(1) by auto
  hence "decode L H \<in> L ` H" by (rule Max_in)
  then obtain h where h: "h \<in> H" "L h = decode L H" by auto
  have "\<forall>v\<in>H \<union> T. L v \<le> L h"
  proof
    fix v assume v: "v \<in> H \<union> T"
    have "finite (L ` (H \<union> T))" using f by auto
    moreover have "L v \<in> L ` (H \<union> T)" using v by auto
    ultimately have "L v \<le> decode L (H \<union> T)" by (rule Max_ge)
    thus "L v \<le> L h" using eq h(2) by simp
  qed
  with h eq show ?thesis by auto
qed

text \<open>(3) TAIL RESIDUE: when the head does NOT dominate, the decode lies in the open-class TAIL.\<close>
theorem tail_is_residue:
  assumes f: "finite H" "finite T" and ne: "H \<noteq> {}" "T \<noteq> {}"
      and notdom: "decode L H < decode L T"
  shows "\<exists>t\<in>T. L t = decode L (H \<union> T) \<and> (\<forall>h\<in>H. L h < L t)"
proof -
  have part: "decode L (H \<union> T) = max (decode L H) (decode L T)"
    using decode_partition[OF f ne, of L] by (simp add: tadd_def)
  have "finite (L ` T)" "L ` T \<noteq> {}" using f(2) ne(2) by auto
  hence "decode L T \<in> L ` T" by (rule Max_in)
  then obtain t where t: "t \<in> T" "L t = decode L T" by auto
  have eq: "decode L (H \<union> T) = L t" using part notdom t(2) by simp
  have "\<forall>h\<in>H. L h < L t"
  proof
    fix h assume "h \<in> H"
    hence "L h \<le> decode L H" using f(1) ne(1) by (simp add: Max_ge)
    also have "\<dots> < decode L T" using notdom by simp
    finally show "L h < L t" using t(2) by simp
  qed
  with t eq show ?thesis by auto
qed

text \<open>====================================================================================
  MIN-PLUS (BOTTOM-K) DUAL of the head/tail certificate.

  The top-K decode argmax_v L v has a dual bottom-K decode argmin_v L v -- the most-SUPPRESSED token,
  the negative-temperature / min-plus reading of the same monomials. Everything below is metric-free
  (pure min-plus over the scalar logits), the exact Min-mirror of the Max results above, and is the
  optional dual view a min-plus / shortest-path analysis wants. (The Krein-flavoured companion -- that
  bottom-K equals top-K of the NEGATED FRAME -- lives in examples/pic_krein/KreinBottomK.thy.)
  ==================================================================================== \<close>

abbreviation codecode :: "('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> real" where
  "codecode L S \<equiv> Min (L ` S)"

text \<open>(1) The bottom-decode splits over the partition, with oplus realised as min (the min-plus sum).\<close>
lemma codecode_partition:
  assumes "finite H" "finite T" "H \<noteq> {}" "T \<noteq> {}"
  shows "codecode L (H \<union> T) = min (codecode L H) (codecode L T)"
proof -
  have "finite (L ` H)" "finite (L ` T)" "L ` H \<noteq> {}" "L ` T \<noteq> {}" using assms by auto
  hence "Min (L ` H \<union> L ` T) = min (codecode L H) (codecode L T)" by (simp add: Min_Un)
  thus ?thesis by (simp add: image_Un)
qed

text \<open>(2) CO-HEAD CERTIFICATE: when the co-head's minimum is at or below the tail's, the full bottom-K
  decode equals the co-head's -- the co-head contains the most-suppressed token.\<close>
theorem cohead_certifies_decode:
  assumes f: "finite H" "finite T" and ne: "H \<noteq> {}" "T \<noteq> {}"
      and dom: "codecode L H \<le> codecode L T"
  shows "codecode L (H \<union> T) = codecode L H"
  using codecode_partition[OF f ne, of L] dom by (simp add: min.absorb1)

text \<open>... and the argMIN then lies in the CO-HEAD.\<close>
theorem cohead_argmin_in_cohead:
  assumes f: "finite H" "finite T" and ne: "H \<noteq> {}" "T \<noteq> {}"
      and dom: "codecode L H \<le> codecode L T"
  shows "\<exists>h\<in>H. L h = codecode L (H \<union> T) \<and> (\<forall>v\<in>H \<union> T. L h \<le> L v)"
proof -
  have eq: "codecode L (H \<union> T) = codecode L H" using f ne dom cohead_certifies_decode by blast
  have "finite (L ` H)" "L ` H \<noteq> {}" using f(1) ne(1) by auto
  hence "codecode L H \<in> L ` H" by (rule Min_in)
  then obtain h where h: "h \<in> H" "L h = codecode L H" by auto
  have "\<forall>v\<in>H \<union> T. L h \<le> L v"
  proof
    fix v assume v: "v \<in> H \<union> T"
    have "finite (L ` (H \<union> T))" using f by auto
    moreover have "L v \<in> L ` (H \<union> T)" using v by auto
    ultimately have "codecode L (H \<union> T) \<le> L v" by (rule Min_le)
    thus "L h \<le> L v" using eq h(2) by simp
  qed
  with h eq show ?thesis by auto
qed

text \<open>(3) BOTTOM-K RESIDUE: when the co-head does NOT dominate from below, the most-suppressed token is
  in the open-class tail -- the explicit bottom-K residue, dual to tail_is_residue.\<close>
theorem cotail_is_residue:
  assumes f: "finite H" "finite T" and ne: "H \<noteq> {}" "T \<noteq> {}"
      and notdom: "codecode L T < codecode L H"
  shows "\<exists>t\<in>T. L t = codecode L (H \<union> T) \<and> (\<forall>h\<in>H. L t < L h)"
proof -
  have part: "codecode L (H \<union> T) = min (codecode L H) (codecode L T)"
    using codecode_partition[OF f ne, of L] .
  have "finite (L ` T)" "L ` T \<noteq> {}" using f(2) ne(2) by auto
  hence "codecode L T \<in> L ` T" by (rule Min_in)
  then obtain t where t: "t \<in> T" "L t = codecode L T" by auto
  have eq: "codecode L (H \<union> T) = L t" using part notdom t(2) by simp
  have "\<forall>h\<in>H. L t < L h"
  proof
    fix h assume hH: "h \<in> H"
    have "codecode L T < codecode L H" using notdom by simp
    also have "codecode L H \<le> L h" using hH f(1) by (simp add: Min_le)
    finally show "L t < L h" using t(2) by simp
  qed
  with t eq show ?thesis by auto
qed

end
