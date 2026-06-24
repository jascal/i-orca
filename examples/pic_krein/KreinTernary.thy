(*
  KreinTernary.thy -- the bridge between the bitnet (BitNet b1.58 ternary-weight) corpus, PIC, and
  Krein-PIC, plus the kernel-checkable VALUE-SYSTEM differences (ternary / integer vs float).

  The question: is a ternary {-1,0,1} structure best described by PIC or by Krein-PIC?  Answer (see
  TERNARY.md): it depends on whether the ternary lives in the DATA or in the METRIC.

  (1) Ternary as a SIGNATURE / metric.  The Krein fundamental symmetry is BINARY: J^2 = I forces
      eigenvalues +-1, so a strict Krein signature has no zero (Js_involution: s^2 = 1 => Js o Js = id,
      in KreinWelch).  A TERNARY signature s_b in {-1,0,1} is NOT strict Krein -- the zeros make the form
      DEGENERATE (a "Krein space with a radical").  It is characterised here by the TRIPOTENT law

          s^3 = s   <=>   Js o Js o Js = Js                 (Js_tripotent)

      whose three real roots are exactly {-1,0,1}.  Js o Js is then multiply-by-s^2 = projection onto the
      support {b. s_b != 0}; the radical is {b. s_b = 0}.  So a ternary signature is the Sylvester inertia
      triple (p,q,z) -- one notch more general than Krein's (p,q).  This is the same {-1,0,1}^d object as
      a bitnet ternary WEIGHT vector (Ternary.thy `tprod`): a ternary weight, read as a metric, is a
      tripotent degenerate fundamental symmetry.

  (2) Ternary as DATA -- standard (Euclidean) PIC suffices; no Krein needed (signed incidence already
      covers +/-/0).  The bitnet facts apply directly: a ternary incidence is a multiplication-free signed
      sum (Ternary.ternary_dot_signed_sum), and an integer frame is a LOSSLESS power-of-3 stack of ternary
      frames (BalancedTernary.balanced_ternary_exists, Lossless.lossless_realization).

  VALUE-SYSTEM DIFFERENCES (provable, decode-side, hence metric-free -- PIC and Krein-PIC alike):
    int_strict_winner_robust : INTEGER (or ternary) logits give a robustness FLOOR -- a strict winner has
                               margin >= 1, so it survives ANY real perturbation < 1/2, no matter how close
                               the runner-up.  Float has no such floor (a strict win by epsilon is not
                               robust to epsilon noise): the proved margin certificate's 2*delta band is
                               EMPTY above ties for exact systems, a continuum for float.
    card_ternary_frame       : the ternary frame space is FINITE, exactly 3^d, vs the continuum of float
                               frames -- packing is a finite ternary-coding question, not a covering number.

  Tags: Js_tripotent, Js_sq, int_strict_winner_robust, card_ternary_frame are [proved] here; the bitnet
  lemmas cited are [proved] in examples/bitnet; "a real model wants a ternary metric" is [open/empirical].
*)
theory KreinTernary
  imports KreinWelch "HOL-Library.FuncSet"
begin

subsection \<open>Ternary signature = tripotent degenerate fundamental symmetry\<close>

text \<open>The TRIPOTENT law.  A ternary signature (s_b^3 = s_b, i.e. s_b in {-1,0,1}) makes the coordinate
  symmetry Js a tripotent: Js o Js o Js = Js.  This is the ternary analogue of the Krein involution
  Js o Js = id (KreinWelch.Js_involution), and the algebraic bridge to bitnet's ternary weights.\<close>
lemma Js_tripotent:
  assumes s3: "\<And>b. s b * s b * s b = s b"
  shows "Js s (Js s (Js s x)) = Js s x"
proof (rule ext)
  fix b
  have "Js s (Js s (Js s x)) b = s b * (s b * (s b * x b))" by (simp add: Js_def)
  also have "\<dots> = (s b * s b * s b) * x b" by (simp add: mult.assoc)
  also have "\<dots> = s b * x b" using s3 by simp
  also have "\<dots> = Js s x b" by (simp add: Js_def)
  finally show "Js s (Js s (Js s x)) b = Js s x b" .
qed

text \<open>Js o Js is multiply-by-s^2; for a ternary signature s^2 in {0,1} is the indicator of the support,
  so Js o Js is the projection onto {b. s_b != 0} and the radical is {b. s_b = 0}.\<close>
lemma Js_sq: "Js s (Js s x) = Js (\<lambda>b. s b * s b) x"
  by (rule ext) (simp add: Js_def mult.assoc)

subsection \<open>Value-system differences (decode-side, metric-free): integer/ternary vs float\<close>

text \<open>THE DISCRETE ROBUSTNESS FLOOR.  Integer-valued logits (in particular ternary-incidence logits) have
  a margin GAP: a strict winner beats the field by at least 1, so it survives EVERY real perturbation
  bounded by 1/2 -- independent of how close the runner-up is.  This is the proved margin certificate
  (the 2*delta threshold) with delta < 1/2 < margin.  Float logits have no such floor: a strict win by an
  arbitrarily small amount is not robust, so float leaves a continuum-wide uncertified band that exact
  (ternary/integer) arithmetic does not.\<close>
lemma int_strict_winner_robust:
  fixes L :: "'v \<Rightarrow> int" and L' :: "'v \<Rightarrow> real"
  assumes win:  "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> L v < L t"
      and pert: "\<forall>v\<in>V. \<bar>L' v - real_of_int (L v)\<bar> < 1/2"
      and tV:   "t \<in> V"
  shows "\<forall>v\<in>V. v \<noteq> t \<longrightarrow> L' v < L' t"
proof (intro ballI impI)
  fix v assume vV: "v \<in> V" and vt: "v \<noteq> t"
  have "L v < L t" using win vV vt by blast
  hence g1: "L v + 1 \<le> L t" by presburger
  have rgap: "real_of_int (L v) + 1 \<le> real_of_int (L t)"
  proof -
    have "real_of_int (L v + 1) \<le> real_of_int (L t)" using g1 by (simp add: of_int_le_iff)
    thus ?thesis by simp
  qed
  have pv: "\<bar>L' v - real_of_int (L v)\<bar> < 1/2" using pert vV by blast
  have pt: "\<bar>L' t - real_of_int (L t)\<bar> < 1/2" using pert tV by blast
  have a: "L' v - real_of_int (L v) \<le> \<bar>L' v - real_of_int (L v)\<bar>" by simp
  have b: "real_of_int (L t) - L' t \<le> \<bar>L' t - real_of_int (L t)\<bar>"
    by (simp add: abs_minus_commute)
  from a b pv pt rgap show "L' v < L' t" by linarith
qed

text \<open>FINITE FRAME SPACE.  The ternary frame space over a finite coordinate set K has exactly 3^|K|
  vectors -- a hard finite cap.  So decode packing for ternary frames is a finite ternary-coding question,
  not the continuous covering number (1 + 2 rho / gamma)^d of DecodeCapacity; the float frame space is a
  continuum.\<close>
lemma card_ternary_frame:
  assumes finK: "finite K"
  shows "card (Pi\<^sub>E K (\<lambda>_. {-1, 0, 1::int})) = 3 ^ card K"
proof -
  have cc: "card {-1, 0, 1::int} = 3" by simp
  have "card (Pi\<^sub>E K (\<lambda>_. {-1, 0, 1::int})) = (\<Prod>b\<in>K. (3::nat))"
    by (simp add: card_PiE[OF finK] cc)
  thus ?thesis by (simp add: prod_constant)
qed

subsection \<open>Lossless conversion to ternary by ADDING DIMENSIONS (width expansion)\<close>

text \<open>The provable lossless conversion.  Per-weight ternarization (rounding into {-1,0,1}) is LOSSY
  (Ternary.roundclip_not_injective).  But with DIMENSION EXPANSION it is exact: expand each integer
  weight into its K balanced-ternary digits (w_j = SUM_{k<K} t_{jk} 3^k, the digits t_{jk} in {-1,0,1}
  exist by BalancedTernary.balanced_ternary_exists), and the incidence rearranges as

      <w, x>  =  SUM_{k<K} 3^k * <t_{.,k}, x>

  -- a fixed power-of-3 combination of K TERNARY incidences <t_{.,k}, x> (the K "trit-plane" hidden
  dimensions added to the layer).  The only non-ternary part is the fixed 3^k read-out (no learned,
  non-ternary weights).  So an INTEGER model converts to ternary LOSSLESSLY at a K-fold width blow-up,
  K = ceil(log_3(value range)).  A finite-precision FP model is integers times a common 2-power scale,
  so it reduces to the integer case plus one fixed global scale -- also lossless (genuinely
  infinite-precision reals are NOT finitely ternary-representable).  The identity below is radix-3 /
  digit-agnostic; ternary is the instantiation where the digits are balanced-ternary.

  In PIC terms: ternary is lossy at FIXED dimension, lossless WITH dimension expansion -- you trade
  ternary's low per-weight precision for added routing rank (the trit-planes), the movable-frame seam.\<close>
lemma ternary_widen_lossless:
  fixes w :: "'j \<Rightarrow> int" and x :: "'j \<Rightarrow> 'a::comm_ring_1" and t :: "'j \<Rightarrow> nat \<Rightarrow> int"
  assumes finJ: "finite J"
      and expand: "\<And>j. j \<in> J \<Longrightarrow> w j = (\<Sum>k<K. t j k * 3 ^ k)"
  shows "(\<Sum>j\<in>J. of_int (w j) * x j)
       = (\<Sum>k<K. (3::'a) ^ k * (\<Sum>j\<in>J. of_int (t j k) * x j))"
proof -
  have "(\<Sum>j\<in>J. of_int (w j) * x j)
      = (\<Sum>j\<in>J. (\<Sum>k<K. (3::'a) ^ k * (of_int (t j k) * x j)))"
  proof (rule sum.cong[OF refl])
    fix j assume jJ: "j \<in> J"
    have "of_int (w j) * x j = of_int (\<Sum>k<K. t j k * 3 ^ k) * x j" by (simp add: expand[OF jJ])
    also have "\<dots> = (\<Sum>k<K. of_int (t j k) * (3::'a) ^ k) * x j"
      by (simp add: of_int_sum of_int_mult of_int_power)
    also have "\<dots> = (\<Sum>k<K. (3::'a) ^ k * (of_int (t j k) * x j))"
      by (simp add: sum_distrib_left sum_distrib_right mult_ac)
    finally show "of_int (w j) * x j = (\<Sum>k<K. (3::'a) ^ k * (of_int (t j k) * x j))" .
  qed
  also have "\<dots> = (\<Sum>k<K. (\<Sum>j\<in>J. (3::'a) ^ k * (of_int (t j k) * x j)))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>k<K. (3::'a) ^ k * (\<Sum>j\<in>J. of_int (t j k) * x j))"
    by (simp add: sum_distrib_left)
  finally show ?thesis .
qed

text \<open>LOSSLESS COMPRESSION (storage).  A natively-ternary frame is losslessly packable: five ternary
  weights fit in one byte (3^5 = 243 <= 256 = 2^8), i.e. ~1.58 bits/weight (mirrors bitnet's
  five_trits_per_byte / log2_3_approx).  So a ternary frame is a ~10-20x lossless storage compression
  over fp16/fp32.

  Honest caveats (where the compression actually comes from):
   * Converting fp/int -> ternary via ternary_widen_lossless is bit-NEUTRAL: the K-fold width expansion
     exactly offsets the per-weight bit drop (K trits = log2(range) bits = the original integer's bits).
     So ternary does not CREATE compression on conversion -- it SURFACES the model's redundancy.
   * Below ~1.58 bits/weight needs STRUCTURE: sparse ternary (mostly 0, as trained ternary nets are) has
     entropy < log2 3, so entropy coding compresses further (Shannon bound -- can't beat the frame's
     entropy).
   * Decode-side floor: the frame matters only through the logits, so lossless decode-preserving
     compression is bounded below by the frame RANK -- the Theta(d) frozen-compression floor of
     PIC_SPEC sec 5/6 (a rank-bottlenecked retrained update clears it; frozen compression does not).\<close>
lemma ternary_byte_packing: "(3::nat) ^ 5 \<le> 2 ^ 8"
  by simp

end
