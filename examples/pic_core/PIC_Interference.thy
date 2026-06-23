(*
  PIC_Interference.thy -- coherence => margin, made precise (the matched-filter bound).

  The §5.3 open item: does generator-side INTERFERENCE (routing-feature coherence, Welch) degrade the
  decode MARGIN? The UNCONDITIONAL claim is FALSE -- trained models pack features at ~the Welch floor yet
  keep healthy margins, because the decoder is free to STEER off the matched filter. This theory pins the
  exact provable core and the exact reason the strong form fails.

  Routing features f : I -> R^M select tokens (the gate pattern per decision). The MATCHED-FILTER decoder
  steers by the target's own feature (w = f t); token i's logit is then <f t, f i>. We prove:

    mfmargin_unit        : (identity) for a unit target feature the matched-filter margin is
                           1 - (largest cross-coherence with a competitor);
    mfmargin_orthonormal : orthonormal features => matched-filter margin = 1 (zero interference);
    mfmargin_le          : a competitor with positive cross-coherence c caps the margin at 1 - c
                           -- coherence subtracts DIRECTLY from the matched-filter margin;
    mfmargin_lt_one      : ANY positive cross-coherence forces the matched-filter margin below 1.

  HONEST SCOPE. This is the matched-filter decoder only. The achievable (best-steering) margin is
  >= 1 - rho (the matched filter is one feasible choice), so coherence does NOT force the OPTIMAL margin
  down -- the decoder can recover, which is exactly the measured "models cope". Quantifying the optimal
  margin's geometric limit when n > M (Welch regime, superposition forced) is the part that stays OPEN.

  Self-contained over PIC_Core; 0 sorry, quick_and_dirty = false.
*)
theory PIC_Interference
  imports PIC_Core
begin

section \<open>Coherence \<Rightarrow> margin: the matched-filter bound\<close>

context
  fixes f :: "'i \<Rightarrow> 'a::real_inner"   \<comment> \<open>routing features (one per token/decision)\<close>
begin

text \<open>Token @{term i}'s logit under matched-filter steering by the target @{term t} (steer @{text "w = f t"}).\<close>
definition mflogit :: "'i \<Rightarrow> 'i \<Rightarrow> real" where
  "mflogit t i = inner (f t) (f i)"

text \<open>The matched-filter margin of the target over its best competitor.\<close>
definition mfmargin :: "'i \<Rightarrow> 'i set \<Rightarrow> real" where
  "mfmargin t I = mflogit t t - Max (mflogit t ` (I - {t}))"

text \<open>(identity) For a unit target feature, the matched-filter margin is @{text "1 - (max cross-coherence)"}.\<close>
lemma mfmargin_unit:
  assumes "inner (f t) (f t) = 1"
  shows "mfmargin t I = 1 - Max (mflogit t ` (I - {t}))"
  using assms by (simp add: mfmargin_def mflogit_def)

text \<open>(clean regime) Orthonormal features \<Rightarrow> matched-filter margin 1: zero interference, full margin.\<close>
lemma mfmargin_orthonormal:
  assumes ne: "I - {t} \<noteq> {}"
      and ut: "inner (f t) (f t) = 1"
      and orth: "\<And>i. i \<in> I \<Longrightarrow> i \<noteq> t \<Longrightarrow> inner (f t) (f i) = 0"
  shows "mfmargin t I = 1"
proof -
  have "mflogit t ` (I - {t}) = {0}"
  proof
    show "mflogit t ` (I - {t}) \<subseteq> {0}" using orth by (auto simp: mflogit_def)
    from ne obtain x where "x \<in> I - {t}" by blast
    thus "{0} \<subseteq> mflogit t ` (I - {t})" using orth by (auto simp: mflogit_def)
  qed
  thus ?thesis by (simp add: mfmargin_def mflogit_def ut)
qed

text \<open>(degradation) A competitor with cross-coherence @{text "<f t, f i> = c"} caps the matched-filter
  margin at @{text "1 - c"}: positive coherence subtracts directly from the margin.\<close>
lemma mfmargin_le:
  assumes fin: "finite I" and iI: "i \<in> I" and ine: "i \<noteq> t" and ut: "inner (f t) (f t) = 1"
  shows "mfmargin t I \<le> 1 - inner (f t) (f i)"
proof -
  have m: "mflogit t i \<in> mflogit t ` (I - {t})" using iI ine by simp
  have "mflogit t i \<le> Max (mflogit t ` (I - {t}))"
    by (rule Max_ge[OF finite_imageI[OF finite_Diff[OF fin]] m])
  hence "mfmargin t I \<le> mflogit t t - mflogit t i" by (simp add: mfmargin_def)
  thus ?thesis by (simp add: mflogit_def ut)
qed

text \<open>(forced loss) ANY strictly-positive cross-coherence forces the matched-filter margin below 1.\<close>
lemma mfmargin_lt_one:
  assumes "finite I" and "i \<in> I" and "i \<noteq> t" and "inner (f t) (f t) = 1"
      and "inner (f t) (f i) > 0"
  shows "mfmargin t I < 1"
proof -
  have "mfmargin t I \<le> 1 - inner (f t) (f i)" using mfmargin_le[OF assms(1,2,3,4)] .
  also have "\<dots> < 1" using assms(5) by simp
  finally show ?thesis .
qed

end \<comment> \<open>context f\<close>

text \<open>SCOPE (the precise boundary of \<section>5.3's coherence\<Rightarrow>margin link). The bounds above are for the
  MATCHED-FILTER decoder (steer by the target feature). The decoder is free to choose any steering @{text w};
  since the matched filter is one feasible choice, the BEST achievable margin is @{text "\<ge> 1 - \<rho>"} -- so
  coherence does NOT force the optimal margin down, and a trained model can recover it (the measured "cope
  at the Welch floor"). What is PROVED: under matched filtering, coherence subtracts directly from the
  margin, and any positive cross-coherence costs margin. What stays OPEN: a geometric lower bound on the
  optimal (best-steering) margin in the Welch regime @{text "n > M"} (where superposition is forced,
  RoutingWelch) -- the genuinely subtle, sign- and steering-dependent part.\<close>

end
