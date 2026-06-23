(*
  PIC_Core.thy -- the core locale of Projective Incidence Calculus.

  A single definitional home from which the scattered PIC theorems re-derive. The frame layer
  (locale `pic_frame`) fixes the proposition directions U and biases b and proves the decision-side
  CAPACITY bound (margin_pair_separation / head_capacity, = DecodeCapacity.thy). The source layer
  (locale `pic`) adds a finite set of sources with residual vectors d, defines the native PIC
  vocabulary -- the incidence arrow `incid` (j |> v), the coalition bracket `Lc` (the (X)-monomial),
  the full logit `Lt`, the tropical decode, and the decision turnstile `decides`/`irreducible` --
  and proves:

    logit_is_residual_reading : the full coalition monomial equals the residual reading of the summed
                                residual (sum d) -- the per-source decomposition is EXACT by linearity
                                (the formal face of fieldrun's recon = 1.00);
    Lc_union                  : coalition incidences are additive over disjoint coalitions;
    head_certifies_decode     : a head that tropically dominates the tail reproduces the decode
                                (= HeadTail.thy, now on the PIC logit);
    decides_eq_pdecides       : the turnstile is exactly Separation.thy's `decides`, so the proved
                                witnesses (irreducible_pair, composed_not_irreducible) live in this
                                vocabulary -- composed (mu0) is necessary but NOT sufficient for
                                irreducible.

  This is the spec/PIC_SPEC.md core (the companion `pic` repo) given a machine-checked spine: every
  symbol of S1-S5 of the spec is a definition here, and each headline theorem is a lemma below.
  Self-contained (imports only HOL-Analysis); 0 sorry; quick_and_dirty = false.
*)
theory PIC_Core
  imports "HOL-Analysis.Analysis"
begin

section \<open>Frame layer: the decode-capacity bound (DecodeCapacity)\<close>

text \<open>A PIC frame fixes the proposition directions @{term U} and the biases @{term b}.\<close>
locale pic_frame =
  fixes U :: "'v \<Rightarrow> 'a::real_inner"
    and b :: "'v \<Rightarrow> real"
begin

text \<open>Token @{term v} is \<open>\<gamma>\<close>-decodable at residual @{term r}: it beats every competitor by \<open>\<gamma>\<close>.\<close>
definition gdecodes :: "real \<Rightarrow> 'v \<Rightarrow> 'a \<Rightarrow> bool" where
  "gdecodes \<gamma> v r \<longleftrightarrow> (\<forall>w. w \<noteq> v \<longrightarrow> inner r (U w) + b w + \<gamma> \<le> inner r (U v) + b v)"

definition gdecodable :: "real \<Rightarrow> 'v set" where
  "gdecodable \<gamma> = {v. \<exists>r. norm r \<le> 1 \<and> gdecodes \<gamma> v r}"

text \<open>Two \<open>\<gamma>\<close>-decodable tokens have \<open>\<gamma>\<close>-separated frames -- the biases cancel.\<close>
theorem margin_pair_separation:
  assumes v: "gdecodes \<gamma> v rv" and w: "gdecodes \<gamma> w rw"
      and nv: "norm rv \<le> 1" and nw: "norm rw \<le> 1" and vw: "v \<noteq> w"
  shows "\<gamma> \<le> norm (U v - U w)"
proof -
  have v1: "inner rv (U w) + b w + \<gamma> \<le> inner rv (U v) + b v"
    using v[unfolded gdecodes_def, rule_format, of w] vw by simp
  have w1: "inner rw (U v) + b v + \<gamma> \<le> inner rw (U w) + b w"
    using w[unfolded gdecodes_def, rule_format, of v] vw by simp
  have eq: "inner (rv - rw) (U v - U w)
            = (inner rv (U v) - inner rv (U w)) + (inner rw (U w) - inner rw (U v))"
    by (simp add: inner_diff_left inner_diff_right algebra_simps)
  have key: "2 * \<gamma> \<le> inner (rv - rw) (U v - U w)" using v1 w1 eq by linarith
  have cs: "inner (rv - rw) (U v - U w) \<le> norm (rv - rw) * norm (U v - U w)"
    by (rule norm_cauchy_schwarz)
  have nrw: "norm (rv - rw) \<le> 2" using nv nw norm_triangle_ineq4[of rv rw] by linarith
  have b2: "norm (rv - rw) * norm (U v - U w) \<le> 2 * norm (U v - U w)"
    by (rule mult_right_mono[OF nrw norm_ge_zero])
  from key cs b2 show ?thesis by linarith
qed

corollary decode_capacity_separated:
  assumes hv: "v \<in> gdecodable \<gamma>" and hw: "w \<in> gdecodable \<gamma>" and vw: "v \<noteq> w"
  shows "\<gamma> \<le> dist (U v) (U w)"
proof -
  from hv obtain rv where rv: "norm rv \<le> 1" "gdecodes \<gamma> v rv" unfolding gdecodable_def by blast
  from hw obtain rw where rw: "norm rw \<le> 1" "gdecodes \<gamma> w rw" unfolding gdecodable_def by blast
  have "\<gamma> \<le> norm (U v - U w)" by (rule margin_pair_separation[OF rv(2) rw(2) rv(1) rw(1) vw])
  thus ?thesis by (simp add: dist_norm)
qed

text \<open>Any subset of \<open>\<gamma>\<close>-decodable tokens (in particular a certifiable head) is a \<open>\<gamma>\<close>-code.\<close>
corollary head_capacity:
  assumes "Sset \<subseteq> gdecodable \<gamma>"
  shows "\<forall>v\<in>Sset. \<forall>w\<in>Sset. v \<noteq> w \<longrightarrow> \<gamma> \<le> dist (U v) (U w)"
proof (intro ballI impI)
  fix v w assume "v \<in> Sset" "w \<in> Sset" "v \<noteq> w"
  with assms have "v \<in> gdecodable \<gamma>" "w \<in> gdecodable \<gamma>" by auto
  thus "\<gamma> \<le> dist (U v) (U w)" by (rule decode_capacity_separated[OF _ _ \<open>v \<noteq> w\<close>])
qed

end \<comment> \<open>pic_frame\<close>


section \<open>Source layer: incidence, the decode polynomial, the turnstile\<close>

text \<open>A PIC model extends a frame with a finite source set @{term S} and per-source residual
  vectors @{term d}. The transformer instance: the sources are the DLA blocks.\<close>
locale pic = pic_frame U b
  for U :: "'v \<Rightarrow> 'a::real_inner" and b :: "'v \<Rightarrow> real" +
  fixes S :: "'s set"
    and d :: "'s \<Rightarrow> 'a"
  assumes finS: "finite S"
begin

text \<open>The incidence arrow @{text "j |> v"}: the one native PIC primitive -- provenance as an inner
  product in the frame.\<close>
definition incid :: "'s \<Rightarrow> 'v \<Rightarrow> real" where
  "incid j v = inner (d j) (U v)"

text \<open>The coalition bracket \<open>\<lbrakk>P\<rbrakk>(v)\<close>: the \<open>\<otimes>\<close>-monomial of a coalition (sources add).\<close>
definition Lc :: "'s set \<Rightarrow> 'v \<Rightarrow> real" where
  "Lc P v = (\<Sum>j\<in>P. incid j v)"

text \<open>The full logit of a token: all sources, plus bias.\<close>
definition Lt :: "'v \<Rightarrow> real" where
  "Lt v = Lc S v + b v"

text \<open>SOUNDNESS. The full coalition monomial is the residual reading of the summed residual
  @{term "\<Sum>j\<in>S. d j"} -- the per-source decomposition is exact by linearity. This is the formal
  face of fieldrun's reconstruction = 1.00.\<close>
lemma logit_is_residual_reading:
  "Lt v = inner (\<Sum>j\<in>S. d j) (U v) + b v"
  unfolding Lt_def Lc_def incid_def by (simp add: inner_sum_left)

text \<open>Coalition incidences are additive over disjoint coalitions (the \<open>\<otimes>\<close>-monomial splits).\<close>
lemma Lc_union:
  assumes "finite P" "finite Q" "P \<inter> Q = {}"
  shows "Lc (P \<union> Q) v = Lc P v + Lc Q v"
  unfolding Lc_def using assms by (simp add: sum.union_disjoint)

text \<open>The decode value over a candidate set is the tropical sum (\<open>\<oplus> = max\<close>) of the logits.\<close>
definition decode :: "'v set \<Rightarrow> real" where
  "decode Vs = Max (Lt ` Vs)"

text \<open>HEAD/TAIL on the PIC logit: a head that tropically dominates the tail reproduces the decode.\<close>
theorem head_certifies_decode:
  assumes f: "finite H" "finite T" and ne: "H \<noteq> {}" "T \<noteq> {}"
      and dom: "decode T \<le> decode H"
  shows "decode (H \<union> T) = decode H"
proof -
  have "finite (Lt ` H)" "finite (Lt ` T)" "Lt ` H \<noteq> {}" "Lt ` T \<noteq> {}" using f ne by auto
  hence "Max (Lt ` (H \<union> T)) = max (Max (Lt ` H)) (Max (Lt ` T))"
    by (simp add: image_Un Max_Un)
  thus ?thesis using dom unfolding decode_def by (simp add: max.absorb1)
qed

text \<open>The decision turnstile: coalition @{term P} decides @{term t} over candidates @{term Vs}
  (strict argmax of the coalition monomial).\<close>
definition decides :: "'s set \<Rightarrow> 'v set \<Rightarrow> 'v \<Rightarrow> bool" where
  "decides P Vs t \<longleftrightarrow> (\<forall>v\<in>Vs. v \<noteq> t \<longrightarrow> Lc P v < Lc P t)"

text \<open>Retrieved: a singleton already decides (high multiplicity). Composed: the full set decides but
  no singleton does (\<open>\<mu>\<^sub>t = 0\<close>). Irreducible: decides, but no proper non-empty sub-coalition does.\<close>
definition retrieved :: "'s set \<Rightarrow> 'v set \<Rightarrow> 'v \<Rightarrow> bool" where
  "retrieved P Vs t \<longleftrightarrow> (\<exists>j\<in>P. decides {j} Vs t)"

definition composed :: "'s set \<Rightarrow> 'v set \<Rightarrow> 'v \<Rightarrow> bool" where
  "composed P Vs t \<longleftrightarrow> decides P Vs t \<and> (\<forall>j\<in>P. \<not> decides {j} Vs t)"

definition irreducible :: "'s set \<Rightarrow> 'v set \<Rightarrow> 'v \<Rightarrow> bool" where
  "irreducible P Vs t \<longleftrightarrow> decides P Vs t \<and> \<not> (\<exists>Q. Q \<noteq> {} \<and> Q \<subset> P \<and> decides Q Vs t)"

lemma irreducible_imp_decides: "irreducible P Vs t \<Longrightarrow> decides P Vs t"
  unfolding irreducible_def by simp

text \<open>Note: @{const retrieved} does NOT imply @{const decides} in general -- a single source deciding
  @{term t} need not survive being summed with the rest of the coalition (other sources can outvote
  it on a competitor). That non-implication is precisely the retrieved/composed distinction, and is
  why irreducibility is certified by the turnstile over SUB-coalitions, not by multiplicity.\<close>

end \<comment> \<open>pic\<close>


section \<open>The PIC encoder: how the residual is WRITTEN (the generator / encode side)\<close>

text \<open>A PIC encoder factors the residual itself: on input @{term x} the residual is a gated sum of
  FIXED write directions, @{term "enc x = (\<Sum>k\<in>K. g k x *\<^sub>R a k)"}, where @{term "a k"} are the
  fixed rule write-directions (the output-projection columns -- attention AND MLP both have this form:
  a block's write is @{text "W_out \<cdot> (input-dependent vector)"}) and @{term "g k x"} is the
  input-dependent gate (the neuron activation / attention-weighted coefficient). PIC does NOT model the
  gate's internal computation (the nonlinear forge-tax); it formalizes the LINEAR write/read algebra
  the gate feeds. Requires a finite-dimensional frame (@{class euclidean_space}) for the rank bound.\<close>
locale pic_encoder = pic_frame U b
  for U :: "'v \<Rightarrow> 'a::euclidean_space" and b :: "'v \<Rightarrow> real" +
  fixes K :: "'k set"          \<comment> \<open>the rules (neurons / heads)\<close>
    and a :: "'k \<Rightarrow> 'a"        \<comment> \<open>fixed write directions (output-projection columns)\<close>
    and g :: "'k \<Rightarrow> 'x \<Rightarrow> real" \<comment> \<open>input-dependent gates (activations) -- left uninterpreted\<close>
  assumes finK: "finite K"
begin

text \<open>The residual written on input @{term x}: a gated sum of the fixed write directions.\<close>
definition enc :: "'x \<Rightarrow> 'a" where
  "enc x = (\<Sum>k\<in>K. g k x *\<^sub>R a k)"

text \<open>Rule @{term k}'s incidence on token @{term v}: fixed (input-independent), unlike a per-input source.\<close>
definition incidA :: "'k \<Rightarrow> 'v \<Rightarrow> real" where
  "incidA k v = inner (a k) (U v)"

text \<open>The input-dependent logit, read out of the encoded residual over the frame.\<close>
definition Lx :: "'v \<Rightarrow> 'x \<Rightarrow> real" where
  "Lx v x = inner (enc x) (U v) + b v"

text \<open>ENCODE \<rightarrow> DECODE composition: the logit is a GATED SUM of fixed rule-incidences. This is the whole
  forward pass as a PIC term -- the gates select/weight rules, the fixed incidences carry the geometry.\<close>
lemma Lx_gated_incidence:
  "Lx v x = (\<Sum>k\<in>K. g k x * incidA k v) + b v"
  unfolding Lx_def enc_def incidA_def by (simp add: inner_sum_left inner_scaleR_left)

text \<open>ROUTING RANK, now a property of the explicit encoder: every encoded residual -- for EVERY input --
  lies in the fixed rule span, of dimension at most @{term "card K"} (and at most the ambient dimension).
  Superposition is forced when the number of rules exceeds the ambient dimension.\<close>
lemma enc_in_rule_span: "enc x \<in> span (a ` K)"
  unfolding enc_def
proof (rule span_sum)
  fix k assume "k \<in> K"
  hence "a k \<in> span (a ` K)" by (simp add: span_base)
  thus "g k x *\<^sub>R a k \<in> span (a ` K)" by (rule span_scale)
qed

lemma routing_rank: "dim (span (a ` K)) \<le> card K"
proof -
  have "dim (span (a ` K)) = dim (a ` K)" by (rule dim_span)
  also have "\<dots> \<le> card (a ` K)" by (rule dim_le_card'[OF finite_imageI[OF finK]])
  also have "\<dots> \<le> card K" using finK by (rule card_image_le)
  finally show ?thesis .
qed

lemma routing_rank_dim: "dim (span (a ` K)) \<le> DIM('a)"
  by (simp add: dim_span dim_subset_UNIV)

text \<open>SUPERPOSITION is forced on the WRITERS: more rules than the ambient dimension means the write
  directions cannot be linearly independent -- the rule bank must reuse directions. This is the
  generator-side packing (the qualitative Welch); the quantitative interference floor
  @{text "\<Sum>\<^sub>i\<noteq>\<^sub>j\<langle>a\<^sub>i,a\<^sub>j\<rangle>\<^sup>2 \<ge> n(n-d)/d"} is @{text Welch.thy} (superposition corpus), and the step from
  interference to a margin penalty stays empirical/open (the coherence\<Rightarrow>margin conjecture).\<close>
lemma encoder_superposition:
  assumes "DIM('a) < card (a ` K)"
  shows "\<not> independent (a ` K)"
proof
  assume "independent (a ` K)"
  hence "card (a ` K) \<le> DIM('a)" using independent_bound by blast
  with assms show False by simp
qed

text \<open>BRIDGE: every input-slice of a PIC encoder is a PIC source-model, with sources the gated rules
  \<open>\<lambda>k. g k x *\<^sub>R a k\<close>. The interpretation below succeeds (so the encoder IS a family of @{locale pic}
  models, one per input), and the slice's logit is exactly the encoder logit \<open>Lx v x\<close>. The encoder
  adds the input axis and the fixed-write / gate factorisation that @{locale pic} leaves implicit.\<close>
context fixes x :: 'x
begin
interpretation slice: pic U b K "\<lambda>k. g k x *\<^sub>R a k"
  by unfold_locales (rule finK)

lemma encoder_slice_logit: "slice.Lt v = Lx v x"
  unfolding slice.Lt_def slice.Lc_def slice.incid_def Lx_def enc_def
  by (simp add: inner_sum_left inner_scaleR_left)
end

end \<comment> \<open>pic_encoder\<close>


section \<open>The turnstile in abstract form, and the proved witnesses (Separation)\<close>

text \<open>The turnstile read off a free contribution table -- the form the concrete witnesses use; tied
  to the locale by @{text decides_eq_pdecides} below.\<close>
definition pdecides :: "('s \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> 's set \<Rightarrow> 'v set \<Rightarrow> 'v \<Rightarrow> bool" where
  "pdecides c P Vs t \<longleftrightarrow> (\<forall>v\<in>Vs. v \<noteq> t \<longrightarrow> (\<Sum>j\<in>P. c j v) < (\<Sum>j\<in>P. c j t))"

definition psuff :: "('s \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> 's set \<Rightarrow> 'v set \<Rightarrow> 'v \<Rightarrow> bool" where
  "psuff c P Vs t \<longleftrightarrow> (\<exists>Q. Q \<noteq> {} \<and> Q \<subset> P \<and> pdecides c Q Vs t)"

definition pmu0 :: "('s \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> 's set \<Rightarrow> 'v set \<Rightarrow> 'v \<Rightarrow> bool" where
  "pmu0 c P Vs t \<longleftrightarrow> (\<forall>j\<in>P. \<not> pdecides c {j} Vs t)"

definition pirreducible :: "('s \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> 's set \<Rightarrow> 'v set \<Rightarrow> 'v \<Rightarrow> bool" where
  "pirreducible c P Vs t \<longleftrightarrow> pdecides c P Vs t \<and> \<not> psuff c P Vs t"

text \<open>BRIDGE: inside a PIC model the turnstile is exactly the contribution-table turnstile applied to
  the incidences. So the abstract witnesses below speak about the locale's @{const pic.decides}.\<close>
lemma (in pic) decides_eq_pdecides: "decides P Vs t \<longleftrightarrow> pdecides incid P Vs t"
  unfolding decides_def pdecides_def Lc_def by simp

subsection \<open>Witness 1: an irreducible composed token (every source necessary)\<close>

definition c2 :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "c2 j v = (if j = 1 then (if v = 0 then 2 else if v = 1 then 3 else 0)
             else (if v = 0 then 2 else if v = 1 then 0 else 3))"

lemma pair_is_mu0: "pmu0 c2 {1,2} {0,1,2} 0"
  by (simp add: pmu0_def pdecides_def c2_def)

lemma irreducible_pair: "pirreducible c2 {1,2} {0,1,2} 0"
proof -
  have dec: "pdecides c2 {1,2} {0,1,2} 0" by (simp add: pdecides_def c2_def)
  have nsub: "\<not> psuff c2 {1,2} {0,1,2} 0"
    unfolding psuff_def
  proof (rule notI, elim exE conjE)
    fix P assume P: "P \<noteq> {}" "P \<subset> {1,2::nat}" "pdecides c2 P {0,1,2} 0"
    have fin: "finite P" using P(2) by (meson finite.intros finite_subset psubset_imp_subset)
    have "card P < card {1,2::nat}" using psubset_card_mono[OF _ P(2)] by simp
    moreover have "1 \<le> card P" using P(1) fin by (simp add: Suc_leI card_gt_0_iff)
    ultimately have "card P = 1" by simp
    then obtain j where "P = {j}" by (meson card_1_singletonE)
    hence "P = {1} \<or> P = {2}" using P(2) by auto
    thus False using P(3) by (auto simp: pdecides_def c2_def)
  qed
  show ?thesis using dec nsub by (simp add: pirreducible_def)
qed

subsection \<open>Witness 2: composed (mu0) does NOT imply irreducible -- a proper pair suffices\<close>

definition c3 :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "c3 j v = (if j = 1 then (if v = 0 then 2 else if v = 1 then 3 else 0)
             else if j = 2 then (if v = 0 then 2 else if v = 1 then 0 else 3)
             else (if v = 0 then 0 else 1/2))"

theorem composed_not_irreducible:
  "pmu0 c3 {1,2,3} {0,1,2} 0 \<and> pdecides c3 {1,2,3} {0,1,2} 0 \<and> psuff c3 {1,2,3} {0,1,2} 0"
proof (intro conjI)
  show "pmu0 c3 {1,2,3} {0,1,2} 0" by (simp add: pmu0_def pdecides_def c3_def)
  show "pdecides c3 {1,2,3} {0,1,2} 0" by (simp add: pdecides_def c3_def)
  show "psuff c3 {1,2,3} {0,1,2} 0"
    unfolding psuff_def by (rule exI[of _ "{1,2}"]) (auto simp: pdecides_def c3_def)
qed

text \<open>So @{text "\<mu>\<^sub>t = 0"} (composed) is necessary but NOT sufficient for irreducibility: reading low
  multiplicity as "irreducible computation" is exactly the overclaim this rules out. The turnstile
  over SUB-coalitions, not the multiplicity count, certifies irreducibility.\<close>

end
