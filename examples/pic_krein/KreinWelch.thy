(*
  KreinWelch.thy -- PIC over a Krein space, the FRAME side: where the signature actually bites.

  Companion to KreinDecode.thy.  Here the residual/frame space carries an INDEFINITE inner product in
  coordinates (mirroring Welch.thy's `ip`): a signature s : 'k => real with s b in {+1,-1} (spacelike /
  timelike coordinates), and

        ipK  K x y = SUM_{b in K} x b * y b           (the positive-definite MAJORANT)
        kip s K x y = SUM_{b in K} s b * x b * y b     (the indefinite Krein form)
        Js  s   x   = (\<lambda>b. s b * x b)               (the fundamental symmetry in coordinates).

  The Euclidean frame side of PIC (Welch.thy, DecodeCapacity.thy) used positive-definiteness in two
  silent places: a COMPACT unit ball (packing capacity) and a PSD Gram (the Welch floor).  Both feel
  the signature; this file states exactly how.

  RESULTS:
    kip_definitize          : the coordinate definitization, kip s K x y = ipK K (Js s x) y.
    kip_sym                 : the Krein form is symmetric.
    single_coord_self       : a feature on a single coordinate has self-coherence = s b0 -- so a
                              "unit" feature is spacelike (+1) or TIMELIKE (-1); "unit norm" splits.
    null_vector             : in signature (1,1) there is a NON-ZERO null token, kip x x = 0 -- a
                              Krein-native "intrinsically composed" proposition with no self-steering
                              margin (it sits on the light cone).
    kip_trace_eq_signature  : the Gram trace SUM_i kip(v_i,v_i) is the signature imbalance s = p - q,
                              not the count n -- the quantity that drives the Welch floor.
    krein_welch_driver_vanishes : the DRIVER of the welch_sos lower bound -- the term trace^2 / |K|,
                              which in the Euclidean case forces interference SUM_{i!=j} <f_i,f_j>^2
                              >= n(n-d)/d -- degrades to s^2/|K| and is VACUOUS (= 0) at balanced
                              signature s = p - q = 0.  Note carefully: it is the TRACE-DRIVER of the
                              bound that vanishes, NOT the interference (see HONESTY).  The Welch
                              *guarantee* is a positive-definiteness phenomenon.
    indefinite_ball_unbounded : the indefinite pseudo-ball {x : kip x x <= 1} is UNBOUNDED in the
                              majorant whenever a timelike coordinate exists -- so the packing/covering
                              argument behind DecodeCapacity has no compact domain and the capacity
                              bound COLLAPSES (timelike escape).

  HONESTY (pic tag discipline).
  (1) krein_welch_driver_vanishes kills the *guarantee* (the trace-driven LOWER BOUND), not the
      interference.  The true floor does NOT vanish: a Krein-orthonormal set ([f_i,f_j] = +-delta) is
      still linearly independent, so zero off-diagonal still forces n <= d (Eckart-Young keeps a rank-<=d
      Gram bounded away from diag(+-1) for n > d).  So for n > d the interference floor is POSITIVE but
      SIGNATURE-DEPENDENT -- it moves off trace^2/|K| to an inertia-dependent expression we do NOT derive
      here.  "Can interference be made arbitrarily small with n > d?" -- NO; "is the sharp signature floor
      below n(n-d)/d?" -- [open].
  (2) The non-compactness in indefinite_ball_unbounded is INTRINSIC to any genuinely indefinite form
      (signature with q >= 1), basis- and J-independent: a timelike ray sits in every sublevel set.  It
      is NOT an artifact of the majorant (the majorant is only the yardstick) and cannot be repaired by
      restricting to a timelike cone (a ray is in the cone) or by changing J (any q >= 1 is non-compact;
      q = 0 is just Euclidean).  Compactness returns ONLY by re-imposing a majorant bound -- which is
      exactly margin_pair_separation_k (KreinDecode).
  (3) That a real transformer's QK pairing has non-trivial signature is [open/empirical] (a fieldrun
      measurement, not a theorem here); timelike units / null tokens have NO correspondent in a standard
      (positive-definite) model -- they exist only if an indefinite readout is imposed.
*)
theory KreinWelch
  imports "HOL-Analysis.Analysis"
begin

definition ipK :: "'k set \<Rightarrow> ('k \<Rightarrow> real) \<Rightarrow> ('k \<Rightarrow> real) \<Rightarrow> real" where
  "ipK K x y = (\<Sum>b\<in>K. x b * y b)"

definition kip :: "('k \<Rightarrow> real) \<Rightarrow> 'k set \<Rightarrow> ('k \<Rightarrow> real) \<Rightarrow> ('k \<Rightarrow> real) \<Rightarrow> real" where
  "kip s K x y = (\<Sum>b\<in>K. s b * x b * y b)"

definition Js :: "('k \<Rightarrow> real) \<Rightarrow> ('k \<Rightarrow> real) \<Rightarrow> ('k \<Rightarrow> real)" where
  "Js s x = (\<lambda>b. s b * x b)"

text \<open>Coordinate definitization: the Krein form is the majorant of the J-transformed argument.\<close>
lemma kip_definitize: "kip s K x y = ipK K (Js s x) y"
  by (simp add: kip_def ipK_def Js_def mult.assoc)

text \<open>The Krein form is symmetric.\<close>
lemma kip_sym: "kip s K x y = kip s K y x"
  unfolding kip_def by (intro sum.cong refl) (simp add: ac_simps)

text \<open>A feature concentrated on a single coordinate @{term b0} has self-coherence @{term "s b0"}.
  With @{term "s b0 = 1"} it is a spacelike unit; with @{term "s b0 = -1"} a TIMELIKE unit
  (self-coherence @{term "-1"}).  So in a Krein frame "unit norm" is not one class but two.\<close>
lemma single_coord_self:
  assumes finK: "finite K" and b0: "b0 \<in> K"
  shows "kip s K (\<lambda>b. if b = b0 then 1 else 0) (\<lambda>b. if b = b0 then 1 else 0) = s b0"
proof -
  have "kip s K (\<lambda>b. if b = b0 then 1 else 0) (\<lambda>b. if b = b0 then 1 else 0)
        = (\<Sum>b\<in>K. if b = b0 then s b else 0)"
    unfolding kip_def by (intro sum.cong refl) simp
  also have "\<dots> = s b0" using finK b0 by (simp add: sum.delta)
  finally show ?thesis .
qed

text \<open>NULL TOKEN.  In a signature-(1,1) coordinate pair there is a non-zero vector with self-coherence
  kip x x = 0 -- it lies on the light cone.  Steered by its own direction it gains zero self-incidence,
  so it can never be retrieved single-source: a frame-geometric sibling of the coalition-combinatorial
  "composed" token (Separation.thy).\<close>
lemma null_vector:
  assumes finK: "finite K" and bp: "bp \<in> K" and bm: "bm \<in> K" and ne: "bp \<noteq> bm"
      and sp: "s bp = 1" and sm: "s bm = - 1"
  shows "kip s K (\<lambda>b. if b = bp \<or> b = bm then 1 else 0) (\<lambda>b. if b = bp \<or> b = bm then 1 else 0) = 0
         \<and> (\<lambda>b. if b = bp \<or> b = bm then (1::real) else 0) \<noteq> (\<lambda>b. 0)"
proof
  let ?x = "(\<lambda>b. if b = bp \<or> b = bm then (1::real) else 0)"
  have "kip s K ?x ?x = (\<Sum>b\<in>K. s b * ?x b * ?x b)" by (simp add: kip_def)
  also have "\<dots> = (\<Sum>b\<in>{bp, bm}. s b * ?x b * ?x b)"
    by (rule sum.mono_neutral_right) (use finK bp bm in auto)
  also have "\<dots> = s bp + s bm" using ne by simp
  also have "\<dots> = 0" using sp sm by simp
  finally show "kip s K ?x ?x = 0" .
next
  show "(\<lambda>b. if b = bp \<or> b = bm then (1::real) else 0) \<noteq> (\<lambda>b. 0)"
  proof
    assume "(\<lambda>b. if b = bp \<or> b = bm then (1::real) else 0) = (\<lambda>b. 0)"
    hence "(if bp = bp \<or> bp = bm then (1::real) else 0) = 0" by (rule fun_cong)
    thus False by simp
  qed
qed

text \<open>The Gram TRACE is the signature imbalance, not the count.  If each feature is a unit
  (@{term "kip s K (v i) (v i) = eps i"}, @{term "eps i \<in> {1,-1}"}) the trace is
  @{term "(\<Sum>i\<in>I. eps i) = p - q"}.\<close>
lemma kip_trace_eq_signature:
  assumes diag: "\<And>i. i \<in> I \<Longrightarrow> kip s K (v i) (v i) = eps i"
  shows "(\<Sum>i\<in>I. kip s K (v i) (v i)) = (\<Sum>i\<in>I. eps i)"
  by (rule sum.cong[OF refl]) (simp add: diag)

text \<open>WELCH DEGRADATION.  The DRIVER of the welch_sos lower bound on total squared coherence is
  @{term "(\<Sum>i\<in>I. kip s K (v i) (v i))\<^sup>2 / real (card K)"} -- the trace squared over the dimension.
  For a BALANCED signature (@{term "(\<Sum>i\<in>I. eps i) = 0"}) it is exactly 0: the term that, in the
  positive-definite case, forces interference @{term "n*(n-d)/d > 0"} when @{term "n > d"} becomes
  VACUOUS.  Read precisely: it is the TRACE-DRIVER of the bound that vanishes, NOT the interference --
  the *guarantee* of forced interference is what indefiniteness removes (the eigenvalues can cancel).
  The true floor stays positive for @{term "n > d"} (linear independence still caps a Krein-orthonormal
  set at d), only it moves off trace^2 / card K to a signature-dependent expression not
  derived here.\<close>
lemma krein_welch_driver_vanishes:
  assumes diag: "\<And>i. i \<in> I \<Longrightarrow> kip s K (v i) (v i) = eps i"
      and bal: "(\<Sum>i\<in>I. eps i) = 0"
  shows "(\<Sum>i\<in>I. kip s K (v i) (v i))\<^sup>2 / real (card K) = 0"
proof -
  have "(\<Sum>i\<in>I. kip s K (v i) (v i)) = (\<Sum>i\<in>I. eps i)"
    by (rule sum.cong[OF refl]) (simp add: diag)
  also have "\<dots> = 0" by (simp add: bal)
  finally show ?thesis by simp
qed

text \<open>OPEN: the sharp signature-dependent interference floor for n > d (the positive replacement for
  the vacuous trace-driver bound), and whether it can fall below the Euclidean n(n-d)/d.  This lemma
  only kills the trace-driven guarantee; achievability of sub-Welch coherence is unresolved.\<close>

text \<open>CAPACITY COLLAPSE.  If any coordinate is timelike (s b0 < 0) the indefinite pseudo-ball
  {x. kip s K x x <= 1} is unbounded in the majorant: for every radius R there is a point inside the
  pseudo-ball with majorant norm-squared >= R (a timelike ray escapes to infinity at no Krein-norm
  cost).  So the packing/covering number behind DecodeCapacity.head_capacity has no compact domain --
  the cell-capacity bound is a theorem about the MAJORANT, vacuous in the indefinite metric of record.
  This non-compactness is INTRINSIC to any genuinely indefinite form (q >= 1), basis- and J-independent;
  it is not an artifact of the majorant and is not repaired by a timelike-cone restriction or a change
  of J.  Compactness returns only by re-imposing a majorant bound (margin_pair_separation_k).\<close>
lemma indefinite_ball_unbounded:
  assumes finK: "finite K" and b0: "b0 \<in> K" and tl: "s b0 < 0"
  shows "\<forall>R. \<exists>x. kip s K x x \<le> 1 \<and> ipK K x x \<ge> R"
proof
  fix R :: real
  define c where "c = sqrt (max R 0)"
  define x where "x = (\<lambda>b. if b = b0 then c else 0)"
  have nn: "0 \<le> max R 0" by simp
  have c2: "c * c = max R 0"
    using nn by (simp add: c_def power2_eq_square[symmetric])
  have ipval: "ipK K x x = c * c"
  proof -
    have "ipK K x x = (\<Sum>b\<in>K. if b = b0 then c * c else 0)"
      unfolding ipK_def x_def by (intro sum.cong refl) simp
    also have "\<dots> = c * c" using finK b0 by (simp add: sum.delta)
    finally show ?thesis .
  qed
  have kval: "kip s K x x = s b0 * (c * c)"
  proof -
    have "kip s K x x = (\<Sum>b\<in>K. if b = b0 then s b0 * (c * c) else 0)"
      unfolding kip_def x_def by (intro sum.cong refl) simp
    also have "\<dots> = s b0 * (c * c)" using finK b0 by (simp add: sum.delta)
    finally show ?thesis .
  qed
  show "\<exists>x. kip s K x x \<le> 1 \<and> ipK K x x \<ge> R"
  proof (intro exI[of _ x] conjI)
    have "s b0 * (c * c) \<le> 0"
      using tl c2 nn by (simp add: mult_nonpos_nonneg)
    thus "kip s K x x \<le> 1" using kval by simp
    show "ipK K x x \<ge> R" using ipval c2 by simp
  qed
qed

end
