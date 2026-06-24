(*
  KreinDecode.thy -- PIC over a Krein space, the DECODE side: metric-free, survives in the majorant.

  THOUGHT EXPERIMENT (companion to pic/spec/PIC_SPEC.md).  PIC's incidence is an inner product
  j |> v = <d_j, U_v> in a Euclidean residual space.  Replace the Euclidean inner product by an
  INDEFINITE (Krein) form

        [x, y] := <J x, y>,        J the "fundamental symmetry" (J self-adjoint, J o J = id),

  where <.,.> is the positive-definite MAJORANT and J encodes the signature (+1 on the spacelike
  subspace, -1 on the timelike one).  This file isolates the half of PIC that does NOT feel the
  signature.

  THE DECISIVE OBSERVATION (kinner_definitize / krein_logit_definitize).  Because J is invertible,
  a Krein incidence is a Euclidean incidence of the J-transformed source: [d, U_v] = <J d, U_v>.
  Everything that flows into the semiring layer is the SCALAR logit, so the entire decode side
  (monomials, argmax, semiring family, margins, head/tail) transfers verbatim under d_j |-> J d_j.

  WHAT THIS BUYS, MADE PRECISE:
    krein_logit_definitize    : the PIC monomial under [.,.] equals the Euclidean monomial with
                                sources d'_j = J d_j -- the decode is metric-free.
    kinner_sym                : the indefinite form is symmetric (J self-adjoint).
    kinner_majorant           : applying J on BOTH sides recovers the majorant <x,y> (J an involution)
                                -- "retreat to the majorant", the definitization escape hatch.
    margin_pair_separation_k  : the DecodeCapacity separation theorem SURVIVES under the Krein form
                                AS LONG AS the residual ball is the majorant ball (norm r <= 1): two
                                gamma-decodable tokens are gamma-separated, gamma <= ||U_v - U_w||.
                                (Proof = DecodeCapacity.margin_pair_separation with the witnesses
                                J r_v, J r_w, which the majorant isometry keeps in the unit ball.)

  CAVEAT this file makes honest (see KreinWelch.thy for the other half): the survival above needs the
  MAJORANT ball.  In the genuinely indefinite pseudo-ball {r : [r,r] <= 1} the bound COLLAPSES
  (KreinWelch.indefinite_ball_unbounded).  With J = id this is exactly ordinary PIC, which is why a
  FIXED, freely-absorbable J adds nothing: the content is in fixing the signature / freezing the frame
  and reading norms in [.,.] rather than the majorant.

  Tags (pic discipline): kinner_* and krein_logit_definitize are [proved] here; margin_pair_separation_k
  is [proved] here; the claim that this is the RIGHT model of any transformer pairing (the QK form) is
  [open/empirical].
*)
theory KreinDecode
  imports "HOL-Analysis.Analysis"
begin

text \<open>The Krein (indefinite) form induced by a fundamental symmetry @{term J}:
  @{term "kinner J x y = inner (J x) y"}.  J = id recovers the Euclidean inner product.\<close>
definition kinner :: "('a::real_inner \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real" where
  "kinner J x y = inner (J x) y"

text \<open>DEFINITIZATION (the one-liner the whole transfer rests on): a Krein incidence is the Euclidean
  incidence of the J-transformed source.  Stated at the level of a full PIC monomial / logit -- the
  Krein logit equals the Euclidean logit with sources @{term "\<lambda>j. J (d j)"}.\<close>
lemma krein_logit_definitize:
  "(\<Sum>j\<in>Jset. kinner J (d j) (U v)) + bb v = (\<Sum>j\<in>Jset. inner (J (d j)) (U v)) + bb v"
  by (simp add: kinner_def)

text \<open>The indefinite form is symmetric when J is self-adjoint for the majorant.\<close>
lemma kinner_sym:
  assumes selfadj: "\<And>x y. inner (J x) y = inner x (J y)"
  shows "kinner J x y = kinner J y x"
proof -
  have "kinner J x y = inner (J x) y" by (simp add: kinner_def)
  also have "\<dots> = inner x (J y)" by (rule selfadj)
  also have "\<dots> = inner (J y) x" by (rule inner_commute)
  also have "\<dots> = kinner J y x" by (simp add: kinner_def)
  finally show ?thesis .
qed

text \<open>Applying J on both sides recovers the positive-definite majorant (J an involution) -- the
  "retreat to the majorant" escape hatch, and the reason a freely-absorbable J is trivial.\<close>
lemma kinner_majorant:
  assumes invol: "\<And>x. J (J x) = x"
  shows "kinner J (J x) y = inner x y"
  by (simp add: kinner_def invol)

text \<open>Token @{term v} beats every competitor by at least @{term \<gamma>} at residual @{term r}, read in
  the INDEFINITE form.\<close>
definition gdecodes_k ::
  "('a::real_inner \<Rightarrow> 'a) \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> 'v \<Rightarrow> 'a \<Rightarrow> bool" where
  "gdecodes_k J U b \<gamma> v r \<longleftrightarrow>
     (\<forall>w. w \<noteq> v \<longrightarrow> kinner J r (U w) + b w + \<gamma> \<le> kinner J r (U v) + b v)"

text \<open>DECODE CAPACITY SURVIVES IN THE MAJORANT.  Two Krein-gamma-decodable tokens (witnesses in the
  majorant unit ball) have gamma-separated frames.  The proof is the Euclidean separation argument run
  on the J-transformed witnesses @{term "J rv"}, @{term "J rw"}; the majorant isometry @{term J}
  keeps them in the unit ball, so the bias cancels and Cauchy-Schwarz finishes exactly as in
  DecodeCapacity.margin_pair_separation.\<close>
theorem margin_pair_separation_k:
  fixes U :: "'v \<Rightarrow> 'a::real_inner"
  assumes v: "gdecodes_k J U b \<gamma> v rv" and w: "gdecodes_k J U b \<gamma> w rw"
      and nv: "norm rv \<le> 1" and nw: "norm rw \<le> 1" and vw: "v \<noteq> w"
      and iso: "\<And>x. norm (J x) = norm x"
  shows "\<gamma> \<le> norm (U v - U w)"
proof -
  have v1: "inner (J rv) (U w) + b w + \<gamma> \<le> inner (J rv) (U v) + b v"
    using v[unfolded gdecodes_k_def kinner_def, rule_format, of w] vw by simp
  have w1: "inner (J rw) (U v) + b v + \<gamma> \<le> inner (J rw) (U w) + b w"
    using w[unfolded gdecodes_k_def kinner_def, rule_format, of v] vw by simp
  have eq: "inner (J rv - J rw) (U v - U w)
            = (inner (J rv) (U v) - inner (J rv) (U w)) + (inner (J rw) (U w) - inner (J rw) (U v))"
    by (simp add: inner_diff_left inner_diff_right algebra_simps)
  have key: "2 * \<gamma> \<le> inner (J rv - J rw) (U v - U w)"
    using v1 w1 eq by linarith
  have cs: "inner (J rv - J rw) (U v - U w) \<le> norm (J rv - J rw) * norm (U v - U w)"
    by (rule norm_cauchy_schwarz)
  have nrw: "norm (J rv - J rw) \<le> 2"
    using nv nw iso[of rv] iso[of rw] norm_triangle_ineq4[of "J rv" "J rw"] by linarith
  have b2: "norm (J rv - J rw) * norm (U v - U w) \<le> 2 * norm (U v - U w)"
    by (rule mult_right_mono[OF nrw norm_ge_zero])
  from key cs b2 show ?thesis by linarith
qed

text \<open>OPEN: a usable capacity bound in the genuinely INDEFINITE ball {r. [r,r] <= 1} (not the majorant
  ball) for a Pontryagin frame -- presumably a bound in the spacelike dimension p plus a q-dependent
  count of unbounded (timelike) escape directions.  margin_pair_separation_k only covers the majorant
  ball; the indefinite-ball case collapses (KreinWelch.indefinite_ball_unbounded).\<close>

text \<open>OPEN/empirical: whether a real transformer pairing (e.g. the QK form, whose symmetric part is
  generically indefinite) carries non-trivial signature -- a fieldrun measurement, not a theorem here.\<close>

end
