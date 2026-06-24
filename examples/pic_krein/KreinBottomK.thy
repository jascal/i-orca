(*
  KreinBottomK.thy -- the BOTTOM-K (min-plus) decode certificate, dual to tropical/HeadTail.thy.

  PIC's top-K decode is the max-plus aggregate  decode L S = Max_{v in S} L v  (the winner / most
  likely token).  Its dual is the BOTTOM-K decode  codecode L S = Min_{v in S} L v  (the loser / most
  SUPPRESSED token) -- the min-plus / "anti-tropical" reading, which in the PIC semiring family is the
  NEGATIVE-TEMPERATURE limit:  T log(e^{a/T}+e^{b/T}) -> min(a,b) as T -> 0^-.

  WHY IT BELONGS WITH KREIN.  Bottom-K is exactly what a suppression channel reads out, and in a Krein
  space the fundamental symmetry gives suppression a structural home: the canonical top<->bottom
  involution is FRAME NEGATION (negate U, or equivalently the timelike subspace), and that holds for
  ANY J (it is metric-light -- only inner-product linearity).  This file proves:

    Min-plus semiring (the bottom-K aggregator):
      comin_commute / comin_idem / comin_assoc : (min, +) is the dual tropical semiring sum.
      comin_as_neg_max                         : min a b = - max (-a) (-b) -- bottom-K is top-K of the
                                                 negated logits (the algebraic heart of the duality).

    The BOTTOM-K HEAD/TAIL CERTIFICATE (dual of HeadTail.thy, verbatim with min for max, <= flipped):
      codecode_partition         : the bottom-decode splits over the partition (min over H u T).
      cohead_certifies_codecode  : a CO-HEAD whose minimum is <= the tail's reproduces the bottom-K
                                   decode exactly (it contains the global minimum).
      cohead_argmin_in_cohead    : ... and the argMIN lies in the co-head.
      cotail_is_residue          : when the co-head does NOT dominate from below, the most-suppressed
                                   token is in the tail -- the explicit bottom-K residue.

    The Krein bridge (top<->bottom = frame negation, any J):
      kinner_neg_frame           : negating the frame negates the incidence, [r, -U_v] = - [r, U_v].
      bottomk_eq_topk_neg_frame  : codecode over U = - (decode over -U) -- bottom-K IS top-K of the
                                   negated frame.

  Tag (pic discipline): all [proved] here.  The claim that a trained model SHOULD expose bottom-K via a
  Krein suppression subspace (signature q = dim K_-) is [open/speculative] -- a design statement, see
  PROPOSAL.md.  Note the genuine tension (PROPOSAL.md sec 3): the top/bottom asymmetry that makes Krein
  interesting lives in the INDEFINITE ball (KreinWelch.indefinite_ball_unbounded), but a JOINT top u
  bottom certificate needs the compact MAJORANT ball, where the duality below is exactly symmetric.
*)
theory KreinBottomK
  imports KreinDecode
begin

text \<open>The top-K (max-plus) and bottom-K (min-plus) decode values over a candidate set.\<close>
abbreviation decode :: "('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> real" where
  "decode L S \<equiv> Max (L ` S)"
abbreviation codecode :: "('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> real" where
  "codecode L S \<equiv> Min (L ` S)"

subsection \<open>The min-plus semiring sum (the bottom-K aggregator)\<close>

definition comin :: "real \<Rightarrow> real \<Rightarrow> real" where "comin a b = min a b"

lemma comin_commute: "comin a b = comin b a" by (simp add: comin_def min.commute)
lemma comin_idem:    "comin a a = a"         by (simp add: comin_def)
lemma comin_assoc:   "comin (comin a b) c = comin a (comin b c)" by (simp add: comin_def)

text \<open>Bottom-K is top-K of the negated logits: the min-plus sum is the max-plus sum conjugated by
  negation.  This is why no new frame is needed -- read the same monomials with the dual aggregator.\<close>
lemma comin_as_neg_max: "comin a b = - max (- a) (- b)"
  by (simp add: comin_def min_def max_def)

subsection \<open>The bottom-K head/tail certificate (dual of HeadTail.thy)\<close>

text \<open>(1) The bottom-decode splits over the head/tail partition, with the min-plus sum @{const comin}.\<close>
lemma codecode_partition:
  assumes "finite H" "finite T" "H \<noteq> {}" "T \<noteq> {}"
  shows "codecode L (H \<union> T) = comin (codecode L H) (codecode L T)"
proof -
  have "finite (L ` H)" "finite (L ` T)" "L ` H \<noteq> {}" "L ` T \<noteq> {}" using assms by auto
  hence "Min (L ` H \<union> L ` T) = min (codecode L H) (codecode L T)" by (simp add: Min_Un)
  thus ?thesis by (simp add: comin_def image_Un)
qed

text \<open>(2) CO-HEAD CERTIFICATE: when the co-head's minimum is at or below the tail's, the full bottom-K
  decode equals the co-head's -- the co-head contains the most-suppressed token.\<close>
theorem cohead_certifies_codecode:
  assumes f: "finite H" "finite T" and ne: "H \<noteq> {}" "T \<noteq> {}"
      and dom: "codecode L H \<le> codecode L T"
  shows "codecode L (H \<union> T) = codecode L H"
  using codecode_partition[OF f ne, of L] dom by (simp add: comin_def min.absorb1)

text \<open>... and the argMIN then lies in the CO-HEAD: a co-head token attains the bottom-K decode and is
  <= every candidate.\<close>
theorem cohead_argmin_in_cohead:
  assumes f: "finite H" "finite T" and ne: "H \<noteq> {}" "T \<noteq> {}"
      and dom: "codecode L H \<le> codecode L T"
  shows "\<exists>h\<in>H. L h = codecode L (H \<union> T) \<and> (\<forall>v\<in>H \<union> T. L h \<le> L v)"
proof -
  have eq: "codecode L (H \<union> T) = codecode L H" using f ne dom cohead_certifies_codecode by blast
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
  in the tail -- the explicit bottom-K residue, dual to HeadTail.tail_is_residue.\<close>
theorem cotail_is_residue:
  assumes f: "finite H" "finite T" and ne: "H \<noteq> {}" "T \<noteq> {}"
      and notdom: "codecode L T < codecode L H"
  shows "\<exists>t\<in>T. L t = codecode L (H \<union> T) \<and> (\<forall>h\<in>H. L t < L h)"
proof -
  have part: "codecode L (H \<union> T) = min (codecode L H) (codecode L T)"
    using codecode_partition[OF f ne, of L] by (simp add: comin_def)
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

subsection \<open>The Krein bridge: bottom-K is top-K of the negated frame (any J)\<close>

text \<open>Negating the frame negates the incidence -- the metric-light fact (inner-product linearity only,
  no assumption on J) behind the top<->bottom involution.\<close>
lemma kinner_neg_frame: "kinner J r (- (U v)) = - kinner J r (U v)"
  by (simp add: kinner_def inner_minus_right)

text \<open>The Min of an image is minus the Max of the negated image.\<close>
lemma Max_uminus_image:
  fixes A :: "real set"
  assumes "finite A" and ne: "A \<noteq> {}"
  shows "Max (uminus ` A) = - Min A"
proof (rule Max_eqI)
  show "finite (uminus ` A)" using assms by simp
next
  fix a assume "a \<in> uminus ` A"
  then obtain b where b: "b \<in> A" "a = - b" by auto
  have "Min A \<le> b" using b(1) assms by (simp add: Min_le)
  thus "a \<le> - Min A" using b(2) by simp
next
  show "- Min A \<in> uminus ` A" using Min_in[OF assms] by force
qed

lemma Min_eq_neg_Max_image:
  fixes g :: "'b \<Rightarrow> real"
  assumes "finite S" "S \<noteq> {}"
  shows "Min (g ` S) = - Max ((\<lambda>x. - g x) ` S)"
proof -
  have fin: "finite (g ` S)" using assms(1) by simp
  have ne: "g ` S \<noteq> {}" using assms(2) by simp
  have "(\<lambda>x. - g x) ` S = uminus ` (g ` S)" by (simp add: image_image)
  hence "Max ((\<lambda>x. - g x) ` S) = Max (uminus ` (g ` S))" by simp
  also have "\<dots> = - Min (g ` S)" by (rule Max_uminus_image[OF fin ne])
  finally show ?thesis by simp
qed

text \<open>BOTTOM-K = TOP-K OF THE NEGATED FRAME.  The bottom-K (min-plus) decode read off the frame U is
  minus the top-K (max-plus) decode read off the negated frame -U -- the canonical top<->bottom
  involution, holding for every fundamental symmetry J (metric-light).\<close>
corollary bottomk_eq_topk_neg_frame:
  assumes "finite S" "S \<noteq> {}"
  shows "codecode (\<lambda>v. kinner J r (U v)) S = - decode (\<lambda>v. kinner J r (- (U v))) S"
proof -
  have img: "(\<lambda>x. - kinner J r (U x)) ` S = (\<lambda>v. kinner J r (- (U v))) ` S"
    by (simp add: kinner_neg_frame)
  have "codecode (\<lambda>v. kinner J r (U v)) S = - Max ((\<lambda>x. - kinner J r (U x)) ` S)"
    using assms by (rule Min_eq_neg_Max_image)
  also have "\<dots> = - decode (\<lambda>v. kinner J r (- (U v))) S" using img by simp
  finally show ?thesis .
qed

end
