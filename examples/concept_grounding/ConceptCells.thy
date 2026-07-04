(*
  ConceptCells.thy -- C1: concept lattice == hyperplane-arrangement face structure == decoder cells.

  The central grounding theorem. K concepts are closed half-spaces H_c = {r. b_c <= <u_c, r>} in
  residual space; the membership map sigma sends a residual to its bit-vector of memberships. We prove
  the three-way correspondence the concept-as-hyperplane bridge rests on:

    (a) the fibers of sigma are exactly the cells of the arrangement: they partition the space, each is
        the stated intersection of half-spaces and open complements, and each is CONVEX;
    (b) the FCA context (residuals, concepts, "r in H_c") has the Galois-connection structure of formal
        concept analysis, the extent/intent maps are antitone with the closure property, formal concepts
        are ordered ANTI-isomorphically (extents by subset iff intents by superset) -- and the intent of
        a nonempty cell recovers exactly its sign vector, so the concept lattice sees the cells;
    (c) the argmax decoder r |-> argmax_v <U_v, r> is piecewise-constant on the cells of its
        difference arrangement, and whenever the concept family contains the decision hyperplanes
        (u_c = U_v - U_w, b_c = 0) the concept arrangement REFINES the decoder: same cell => same decode.

  This generalizes tropical/DecodeCapacity.thy's cell reasoning to the concept arrangement. The full
  polyhedral face-lattice order (faces ordered by closure containment) is NOT formalized -- the
  correspondence proved is at the level of cells/sign-vectors and the FCA order; that scoping is stated
  in RESULTS.md. Domain: finite concept sets, linear readout, half-space membership; real-LLM bridge open.
*)
theory ConceptCells
  imports "HOL-Analysis.Analysis"
begin

subsection \<open>The arrangement and the membership map\<close>

text \<open>Concept c's half-space (closed side).\<close>
definition Hspace :: "('c \<Rightarrow> 'a::real_inner) \<Rightarrow> ('c \<Rightarrow> real) \<Rightarrow> 'c \<Rightarrow> 'a set" where
  "Hspace u b c = {r. b c \<le> u c \<bullet> r}"

text \<open>The membership (sign-vector) map sigma : residual => concept bit-vector.\<close>
definition sgnvec :: "('c \<Rightarrow> 'a::real_inner) \<Rightarrow> ('c \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool" where
  "sgnvec u b r c \<longleftrightarrow> b c \<le> u c \<bullet> r"

text \<open>The cell of a sign pattern s: the fiber of sigma over s, relative to the concept set C.\<close>
definition cell :: "'c set \<Rightarrow> ('c \<Rightarrow> 'a::real_inner) \<Rightarrow> ('c \<Rightarrow> real) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> 'a set" where
  "cell C u b s = {r. \<forall>c\<in>C. sgnvec u b r c = s c}"

lemma sgnvec_iff_mem: "sgnvec u b r c \<longleftrightarrow> r \<in> Hspace u b c"
  unfolding sgnvec_def Hspace_def by simp

subsection \<open>(a) The fibers of sigma are the cells of the arrangement\<close>

text \<open>Every residual lies in the cell of its own sign vector: the cells cover the space.\<close>
lemma cell_self: "r \<in> cell C u b (sgnvec u b r)"
  unfolding cell_def by simp

lemma cells_cover: "(\<Union>s. cell C u b s) = UNIV"
proof
  show "(\<Union>s. cell C u b s) \<subseteq> UNIV" by simp
  show "UNIV \<subseteq> (\<Union>s. cell C u b s)"
  proof
    fix r :: 'a
    show "r \<in> (\<Union>s. cell C u b s)"
      using cell_self[of r C u b] by (intro UN_I[OF UNIV_I])
  qed
qed

text \<open>Two cells meet only if their sign patterns agree on C: distinct patterns give disjoint fibers.
      Together with the cover, the (nonempty) cells PARTITION residual space.\<close>
lemma cells_disjoint:
  assumes "c \<in> C" and "s c \<noteq> t c"
  shows "cell C u b s \<inter> cell C u b t = {}"
  using assms unfolding cell_def by auto

lemma cell_fiber:
  assumes "r \<in> cell C u b s" and "r \<in> cell C u b t" and "c \<in> C"
  shows "s c = t c"
  using assms unfolding cell_def by auto

text \<open>A cell is exactly the intersection of the half-spaces its pattern turns on with the (open)
      complements of those it turns off -- the face of the arrangement in its stated form.\<close>
lemma cell_as_intersection:
  "cell C u b s =
     (\<Inter>c\<in>{c \<in> C. s c}. Hspace u b c) \<inter> (\<Inter>c\<in>{c \<in> C. \<not> s c}. - Hspace u b c)"
  unfolding cell_def sgnvec_def Hspace_def by auto

text \<open>Each cell is convex: closed half-spaces and open half-spaces are convex and convexity is
      stable under intersection. (Relative openness/closure structure is not formalized; see header.)\<close>
lemma cell_convex: "convex (cell C u b s)"
proof -
  have on: "convex (\<Inter>c\<in>{c \<in> C. s c}. Hspace u b c)"
  proof (rule convex_INT)
    fix c show "convex (Hspace u b c)"
      unfolding Hspace_def by (rule convex_halfspace_ge)
  qed
  have off: "convex (\<Inter>c\<in>{c \<in> C. \<not> s c}. - Hspace u b c)"
  proof (rule convex_INT)
    fix c
    have "- Hspace u b c = {r. u c \<bullet> r < b c}"
      unfolding Hspace_def by auto
    thus "convex (- Hspace u b c)" by (simp add: convex_halfspace_lt)
  qed
  show ?thesis
    unfolding cell_as_intersection by (rule convex_Int[OF on off])
qed

subsection \<open>(b) The FCA structure of the half-space context\<close>

text \<open>The formal context: objects = residuals, attributes = concepts in C, incidence = membership.
      intent X = the concepts every residual of X satisfies; extent B = the residuals satisfying
      every concept of B.\<close>
definition intent :: "'c set \<Rightarrow> ('c \<Rightarrow> 'a::real_inner) \<Rightarrow> ('c \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> 'c set" where
  "intent C u b X = {c \<in> C. \<forall>r\<in>X. r \<in> Hspace u b c}"

definition extent :: "('c \<Rightarrow> 'a::real_inner) \<Rightarrow> ('c \<Rightarrow> real) \<Rightarrow> 'c set \<Rightarrow> 'a set" where
  "extent u b B = {r. \<forall>c\<in>B. r \<in> Hspace u b c}"

text \<open>The Galois connection: X is inside the extent of B iff B is inside the intent of X.\<close>
lemma fca_galois:
  assumes "B \<subseteq> C"
  shows "X \<subseteq> extent u b B \<longleftrightarrow> B \<subseteq> intent C u b X"
  using assms unfolding extent_def intent_def by auto

lemma intent_antitone: "X \<subseteq> Y \<Longrightarrow> intent C u b Y \<subseteq> intent C u b X"
  unfolding intent_def by auto

lemma extent_antitone: "B \<subseteq> B' \<Longrightarrow> extent u b B' \<subseteq> extent u b B"
  unfolding extent_def by auto

lemma fca_closure_extensive: "X \<subseteq> extent u b (intent C u b X)"
  unfolding extent_def intent_def by auto

lemma fca_intent_extensive: "B \<inter> C \<subseteq> intent C u b (extent u b B)"
  unfolding extent_def intent_def by auto

text \<open>Every extent is an intersection of closed half-spaces: a closed convex polyhedral set.\<close>
lemma extent_convex: "convex (extent u b B)"
proof -
  have eq: "extent u b B = (\<Inter>c\<in>B. Hspace u b c)" unfolding extent_def by auto
  have "convex (\<Inter>c\<in>B. Hspace u b c)"
  proof (rule convex_INT)
    fix c show "convex (Hspace u b c)"
      unfolding Hspace_def by (rule convex_halfspace_ge)
  qed
  thus ?thesis by (simp add: eq)
qed

text \<open>The core of the fundamental theorem of FCA, for this context: formal concepts
      (X_i, B_i) -- extent/intent fixed pairs -- are ordered anti-isomorphically:
      extents by inclusion iff intents by REVERSE inclusion.\<close>
theorem concept_anti_iso:
  assumes c1: "X1 = extent u b B1" "B1 = intent C u b X1"
      and c2: "X2 = extent u b B2" "B2 = intent C u b X2"
  shows "X1 \<subseteq> X2 \<longleftrightarrow> B2 \<subseteq> B1"
proof
  assume "X1 \<subseteq> X2"
  hence "intent C u b X2 \<subseteq> intent C u b X1" by (rule intent_antitone)
  thus "B2 \<subseteq> B1" using c1(2) c2(2) by simp
next
  assume "B2 \<subseteq> B1"
  hence "extent u b B1 \<subseteq> extent u b B2" by (rule extent_antitone)
  thus "X1 \<subseteq> X2" using c1(1) c2(1) by simp
qed

text \<open>The bridge between (a) and (b): the FCA intent of a nonempty cell recovers exactly the ON-set
      of its sign vector. The concept lattice and the arrangement carry the same information.\<close>
theorem cell_intent_recovers_sign:
  assumes ne: "cell C u b s \<noteq> {}"
  shows "intent C u b (cell C u b s) = {c \<in> C. s c}"
proof
  show "{c \<in> C. s c} \<subseteq> intent C u b (cell C u b s)"
    unfolding intent_def cell_def sgnvec_def Hspace_def by auto
next
  show "intent C u b (cell C u b s) \<subseteq> {c \<in> C. s c}"
  proof
    fix c assume c: "c \<in> intent C u b (cell C u b s)"
    obtain r where r: "r \<in> cell C u b s" using ne by auto
    have "r \<in> Hspace u b c" and "c \<in> C" using c r unfolding intent_def by auto
    hence "sgnvec u b r c" by (simp add: sgnvec_iff_mem)
    thus "c \<in> {c \<in> C. s c}" using r \<open>c \<in> C\<close> unfolding cell_def by auto
  qed
qed

text \<open>Realized sign patterns and cells correspond bijectively: equal nonempty cells force equal
      patterns on C -- the object part of the anti-isomorphism is well-defined and injective.\<close>
lemma cell_inj_on_realized:
  assumes "cell C u b s \<noteq> {}" and "cell C u b s = cell C u b t" and "c \<in> C"
  shows "s c = t c"
  using assms cell_fiber by (metis all_not_in_conv)

subsection \<open>(c) The argmax decoder is piecewise-constant on the cells\<close>

text \<open>The argmax decoder over readout directions U: the set of maximizing vocabulary items.\<close>
definition amax :: "'v set \<Rightarrow> ('v \<Rightarrow> 'a::real_inner) \<Rightarrow> 'a \<Rightarrow> 'v set" where
  "amax V U r = {v \<in> V. \<forall>w\<in>V. U w \<bullet> r \<le> U v \<bullet> r}"

text \<open>Two residuals with the same sign pattern on every decision difference U_v - U_w decode
      identically: the decoder is piecewise-constant on the cells of its difference arrangement.\<close>
lemma amax_piecewise_constant:
  assumes agree: "\<And>v w. v \<in> V \<Longrightarrow> w \<in> V \<Longrightarrow>
                    (0 \<le> (U v - U w) \<bullet> r) \<longleftrightarrow> (0 \<le> (U v - U w) \<bullet> r')"
  shows "amax V U r = amax V U r'"
proof -
  have iff: "(U w \<bullet> r \<le> U v \<bullet> r) \<longleftrightarrow> (U w \<bullet> r' \<le> U v \<bullet> r')" if "v \<in> V" "w \<in> V" for v w
    using agree[OF that] by (simp add: inner_diff_left)
  show ?thesis
  proof
    show "amax V U r \<subseteq> amax V U r'"
      unfolding amax_def using iff by auto
    show "amax V U r' \<subseteq> amax V U r"
      unfolding amax_def using iff by auto
  qed
qed

text \<open>When the concept family C contains every decision hyperplane (u_c = U_v - U_w with b_c = 0),
      the concept arrangement refines the decoder's cells: residuals in the SAME concept cell decode
      identically. The membership bit-vector determines the decode -- (a)/(b)'s lattice is fine
      enough to carry the tropical decision structure.\<close>
theorem concept_refines_decoder:
  assumes cov: "\<And>v w. v \<in> V \<Longrightarrow> w \<in> V \<Longrightarrow> \<exists>c\<in>C. u c = U v - U w \<and> b c = 0"
      and s1: "r \<in> cell C u b s" and s2: "r' \<in> cell C u b s"
  shows "amax V U r = amax V U r'"
proof (rule amax_piecewise_constant)
  fix v w assume vw: "v \<in> V" "w \<in> V"
  obtain c where c: "c \<in> C" "u c = U v - U w" "b c = 0" using cov[OF vw] by auto
  have "sgnvec u b r c = s c" and "sgnvec u b r' c = s c"
    using s1 s2 c(1) unfolding cell_def by auto
  thus "(0 \<le> (U v - U w) \<bullet> r) \<longleftrightarrow> (0 \<le> (U v - U w) \<bullet> r')"
    using c(2,3) unfolding sgnvec_def by simp
qed

end
