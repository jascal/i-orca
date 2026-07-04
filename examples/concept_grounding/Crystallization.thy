(*
  Crystallization.thy -- C2: crystallization exactness (when a rule collapses to one concept).

  A rule is a polyhedral region rho = region u b S = the intersection of its constraint half-spaces.
  "Crystallizing" the rule into a single concept direction replaces the indicator 1_rho by a single
  half-space indicator [<w,r> >= t]. This theory proves when that collapse is exact:

    * EXACT DIRECTION: if the other constraints are jointly redundant on the rule -- the region
      already equals one constraint's half-space -- the collapse is exact (trivially, and the only
      way it can be: the region IS a half-space).
    * OBSTRUCTION (the load-bearing part): a half-space has a CONVEX complement. So the moment two
      violating points straddle the region -- q1, q2 outside rho with their midpoint inside -- NO
      half-space indicator [<w,r> >= t] equals 1_rho: the collapse is inexact, whatever (w, t).
      An essential constraint always supplies violating points (essential_witness); two essential
      constraints with a straddling witness pair block the collapse (two_essential_facets_block).
    * WORKED INSTANCE: the quadrant {r. 0 <= r.i} \<inter> {r. 0 <= r.j} (i, j distinct basis directions)
      has both constraints essential, admits the straddling pair q1 = j - i, q2 = i - j with
      midpoint 0, and hence provably equals NO single half-space -- the canonical inexact
      crystallization, kernel-checked with concrete witnesses.

  HONEST SCOPE. The conjecture's "iff <= 1 essential facet" needs, for its hard direction, the
  supporting-hyperplane construction of straddling witnesses from bare essentialness plus
  non-parallelism; that geometric step is NOT formalized here -- the obstruction theorem takes the
  witness pair as its stated domain, the instance exhibits them concretely, and the quantitative
  "margin deficit" of the best approximating half-space stays `open`. The MDL keep-vs-collapse
  decision thresholds on exactly the dichotomy proved: complement-convexity of the firing region.
*)
theory Crystallization
  imports "HOL-Analysis.Analysis"
begin

subsection \<open>Rules as polyhedral regions\<close>

text \<open>The firing region of a rule: the intersection of its constraint half-spaces over S.\<close>
definition region :: "('c \<Rightarrow> 'a::real_inner) \<Rightarrow> ('c \<Rightarrow> real) \<Rightarrow> 'c set \<Rightarrow> 'a set" where
  "region u b S = (\<Inter>c\<in>S. {r. b c \<le> u c \<bullet> r})"

lemma region_convex: "convex (region u b S)"
  unfolding region_def by (blast intro: convex_INT convex_halfspace_ge)

lemma region_antimono: "S' \<subseteq> S \<Longrightarrow> region u b S \<subseteq> region u b S'"
  unfolding region_def by auto

text \<open>A single-constraint rule IS a half-space: the degenerate exact case.\<close>
lemma region_single: "region u b {c} = {r. b c \<le> u c \<bullet> r}"
  unfolding region_def by auto

subsection \<open>The exact direction: joint redundancy collapses exactly\<close>

text \<open>If every other constraint is jointly redundant on the rule -- dropping them all changes
      nothing -- the rule region is exactly one half-space and crystallization is exact.\<close>
theorem redundant_collapse_exact:
  assumes "c \<in> S" and "region u b S = region u b {c}"
  shows "\<exists>w t. region u b S = {r. t \<le> w \<bullet> r}"
proof -
  have "region u b S = {r. b c \<le> u c \<bullet> r}" using assms(2) region_single by simp
  thus ?thesis by blast
qed

subsection \<open>The obstruction: half-space complements are convex\<close>

text \<open>The complement of a (closed) half-space is convex -- the fact every failed collapse
      reduces to.\<close>
lemma halfspace_complement_convex: "convex (- {r. t \<le> w \<bullet> (r::'a::real_inner)})"
proof -
  have "- {r. t \<le> w \<bullet> (r::'a)} = {r. w \<bullet> r < t}" by auto
  thus ?thesis by (simp add: convex_halfspace_lt)
qed

text \<open>The midpoint obstruction, for ANY candidate set: two points outside R whose midpoint is
      inside R rule out every half-space representation of R. (Applied to R = region u b S, this is
      the inexactness of crystallization; but the argument is representation-independent.)\<close>
theorem midpoint_blocks_collapse:
  fixes R :: "'a::real_inner set"
  assumes q1: "q1 \<notin> R" and q2: "q2 \<notin> R" and mid: "midpoint q1 q2 \<in> R"
  shows "\<nexists>w t. R = {r. t \<le> w \<bullet> r}"
proof
  assume "\<exists>w t. R = {r. t \<le> w \<bullet> r}"
  then obtain w t where Rht: "R = {r. t \<le> w \<bullet> r}" by auto
  have "w \<bullet> q1 < t" and "w \<bullet> q2 < t" using q1 q2 Rht by auto
  hence "w \<bullet> midpoint q1 q2 < t"
    unfolding midpoint_def by (simp add: inner_add_right)
  thus False using mid Rht by auto
qed

subsection \<open>Essential constraints supply the witnesses\<close>

text \<open>A constraint is essential when dropping it strictly grows the region.\<close>
definition essential :: "('c \<Rightarrow> 'a::real_inner) \<Rightarrow> ('c \<Rightarrow> real) \<Rightarrow> 'c set \<Rightarrow> 'c \<Rightarrow> bool" where
  "essential u b S c \<longleftrightarrow> c \<in> S \<and> region u b (S - {c}) \<noteq> region u b S"

text \<open>An essential constraint always has a witness: a point satisfying every OTHER constraint but
      violating the region -- the "point near the facet, just outside" of the conjecture.\<close>
lemma essential_witness:
  assumes "essential u b S c"
  shows "\<exists>q. q \<in> region u b (S - {c}) \<and> q \<notin> region u b S"
proof -
  have "region u b S \<subseteq> region u b (S - {c})" by (rule region_antimono) auto
  thus ?thesis using assms unfolding essential_def by blast
qed

text \<open>Two essential constraints whose witnesses straddle the region block the collapse: the rule
      indicator is NOT any single half-space indicator. (The witnessed-straddling hypothesis is the
      stated domain; constructing it from bare essentialness + non-parallel facets is the open
      supporting-hyperplane step recorded in the header.)\<close>
theorem two_essential_facets_block:
  assumes c1: "essential u b S c1" and c2: "essential u b S c2"
      and w1: "q1 \<in> region u b (S - {c1})" "q1 \<notin> region u b S"
      and w2: "q2 \<in> region u b (S - {c2})" "q2 \<notin> region u b S"
      and mid: "midpoint q1 q2 \<in> region u b S"
  shows "\<nexists>w t. region u b S = {r. t \<le> w \<bullet> r}"
  by (rule midpoint_blocks_collapse[OF w1(2) w2(2) mid])

subsection \<open>The worked instance: a quadrant is not a half-space\<close>

text \<open>The two-constraint rule over distinct basis directions i, j: the quadrant.\<close>
definition quadrant_dirs :: "'a::euclidean_space \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "quadrant_dirs i j c = (if c = 0 then i else j)"

lemma quadrant_region:
  "region (quadrant_dirs i j) (\<lambda>_. 0) {0, 1} = {r. 0 \<le> i \<bullet> r} \<inter> {r. 0 \<le> j \<bullet> r}"
  unfolding region_def quadrant_dirs_def by auto

text \<open>Both quadrant constraints are essential: dropping either admits the witness that violates
      exactly it.\<close>
lemma quadrant_essential:
  fixes i j :: "'a::euclidean_space"
  assumes iB: "i \<in> Basis" and jB: "j \<in> Basis" and ij: "i \<noteq> j"
  shows "essential (quadrant_dirs i j) (\<lambda>_. 0) {0, 1} 0"
    and "essential (quadrant_dirs i j) (\<lambda>_. 0) {0, 1} 1"
proof -
  have ii: "i \<bullet> i = 1" and jj: "j \<bullet> j = 1" and ij0: "i \<bullet> j = 0" and ji0: "j \<bullet> i = 0"
    using iB jB ij by (auto simp: inner_Basis)
  have set0: "({0, 1} :: nat set) - {0} = {1}" and set1: "({0, 1} :: nat set) - {1} = {0}"
    by auto
  have m1': "j - i \<in> region (quadrant_dirs i j) (\<lambda>_. 0) {1}"
    unfolding region_def quadrant_dirs_def by (simp add: inner_diff_right jj ji0)
  have m1: "j - i \<in> region (quadrant_dirs i j) (\<lambda>_. 0) ({0, 1} - {0})"
    using m1' unfolding set0 .
  have n1: "j - i \<notin> region (quadrant_dirs i j) (\<lambda>_. 0) {0, 1}"
    unfolding region_def quadrant_dirs_def by (auto simp: inner_diff_right ii ij0)
  have m2': "i - j \<in> region (quadrant_dirs i j) (\<lambda>_. 0) {0}"
    unfolding region_def quadrant_dirs_def by (simp add: inner_diff_right ii ij0)
  have m2: "i - j \<in> region (quadrant_dirs i j) (\<lambda>_. 0) ({0, 1} - {1})"
    using m2' unfolding set1 .
  have n2: "i - j \<notin> region (quadrant_dirs i j) (\<lambda>_. 0) {0, 1}"
    unfolding region_def quadrant_dirs_def by (auto simp: inner_diff_right jj ji0)
  show "essential (quadrant_dirs i j) (\<lambda>_. 0) {0, 1} 0"
    unfolding essential_def using m1 n1 by blast
  show "essential (quadrant_dirs i j) (\<lambda>_. 0) {0, 1} 1"
    unfolding essential_def using m2 n2 by blast
qed

text \<open>The quadrant equals NO single half-space: crystallizing a genuinely two-facet rule into one
      concept direction is provably inexact. Witnesses: q1 = j - i and q2 = i - j, each violating
      exactly one facet, with midpoint 0 inside the rule.\<close>
theorem quadrant_not_halfspace:
  fixes i j :: "'a::euclidean_space"
  assumes iB: "i \<in> Basis" and jB: "j \<in> Basis" and ij: "i \<noteq> j"
  shows "\<nexists>w t. region (quadrant_dirs i j) (\<lambda>_. 0) {0, 1} = {r. t \<le> w \<bullet> r}"
proof (rule midpoint_blocks_collapse)
  have ii: "i \<bullet> i = 1" and jj: "j \<bullet> j = 1" and ij0: "i \<bullet> j = 0" and ji0: "j \<bullet> i = 0"
    using iB jB ij by (auto simp: inner_Basis)
  show "j - i \<notin> region (quadrant_dirs i j) (\<lambda>_. 0) {0, 1}"
    unfolding region_def quadrant_dirs_def by (auto simp: inner_diff_right ii ij0)
  show "i - j \<notin> region (quadrant_dirs i j) (\<lambda>_. 0) {0, 1}"
    unfolding region_def quadrant_dirs_def by (auto simp: inner_diff_right jj ji0)
  show "midpoint (j - i) (i - j) \<in> region (quadrant_dirs i j) (\<lambda>_. 0) {0, 1}"
    unfolding midpoint_def region_def quadrant_dirs_def by (simp add: algebra_simps)
qed

end
