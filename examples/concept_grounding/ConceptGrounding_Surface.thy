theory ConceptGrounding_Surface
  imports Consolidation ConceptCells ComputedRank Compositional Crystallization Gauge
begin

text \<open>C4(i), one step: a masked update leaves every frozen concept's membership function identical. Cites `frozen_membership_invariant`.\<close>
theorem frozenmembershipinvariant:
  shows "masked F u b u' b' \<Longrightarrow> c \<in> F \<Longrightarrow> fires u' b' c = fires u b c"
proof -
  show "masked F u b u' b' \<Longrightarrow> c \<in> F \<Longrightarrow> fires u' b' c = fires u b c" by (rule frozen_membership_invariant)
qed

text \<open>C4(i), whole trajectory: any run of masked training steps leaves frozen memberships at their initial state -- invariance under ALL subsequent training. Cites `frozen_membership_trajectory`.\<close>
theorem frozenmembershiptrajectory:
  shows "(\<And>n. n < N \<Longrightarrow> masked F (u n) (b n) (u (Suc n)) (b (Suc n))) \<Longrightarrow> c \<in> F \<Longrightarrow> fires (u N) (b N) c = fires (u 0) (b 0) c"
proof -
  show "(\<And>n. n < N \<Longrightarrow> masked F (u n) (b n) (u (Suc n)) (b (Suc n))) \<Longrightarrow> c \<in> F \<Longrightarrow> fires (u N) (b N) c = fires (u 0) (b 0) c" by (rule frozen_membership_trajectory)
qed

text \<open>C4(ii): every decision that reads only the frozen memberships returns the same value on every residual after any masked update -- zero forgetting, exactly. Cites `frozen_decision_preserved`.\<close>
theorem frozendecisionpreserved:
  shows "masked F u b u' b' \<Longrightarrow> D (restrict (\<lambda>c. fires u' b' c r) F) = D (restrict (\<lambda>c. fires u b c r) F)"
proof -
  show "masked F u b u' b' \<Longrightarrow> D (restrict (\<lambda>c. fires u' b' c r) F) = D (restrict (\<lambda>c. fires u b c r) F)" by (rule frozen_decision_preserved)
qed

text \<open>C4(iii): the update of the whole concept frame vanishes on F, so it spans at most card (K - F) dimensions -- the reachable change is confined to the plastic span. Cites `reachable_change_dim`.\<close>
theorem reachablechangedim:
  shows "finite K \<Longrightarrow> masked F (u::'c \<Rightarrow> 'a::euclidean_space) b u' b' \<Longrightarrow> F \<subseteq> K \<Longrightarrow> dim (span ((\<lambda>c. u' c - u c) ` K)) \<le> card (K - F)"
proof -
  show "finite K \<Longrightarrow> masked F (u::'c \<Rightarrow> 'a::euclidean_space) b u' b' \<Longrightarrow> F \<subseteq> K \<Longrightarrow> dim (span ((\<lambda>c. u' c - u c) ` K)) \<le> card (K - F)" by (rule reachable_change_dim)
qed

text \<open>C4(iii), boundary form: any bank of directions over the plastic set spans at most card P dimensions -- new-task decision boundaries live in a subspace of dimension at most the plastic budget. Cites `plastic_boundary_dim`.\<close>
theorem plasticboundarydim:
  shows "finite P \<Longrightarrow> dim (span ((u'::'c \<Rightarrow> 'a::euclidean_space) ` P)) \<le> card P"
proof -
  show "finite P \<Longrightarrow> dim (span ((u'::'c \<Rightarrow> 'a::euclidean_space) ` P)) \<le> card P" by (rule plastic_boundary_dim)
qed

text \<open>C4 corollary, the hard tradeoff: retain-rank + learn-rank <= K. Freezing a k-dim frame preserves it exactly at the cost of capping new learning at K - k dimensions. Cites `retain_learn_budget`.\<close>
theorem retainlearnbudget:
  shows "finite K \<Longrightarrow> F \<subseteq> K \<Longrightarrow> masked F (u::'c \<Rightarrow> 'a::euclidean_space) b u' b' \<Longrightarrow> dim (span (u ` F)) + dim (span ((\<lambda>c. u' c - u c) ` K)) \<le> card K"
proof -
  show "finite K \<Longrightarrow> F \<subseteq> K \<Longrightarrow> masked F (u::'c \<Rightarrow> 'a::euclidean_space) b u' b' \<Longrightarrow> dim (span (u ` F)) + dim (span ((\<lambda>c. u' c - u c) ` K)) \<le> card K" by (rule retain_learn_budget)
qed

text \<open>C1(a): every residual lies in the cell of its own sign vector -- the fibers of the membership map cover residual space. Cites `cell_self`.\<close>
theorem cellself:
  shows "r \<in> cell C u b (sgnvec u b r)"
proof -
  show "r \<in> cell C u b (sgnvec u b r)" by (rule cell_self)
qed

text \<open>C1(a): the cells cover all of residual space. Cites `cells_cover`.\<close>
theorem cellscover:
  shows "(\<Union>s. cell C u b s) = UNIV"
proof -
  show "(\<Union>s. cell C u b s) = UNIV" by (rule cells_cover)
qed

text \<open>C1(a): cells of patterns that differ on some concept are disjoint -- with the cover, the nonempty cells PARTITION residual space, so the fibers of the membership map are exactly the arrangement cells. Cites `cells_disjoint`.\<close>
theorem cellsdisjoint:
  shows "c \<in> C \<Longrightarrow> s c \<noteq> t c \<Longrightarrow> cell C u b s \<inter> cell C u b t = {}"
proof -
  show "c \<in> C \<Longrightarrow> s c \<noteq> t c \<Longrightarrow> cell C u b s \<inter> cell C u b t = {}" by (rule cells_disjoint)
qed

text \<open>C1(a): a cell is exactly the intersection of the half-spaces its pattern turns ON with the open complements of those it turns OFF -- the face of the arrangement in its stated polyhedral form. Cites `cell_as_intersection`.\<close>
theorem cellasintersection:
  shows "cell C u b s = (\<Inter>c\<in>{c \<in> C. s c}. Hspace u b c) \<inter> (\<Inter>c\<in>{c \<in> C. \<not> s c}. - Hspace u b c)"
proof -
  show "cell C u b s = (\<Inter>c\<in>{c \<in> C. s c}. Hspace u b c) \<inter> (\<Inter>c\<in>{c \<in> C. \<not> s c}. - Hspace u b c)" by (rule cell_as_intersection)
qed

text \<open>C1(a): every cell is convex -- an intersection of closed and open half-spaces. Cites `cell_convex`.\<close>
theorem cellconvex:
  shows "convex (cell C u b s)"
proof -
  show "convex (cell C u b s)" by (rule cell_convex)
qed

text \<open>C1(b): the derivation operators of the half-space context form a Galois connection -- X is inside the extent of B iff B is inside the intent of X. Cites `fca_galois`.\<close>
theorem fcagalois:
  shows "B \<subseteq> C \<Longrightarrow> (X \<subseteq> extent u b B) \<longleftrightarrow> (B \<subseteq> intent C u b X)"
proof -
  show "B \<subseteq> C \<Longrightarrow> (X \<subseteq> extent u b B) \<longleftrightarrow> (B \<subseteq> intent C u b X)" by (rule fca_galois)
qed

text \<open>C1(b): the double-derivation is extensive -- every object set is contained in the extent of its intent, the closure half of the FCA structure. Cites `fca_closure_extensive`.\<close>
theorem fcaclosureextensive:
  shows "X \<subseteq> extent u b (intent C u b X)"
proof -
  show "X \<subseteq> extent u b (intent C u b X)" by (rule fca_closure_extensive)
qed

text \<open>C1(b): every FCA extent is an intersection of closed half-spaces, hence convex -- the concept lattice's object sets are polyhedral. Cites `extent_convex`.\<close>
theorem extentconvex:
  shows "convex (extent u b B)"
proof -
  show "convex (extent u b B)" by (rule extent_convex)
qed

text \<open>C1(b), the core of the fundamental theorem of FCA for this context: formal concepts are ordered anti-isomorphically -- extents by inclusion iff intents by REVERSE inclusion. Cites `concept_anti_iso`.\<close>
theorem conceptantiiso:
  shows "X1 = extent u b B1 \<Longrightarrow> B1 = intent C u b X1 \<Longrightarrow> X2 = extent u b B2 \<Longrightarrow> B2 = intent C u b X2 \<Longrightarrow> (X1 \<subseteq> X2) \<longleftrightarrow> (B2 \<subseteq> B1)"
proof -
  show "X1 = extent u b B1 \<Longrightarrow> B1 = intent C u b X1 \<Longrightarrow> X2 = extent u b B2 \<Longrightarrow> B2 = intent C u b X2 \<Longrightarrow> (X1 \<subseteq> X2) \<longleftrightarrow> (B2 \<subseteq> B1)" by (rule concept_anti_iso)
qed

text \<open>C1(b) bridge to (a): the FCA intent of a nonempty cell is exactly the ON-set of its sign vector -- the concept lattice carries the same information as the arrangement. Cites `cell_intent_recovers_sign`.\<close>
theorem cellintentrecoverssign:
  shows "cell C u b s \<noteq> {} \<Longrightarrow> intent C u b (cell C u b s) = {c \<in> C. s c}"
proof -
  show "cell C u b s \<noteq> {} \<Longrightarrow> intent C u b (cell C u b s) = {c \<in> C. s c}" by (rule cell_intent_recovers_sign)
qed

text \<open>C1(b): realized sign patterns and cells correspond bijectively -- equal nonempty cells force equal patterns, the object half of the anti-isomorphism. Cites `cell_inj_on_realized`.\<close>
theorem cellinjonrealized:
  shows "cell C u b s \<noteq> {} \<Longrightarrow> cell C u b s = cell C u b t \<Longrightarrow> c \<in> C \<Longrightarrow> s c = t c"
proof -
  show "cell C u b s \<noteq> {} \<Longrightarrow> cell C u b s = cell C u b t \<Longrightarrow> c \<in> C \<Longrightarrow> s c = t c" by (rule cell_inj_on_realized)
qed

text \<open>C1(c): two residuals with the same sign pattern on every decision difference decode identically -- the argmax decoder is piecewise-constant on the cells of its difference arrangement, tropic's cells. Cites `amax_piecewise_constant`.\<close>
theorem amaxpiecewiseconstant:
  shows "(\<And>v w. v \<in> V \<Longrightarrow> w \<in> V \<Longrightarrow> (0 \<le> (U v - U w) \<bullet> r) \<longleftrightarrow> (0 \<le> (U v - U w) \<bullet> r')) \<Longrightarrow> amax V U r = amax V U r'"
proof -
  show "(\<And>v w. v \<in> V \<Longrightarrow> w \<in> V \<Longrightarrow> (0 \<le> (U v - U w) \<bullet> r) \<longleftrightarrow> (0 \<le> (U v - U w) \<bullet> r')) \<Longrightarrow> amax V U r = amax V U r'" by (rule amax_piecewise_constant)
qed

text \<open>C1(c): when the concept family contains every decision hyperplane, residuals in the SAME concept cell decode identically -- the concept arrangement refines the decoder, so the membership bit-vector determines the decode. Cites `concept_refines_decoder`.\<close>
theorem conceptrefinesdecoder:
  shows "(\<And>v w. v \<in> V \<Longrightarrow> w \<in> V \<Longrightarrow> \<exists>c\<in>C. u c = U v - U w \<and> b c = 0) \<Longrightarrow> r \<in> cell C u b s \<Longrightarrow> r' \<in> cell C u b s \<Longrightarrow> amax V U r = amax V U r'"
proof -
  show "(\<And>v w. v \<in> V \<Longrightarrow> w \<in> V \<Longrightarrow> \<exists>c\<in>C. u c = U v - U w \<and> b c = 0) \<Longrightarrow> r \<in> cell C u b s \<Longrightarrow> r' \<in> cell C u b s \<Longrightarrow> amax V U r = amax V U r'" by (rule concept_refines_decoder)
qed

text \<open>C5 main, over the strengthened (exact/calibrated readout) domain: if residuals live in S and the scores are the one-hot targets, the number of distinct outputs -- which IS rank M_g -- is at most dim S. Cites `computed_rank_lower_bound`.\<close>
theorem computedranklowerbound:
  shows "finite X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> (r::'x \<Rightarrow> 'a::euclidean_space) x \<in> S) \<Longrightarrow> g ` X \<subseteq> V \<Longrightarrow> (\<And>x v. x \<in> X \<Longrightarrow> v \<in> V \<Longrightarrow> W v \<bullet> r x = (if g x = v then 1 else 0)) \<Longrightarrow> card (g ` X) \<le> dim S"
proof -
  show "finite X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> (r::'x \<Rightarrow> 'a::euclidean_space) x \<in> S) \<Longrightarrow> g ` X \<subseteq> V \<Longrightarrow> (\<And>x v. x \<in> X \<Longrightarrow> v \<in> V \<Longrightarrow> W v \<bullet> r x = (if g x = v then 1 else 0)) \<Longrightarrow> card (g ` X) \<le> dim S" by (rule computed_rank_lower_bound)
qed

text \<open>C5 degenerate direction: a constant decision (pure lookup) is realizable with exactly calibrated readout over a residual subspace of dimension at most ONE -- retrieval is the rank-one regime. Cites `retrieval_rank_one`.\<close>
theorem retrievalrankone:
  shows "\<exists>(S::'a::euclidean_space set) r W. dim S \<le> 1 \<and> (\<forall>x\<in>X. r x \<in> S) \<and> (\<forall>x\<in>X. \<forall>v\<in>V. W v \<bullet> r x = (if y0 = v then 1 else 0))"
proof -
  show "\<exists>(S::'a::euclidean_space set) r W. dim S \<le> 1 \<and> (\<forall>x\<in>X. r x \<in> S) \<and> (\<forall>x\<in>X. \<forall>v\<in>V. W v \<bullet> r x = (if y0 = v then 1 else 0))" by (rule retrieval_rank_one)
qed

text \<open>Constancy is exactly the one-output case, tying the rank floor to C5's "rho = 1 iff lookup" phrasing on the exact-readout domain. Cites `constant_iff_card_one`.\<close>
theorem constantiffcardone:
  shows "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> (card (g ` X) = 1) \<longleftrightarrow> (\<exists>y. \<forall>x\<in>X. g x = y)"
proof -
  show "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> (card (g ` X) = 1) \<longleftrightarrow> (\<exists>y. \<forall>x\<in>X. g x = y)" by (rule constant_iff_card_one)
qed

text \<open>C5's non-degeneracy consequence, proved form: any two inputs with different outputs force at least TWO residual dimensions under exact readout -- computation is separated from lookup by rank. Cites `computation_needs_rank_two`.\<close>
theorem computationneedsranktwo:
  shows "finite X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> (r::'x \<Rightarrow> 'a::euclidean_space) x \<in> S) \<Longrightarrow> g ` X \<subseteq> V \<Longrightarrow> (\<And>x v. x \<in> X \<Longrightarrow> v \<in> V \<Longrightarrow> W v \<bullet> r x = (if g x = v then 1 else 0)) \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> g x1 \<noteq> g x2 \<Longrightarrow> 2 \<le> dim S"
proof -
  show "finite X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> (r::'x \<Rightarrow> 'a::euclidean_space) x \<in> S) \<Longrightarrow> g ` X \<subseteq> V \<Longrightarrow> (\<And>x v. x \<in> X \<Longrightarrow> v \<in> V \<Longrightarrow> W v \<bullet> r x = (if g x = v then 1 else 0)) \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> g x1 \<noteq> g x2 \<Longrightarrow> 2 \<le> dim S" by (rule computation_needs_rank_two)
qed

text \<open>Homogeneous argmax is scale-invariant on rays: positive scaling never changes the decode. Cites `amax_scaleR`.\<close>
theorem amaxscaler:
  shows "0 < c \<Longrightarrow> amax V W (c *\<^sub>R y) = amax V W y"
proof -
  show "0 < c \<Longrightarrow> amax V W (c *\<^sub>R y) = amax V W y" by (rule amax_scaleR)
qed

text \<open>C5's argmax salvage: over a ONE-dimensional residual subspace the bias-free argmax decoder attains at most THREE distinct decision sets (positive ray, origin, negative ray) -- the provable form of "rank one is the retrieval regime" for the decoder as originally conjectured. Cites `argmax_rank_one_three_behaviors`.\<close>
theorem argmaxrankonethreebehaviors:
  shows "(\<And>x. x \<in> X \<Longrightarrow> r x \<in> span {e}) \<Longrightarrow> card ((\<lambda>x. amax V W (r x)) ` X) \<le> 3"
proof -
  show "(\<And>x. x \<in> X \<Longrightarrow> r x \<in> span {e}) \<Longrightarrow> card ((\<lambda>x. amax V W (r x)) ` X) \<le> 3" by (rule argmax_rank_one_three_behaviors)
qed

text \<open>The addition anchor's counting core: the sum of two width-n operands attains exactly 2n - 1 distinct values. Cites `add_range_card`.\<close>
theorem addrangecard:
  shows "0 < n \<Longrightarrow> card ((\<lambda>(x, y). x + y) ` ({0..<n} \<times> {0..<n})) = 2 * n - 1"
proof -
  show "0 < n \<Longrightarrow> card ((\<lambda>(x, y). x + y) ` ({0..<n} \<times> {0..<n})) = 2 * n - 1" by (rule add_range_card)
qed

text \<open>C5's growth consequence on the exact-readout domain: reading out the sum of two width-n operands needs at least 2n - 1 residual dimensions -- for b-bit operands the floor 2^(b+1) - 1 grows with b. (With argmax decoding the floor provably does not apply -- see RESULTS.md; the measured rank-4 stays `empirical`.) Cites `addition_rank_grows`.\<close>
theorem additionrankgrows:
  shows "0 < n \<Longrightarrow> (\<And>x. x \<in> {0..<n} \<times> {0..<n} \<Longrightarrow> (r::nat \<times> nat \<Rightarrow> 'a::euclidean_space) x \<in> S) \<Longrightarrow> (\<lambda>(x, y). x + y) ` ({0..<n} \<times> {0..<n}) \<subseteq> V \<Longrightarrow> (\<And>x v. x \<in> {0..<n} \<times> {0..<n} \<Longrightarrow> v \<in> V \<Longrightarrow> W v \<bullet> r x = (if fst x + snd x = v then 1 else 0)) \<Longrightarrow> 2 * n - 1 \<le> dim S"
proof -
  show "0 < n \<Longrightarrow> (\<And>x. x \<in> {0..<n} \<times> {0..<n} \<Longrightarrow> (r::nat \<times> nat \<Rightarrow> 'a::euclidean_space) x \<in> S) \<Longrightarrow> (\<lambda>(x, y). x + y) ` ({0..<n} \<times> {0..<n}) \<subseteq> V \<Longrightarrow> (\<And>x v. x \<in> {0..<n} \<times> {0..<n} \<Longrightarrow> v \<in> V \<Longrightarrow> W v \<bullet> r x = (if fst x + snd x = v then 1 else 0)) \<Longrightarrow> 2 * n - 1 \<le> dim S" by (rule addition_rank_grows)
qed

text \<open>The canonical covering set -- the base assignment plus each single-attribute flip -- has exactly card A + 1 elements: the O(A) sample budget of the factored code. Cites `covering_card`.\<close>
theorem coveringcard:
  shows "finite A \<Longrightarrow> card (covering A) = card A + 1"
proof -
  show "finite A \<Longrightarrow> card (covering A) = card A + 1" by (rule covering_card)
qed

text \<open>C3(b), factored side: two factored readouts agreeing on the covering set agree on EVERY assignment -- fitting A + 1 examples pins all 2^A outputs, exact compositional generalization. Cites `factored_identification`.\<close>
theorem factoredidentification:
  shows "finite A \<Longrightarrow> (\<And>T. T \<in> covering A \<Longrightarrow> fpred \<theta> \<theta>0 T = fpred \<theta>' \<theta>0' T) \<Longrightarrow> S \<subseteq> A \<Longrightarrow> fpred \<theta> \<theta>0 S = fpred \<theta>' \<theta>0' S"
proof -
  show "finite A \<Longrightarrow> (\<And>T. T \<in> covering A \<Longrightarrow> fpred \<theta> \<theta>0 T = fpred \<theta>' \<theta>0' T) \<Longrightarrow> S \<subseteq> A \<Longrightarrow> fpred \<theta> \<theta>0 S = fpred \<theta>' \<theta>0' S" by (rule factored_identification)
qed

text \<open>C3(b), partition side: for ANY target and any unseen combination, two partition readouts fit the training set exactly yet disagree on the held-out cell -- the unseen cell is undetermined (chance). Cites `partition_no_generalization`.\<close>
theorem partitionnogeneralization:
  shows "S0 \<notin> Train \<Longrightarrow> \<exists>w w'. (\<forall>S\<in>Train. w S = (T::'i set \<Rightarrow> real) S) \<and> (\<forall>S\<in>Train. w' S = T S) \<and> w S0 \<noteq> w' S0"
proof -
  show "S0 \<notin> Train \<Longrightarrow> \<exists>w w'. (\<forall>S\<in>Train. w S = (T::'i set \<Rightarrow> real) S) \<and> (\<forall>S\<in>Train. w' S = T S) \<and> w S0 \<noteq> w' S0" by (rule partition_no_generalization)
qed

text \<open>C3(c), factored side packaged: there IS a training set of card A + 1 assignments whose fit determines the factored readout on all of Pow A. Cites `factored_sample_complexity`.\<close>
theorem factoredsamplecomplexity:
  shows "finite A \<Longrightarrow> \<exists>Cov\<subseteq>Pow A. card Cov = card A + 1 \<and> (\<forall>\<theta> \<theta>0 \<tau> \<tau>0. (\<forall>T\<in>Cov. fpred \<theta> \<theta>0 T = fpred \<tau> \<tau>0 T) \<longrightarrow> (\<forall>S\<in>Pow A. fpred \<theta> \<theta>0 S = fpred \<tau> \<tau>0 S))"
proof -
  show "finite A \<Longrightarrow> \<exists>Cov\<subseteq>Pow A. card Cov = card A + 1 \<and> (\<forall>\<theta> \<theta>0 \<tau> \<tau>0. (\<forall>T\<in>Cov. fpred \<theta> \<theta>0 T = fpred \<tau> \<tau>0 T) \<longrightarrow> (\<forall>S\<in>Pow A. fpred \<theta> \<theta>0 S = fpred \<tau> \<tau>0 S))" by (rule factored_sample_complexity)
qed

text \<open>C3(c), partition side: any training set with fewer than 2^A cells leaves some combination whose output is a free parameter for EVERY target -- the partition code needs Omega(2^A) samples. Cites `partition_needs_all_cells`.\<close>
theorem partitionneedsallcells:
  shows "finite A \<Longrightarrow> Train \<subseteq> Pow A \<Longrightarrow> card Train < 2 ^ card A \<Longrightarrow> \<exists>S0\<in>Pow A - Train. \<forall>T::'i set \<Rightarrow> real. \<exists>w w'. (\<forall>S\<in>Train. w S = T S) \<and> (\<forall>S\<in>Train. w' S = T S) \<and> w S0 \<noteq> w' S0"
proof -
  show "finite A \<Longrightarrow> Train \<subseteq> Pow A \<Longrightarrow> card Train < 2 ^ card A \<Longrightarrow> \<exists>S0\<in>Pow A - Train. \<forall>T::'i set \<Rightarrow> real. \<exists>w w'. (\<forall>S\<in>Train. w S = T S) \<and> (\<forall>S\<in>Train. w' S = T S) \<and> w S0 \<noteq> w' S0" by (rule partition_needs_all_cells)
qed

text \<open>C3(a), factored side: the conjunction over S0 is ONE linear-threshold rule on the factored code -- unit weights on S0, threshold card S0. Cites `conjunction_single_threshold`.\<close>
theorem conjunctionsinglethreshold:
  shows "finite S0 \<Longrightarrow> (S0 \<subseteq> S) \<longleftrightarrow> (real (card S0) \<le> (\<Sum>i\<in>S0. if i \<in> S then (1::real) else 0))"
proof -
  show "finite S0 \<Longrightarrow> (S0 \<subseteq> S) \<longleftrightarrow> (real (card S0) \<le> (\<Sum>i\<in>S0. if i \<in> S then (1::real) else 0))" by (rule conjunction_single_threshold)
qed

text \<open>C3(a), partition side: the same conjunction occupies one partition cell per positive combination -- exactly 2^(card A - card S0) cells, exponentially many. Cites `conjunction_partition_cells`.\<close>
theorem conjunctionpartitioncells:
  shows "finite A \<Longrightarrow> S0 \<subseteq> A \<Longrightarrow> card {S \<in> Pow A. S0 \<subseteq> S} = 2 ^ (card A - card S0)"
proof -
  show "finite A \<Longrightarrow> S0 \<subseteq> A \<Longrightarrow> card {S \<in> Pow A. S0 \<subseteq> S} = 2 ^ (card A - card S0)" by (rule conjunction_partition_cells)
qed

text \<open>A rule's firing region -- the intersection of its constraint half-spaces -- is convex. Cites `region_convex`.\<close>
theorem regionconvex:
  shows "convex (region u b S)"
proof -
  show "convex (region u b S)" by (rule region_convex)
qed

text \<open>The degenerate exact case: a single-constraint rule IS a half-space. Cites `region_single`.\<close>
theorem regionsingle:
  shows "region u b {c} = {r. b c \<le> u c \<bullet> r}"
proof -
  show "region u b {c} = {r. b c \<le> u c \<bullet> r}" by (rule region_single)
qed

text \<open>C2 exact direction: if the other constraints are jointly redundant -- the region already equals one constraint's half-space -- crystallization into a single concept direction is exact. Cites `redundant_collapse_exact`.\<close>
theorem redundantcollapseexact:
  shows "c \<in> S \<Longrightarrow> region u b S = region u b {c} \<Longrightarrow> \<exists>w t. region u b S = {r. t \<le> w \<bullet> r}"
proof -
  show "c \<in> S \<Longrightarrow> region u b S = region u b {c} \<Longrightarrow> \<exists>w t. region u b S = {r. t \<le> w \<bullet> r}" by (rule redundant_collapse_exact)
qed

text \<open>C2 obstruction: two points outside R whose midpoint lies inside R rule out EVERY half-space representation of R -- half-space complements are convex. The representation-independent core of crystallization inexactness. Cites `midpoint_blocks_collapse`.\<close>
theorem midpointblockscollapse:
  shows "q1 \<notin> R \<Longrightarrow> q2 \<notin> R \<Longrightarrow> midpoint q1 q2 \<in> R \<Longrightarrow> \<not> (\<exists>w t. R = {r. t \<le> w \<bullet> r})"
proof -
  show "q1 \<notin> R \<Longrightarrow> q2 \<notin> R \<Longrightarrow> midpoint q1 q2 \<in> R \<Longrightarrow> \<not> (\<exists>w t. R = {r. t \<le> w \<bullet> r})" by (rule midpoint_blocks_collapse)
qed

text \<open>Every essential constraint supplies a witness: a point satisfying all OTHER constraints but violating the region -- the conjecture's "point near the facet, just outside". Cites `essential_witness`.\<close>
theorem essentialwitness:
  shows "essential u b S c \<Longrightarrow> \<exists>q. q \<in> region u b (S - {c}) \<and> q \<notin> region u b S"
proof -
  show "essential u b S c \<Longrightarrow> \<exists>q. q \<in> region u b (S - {c}) \<and> q \<notin> region u b S" by (rule essential_witness)
qed

text \<open>C2 main obstruction on its stated domain: two essential constraints whose witnesses straddle the region (midpoint inside) block the collapse -- the rule indicator equals NO single half-space indicator. Cites `two_essential_facets_block`.\<close>
theorem twoessentialfacetsblock:
  shows "essential u b S c1 \<Longrightarrow> essential u b S c2 \<Longrightarrow> q1 \<in> region u b (S - {c1}) \<Longrightarrow> q1 \<notin> region u b S \<Longrightarrow> q2 \<in> region u b (S - {c2}) \<Longrightarrow> q2 \<notin> region u b S \<Longrightarrow> midpoint q1 q2 \<in> region u b S \<Longrightarrow> \<not> (\<exists>w t. region u b S = {r. t \<le> w \<bullet> r})"
proof -
  show "essential u b S c1 \<Longrightarrow> essential u b S c2 \<Longrightarrow> q1 \<in> region u b (S - {c1}) \<Longrightarrow> q1 \<notin> region u b S \<Longrightarrow> q2 \<in> region u b (S - {c2}) \<Longrightarrow> q2 \<notin> region u b S \<Longrightarrow> midpoint q1 q2 \<in> region u b S \<Longrightarrow> \<not> (\<exists>w t. region u b S = {r. t \<le> w \<bullet> r})" by (rule two_essential_facets_block)
qed

text \<open>The worked instance, facet one: in the quadrant rule over distinct basis directions both constraints matter -- dropping the first admits a violating witness. Cites `quadrant_essential(1)`.\<close>
theorem quadrantessentialfirst:
  shows "i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> i \<noteq> j \<Longrightarrow> essential (quadrant_dirs i j) (\<lambda>_. 0) {0, 1} 0"
proof -
  show "i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> i \<noteq> j \<Longrightarrow> essential (quadrant_dirs i j) (\<lambda>_. 0) {0, 1} 0" by (rule quadrant_essential(1))
qed

text \<open>The worked instance, facet two: symmetrically, dropping the second constraint admits the witness i - j. Cites `quadrant_essential(2)`.\<close>
theorem quadrantessentialsecond:
  shows "i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> i \<noteq> j \<Longrightarrow> essential (quadrant_dirs i j) (\<lambda>_. 0) {0, 1} 1"
proof -
  show "i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> i \<noteq> j \<Longrightarrow> essential (quadrant_dirs i j) (\<lambda>_. 0) {0, 1} 1" by (rule quadrant_essential(2))
qed

text \<open>C2's worked inexactness: the quadrant -- a genuinely two-facet rule -- provably equals NO single half-space; crystallizing it into one concept direction is inexact, with concrete witnesses j - i, i - j and midpoint 0. Cites `quadrant_not_halfspace`.\<close>
theorem quadrantnothalfspace:
  shows "i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> i \<noteq> j \<Longrightarrow> \<not> (\<exists>w t. region (quadrant_dirs i j) (\<lambda>_. 0) {0, 1} = {r. t \<le> w \<bullet> r})"
proof -
  show "i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> i \<noteq> j \<Longrightarrow> \<not> (\<exists>w t. region (quadrant_dirs i j) (\<lambda>_. 0) {0, 1} = {r. t \<le> w \<bullet> r})" by (rule quadrant_not_halfspace)
qed

text \<open>C6 ungrounded freedom, membership side: rotating residuals and concept directions together preserves every membership -- decisions cannot see the gauge. Cites `ungrounded_gauge_membership`.\<close>
theorem ungroundedgaugemembership:
  shows "orthogonal_transformation R \<Longrightarrow> fires (\<lambda>c. R (u c)) b c (R r) = fires u b c r"
proof -
  show "orthogonal_transformation R \<Longrightarrow> fires (\<lambda>c. R (u c)) b c (R r) = fires u b c r" by (rule ungrounded_gauge_membership)
qed

text \<open>C6 ungrounded freedom, decoder side: the argmax decode is invariant under any orthogonal gauge applied to residuals and readout directions together. Cites `ungrounded_gauge_decoder`.\<close>
theorem ungroundedgaugedecoder:
  shows "orthogonal_transformation R \<Longrightarrow> amax V (\<lambda>v. R (U v)) (R r) = amax V U r"
proof -
  show "orthogonal_transformation R \<Longrightarrow> amax V (\<lambda>v. R (U v)) (R r) = amax V U r" by (rule ungrounded_gauge_decoder)
qed

text \<open>The Householder reflection along any unit direction is an orthogonal transformation -- the generator of the explicit infinite family. Cites `hreflect_orthogonal`.\<close>
theorem hreflectorthogonal:
  shows "n \<bullet> n = 1 \<Longrightarrow> orthogonal_transformation (hreflect n)"
proof -
  show "n \<bullet> n = 1 \<Longrightarrow> orthogonal_transformation (hreflect n)" by (rule hreflect_orthogonal)
qed

text \<open>C6's "continuous": for DIM at least 2 the ungrounded gauge group is INFINITE -- witnessed by the Householder reflections along the unit vectors of a coordinate plane, injectively parametrized. Cites `ungrounded_gauge_infinite`.\<close>
theorem ungroundedgaugeinfinite:
  shows "2 \<le> DIM('a::euclidean_space) \<Longrightarrow> infinite {R::'a \<Rightarrow> 'a. orthogonal_transformation R}"
proof -
  show "2 \<le> DIM('a::euclidean_space) \<Longrightarrow> infinite {R::'a \<Rightarrow> 'a. orthogonal_transformation R}" by (rule ungrounded_gauge_infinite)
qed

text \<open>C6 grounded, exact case: an orthogonal gauge that fixes a SPANNING readout frame pointwise is the identity -- decisions plus exact alignment leave no gauge freedom at all (the generically trivial stabilizer). Cites `alignment_kills_gauge`.\<close>
theorem alignmentkillsgauge:
  shows "orthogonal_transformation R \<Longrightarrow> (\<And>v. v \<in> V \<Longrightarrow> R ((Uout::'v \<Rightarrow> 'a::euclidean_space) v) = Uout v) \<Longrightarrow> span (Uout ` V) = UNIV \<Longrightarrow> R = id"
proof -
  show "orthogonal_transformation R \<Longrightarrow> (\<And>v. v \<in> V \<Longrightarrow> R ((Uout::'v \<Rightarrow> 'a::euclidean_space) v) = Uout v) \<Longrightarrow> span (Uout ` V) = UNIV \<Longrightarrow> R = id" by (rule alignment_kills_gauge)
qed

text \<open>C6 grounded, sign case: if alignment pins each frame direction only up to sign, every consistent gauge is an involution -- applying it twice restores every residual. Cites `sign_gauge_involutive`.\<close>
theorem signgaugeinvolutive:
  shows "linear R \<Longrightarrow> (\<And>v. v \<in> B \<Longrightarrow> R v = v \<or> R v = - v) \<Longrightarrow> span B = (UNIV :: 'a::euclidean_space set) \<Longrightarrow> R \<circ> R = id"
proof -
  show "linear R \<Longrightarrow> (\<And>v. v \<in> B \<Longrightarrow> R v = v \<or> R v = - v) \<Longrightarrow> span B = (UNIV :: 'a::euclidean_space set) \<Longrightarrow> R \<circ> R = id" by (rule sign_gauge_involutive)
qed

text \<open>C6's collapse: only FINITELY many linear gauges send each basis direction to itself or its negation (at most 2^d sign choices) -- versus the infinite ungrounded group. Grounding collapses a continuous gauge to a finite one. Cites `sign_gauge_finite`.\<close>
theorem signgaugefinite:
  shows "finite {R::'a::euclidean_space \<Rightarrow> 'a. linear R \<and> (\<forall>v\<in>Basis. R v = v \<or> R v = - v)}"
proof -
  show "finite {R::'a::euclidean_space \<Rightarrow> 'a. linear R \<and> (\<forall>v\<in>Basis. R v = v \<or> R v = - v)}" by (rule sign_gauge_finite)
qed

end
