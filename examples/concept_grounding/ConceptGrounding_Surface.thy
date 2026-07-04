theory ConceptGrounding_Surface
  imports Consolidation ConceptCells ComputedRank Compositional Crystallization Gauge CrossToken GradedConsolidation
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

text \<open>C7(i), the 4-point core: an additive score g(t1) + h(t2) that clears theta exactly on the diagonal is contradictory on the four pairs from two distinct tokens -- matched and mismatched pairs have the same total. Dimension-free. Cites `equality_not_additive`.\<close>
theorem equalitynotadditive:
  shows "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x \<noteq> y \<Longrightarrow> (\<And>t1 t2. t1 \<in> V \<Longrightarrow> t2 \<in> V \<Longrightarrow> ((theta::real) \<le> g t1 + h t2) \<longleftrightarrow> (t1 = t2)) \<Longrightarrow> False"
proof -
  show "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x \<noteq> y \<Longrightarrow> (\<And>t1 t2. t1 \<in> V \<Longrightarrow> t2 \<in> V \<Longrightarrow> ((theta::real) \<le> g t1 + h t2) \<longleftrightarrow> (t1 = t2)) \<Longrightarrow> False" by (rule equality_not_additive[where V = V and x = x and y = y and theta = theta and g = g and h = h])
qed

text \<open>C7(i) packaged: over any vocabulary with two tokens there is NO additive equality decider at all -- which subsumes every linear head over concatenated per-position features in any dimension. Cites `equality_not_linear`.\<close>
theorem equalitynotlinear:
  shows "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> (\<exists>g h theta. \<forall>t1\<in>V. \<forall>t2\<in>V. ((theta::real) \<le> g t1 + h t2) \<longleftrightarrow> (t1 = t2))"
proof -
  show "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> (\<exists>g h theta. \<forall>t1\<in>V. \<forall>t2\<in>V. ((theta::real) \<le> g t1 + h t2) \<longleftrightarrow> (t1 = t2))" by (rule equality_not_linear)
qed

text \<open>C7(ii): a linear readout over concatenated per-position RESIDUALS is an additive reader, hence cannot decide cross-token equality -- the grounded reader ground_multipos trained, ruled out at every dimension. Cites `equality_not_residual_linear`.\<close>
theorem equalitynotresiduallinear:
  shows "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> (\<exists>theta. \<forall>t1\<in>V. \<forall>t2\<in>V. ((theta::real) \<le> (W1::'a::real_inner) \<bullet> r1 t1 + (W2::'a) \<bullet> r2 t2) \<longleftrightarrow> (t1 = t2))"
proof -
  show "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> (\<exists>theta. \<forall>t1\<in>V. \<forall>t2\<in>V. ((theta::real) \<le> (W1::'a::real_inner) \<bullet> r1 t1 + (W2::'a) \<bullet> r2 t2) \<longleftrightarrow> (t1 = t2))" by (rule equality_not_residual_linear)
qed

text \<open>C7(ii): neither can any bank of hyperplane concepts read per-position and combined linearly -- concept memberships are still additive across positions. The wall is structural, not a capacity limit. Cites `equality_not_membership_linear`.\<close>
theorem equalitynotmembershiplinear:
  shows "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> (\<exists>theta. \<forall>t1\<in>V. \<forall>t2\<in>V. ((theta::real) \<le> (\<Sum>c\<in>C. w1 c * (if fires u bb c (r1 t1) then 1 else 0)) + (\<Sum>c\<in>C. w2 c * (if fires u bb c (r2 t2) then 1 else 0))) \<longleftrightarrow> (t1 = t2))"
proof -
  show "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> (\<exists>theta. \<forall>t1\<in>V. \<forall>t2\<in>V. ((theta::real) \<le> (\<Sum>c\<in>C. w1 c * (if fires u bb c (r1 t1) then 1 else 0)) + (\<Sum>c\<in>C. w2 c * (if fires u bb c (r2 t2) then 1 else 0))) \<longleftrightarrow> (t1 = t2))" by (rule equality_not_membership_linear)
qed

text \<open>C7(iii): with orthonormal per-token features the bilinear score IS the equality indicator -- threshold one half, margin one half. The PR's soft-eq match and the QK-attention primitive. Cites `equality_bilinear`.\<close>
theorem equalitybilinear:
  shows "(\<And>t1 t2. t1 \<in> V \<Longrightarrow> t2 \<in> V \<Longrightarrow> phi t1 \<bullet> phi t2 = (if t1 = t2 then 1 else 0)) \<Longrightarrow> t1 \<in> V \<Longrightarrow> t2 \<in> V \<Longrightarrow> (1 / 2 \<le> phi t1 \<bullet> phi t2) \<longleftrightarrow> (t1 = t2)"
proof -
  show "(\<And>t1 t2. t1 \<in> V \<Longrightarrow> t2 \<in> V \<Longrightarrow> phi t1 \<bullet> phi t2 = (if t1 = t2 then 1 else 0)) \<Longrightarrow> t1 \<in> V \<Longrightarrow> t2 \<in> V \<Longrightarrow> (1 / 2 \<le> phi t1 \<bullet> phi t2) \<longleftrightarrow> (t1 = t2)" by (rule equality_bilinear)
qed

text \<open>C7(iii) existence: orthonormal token features -- hence an exact bilinear equality reader -- exist whenever card V fits the dimension. Paired with the impossibility, the separation theorem for the retrieved/computed frontier. Cites `bilinear_reader_exists`.\<close>
theorem bilinearreaderexists:
  shows "finite V \<Longrightarrow> card V \<le> DIM('a::euclidean_space) \<Longrightarrow> \<exists>phi::'t \<Rightarrow> 'a. \<forall>t1\<in>V. \<forall>t2\<in>V. (1 / 2 \<le> phi t1 \<bullet> phi t2) \<longleftrightarrow> (t1 = t2)"
proof -
  show "finite V \<Longrightarrow> card V \<le> DIM('a::euclidean_space) \<Longrightarrow> \<exists>phi::'t \<Rightarrow> 'a. \<forall>t1\<in>V. \<forall>t2\<in>V. (1 / 2 \<le> phi t1 \<bullet> phi t2) \<longleftrightarrow> (t1 = t2)" by (rule bilinear_reader_exists)
qed

text \<open>C7(iv): a conjunction of per-position concepts fires on a PRODUCT set -- the extents of its two position groups. Conjunctive rules over per-position memberships can only carve products. Cites `conjunction_rule_is_product`.\<close>
theorem conjunctionruleisproduct:
  shows "{(r1, r2). (\<forall>c\<in>S1. r1 \<in> Hspace u bb c) \<and> (\<forall>c\<in>S2. r2 \<in> Hspace u bb c)} = extent u bb S1 \<times> extent u bb S2"
proof -
  show "{(r1, r2). (\<forall>c\<in>S1. r1 \<in> Hspace u bb c) \<and> (\<forall>c\<in>S2. r2 \<in> Hspace u bb c)} = extent u bb S1 \<times> extent u bb S2" by (rule conjunction_rule_is_product)
qed

text \<open>C7(iv) counting: any family of product rules covering the diagonal without firing off-diagonal needs at least card V rules -- each sound rule pins one token. One symbolic eq_atom replaces card V geometric rules: the case for the unified substrate. Cites `equality_needs_card_rules`.\<close>
theorem equalityneedscardrules:
  shows "finite I \<Longrightarrow> (\<And>t. t \<in> V \<Longrightarrow> \<exists>i\<in>I. t \<in> A i \<and> t \<in> B i) \<Longrightarrow> (\<And>i t1 t2. i \<in> I \<Longrightarrow> t1 \<in> V \<Longrightarrow> t2 \<in> V \<Longrightarrow> t1 \<in> A i \<Longrightarrow> t2 \<in> B i \<Longrightarrow> t1 = t2) \<Longrightarrow> card V \<le> card I"
proof -
  show "finite I \<Longrightarrow> (\<And>t. t \<in> V \<Longrightarrow> \<exists>i\<in>I. t \<in> A i \<and> t \<in> B i) \<Longrightarrow> (\<And>i t1 t2. i \<in> I \<Longrightarrow> t1 \<in> V \<Longrightarrow> t2 \<in> V \<Longrightarrow> t1 \<in> A i \<Longrightarrow> t2 \<in> B i \<Longrightarrow> t1 = t2) \<Longrightarrow> card V \<le> card I" by (rule equality_needs_card_rules)
qed

text \<open>C7(iv) tightness: the card V singleton rules cover the diagonal soundly -- the product-rule cost of equality is exactly card V. Cites `equality_card_rules_suffice`.\<close>
theorem equalitycardrulessuffice:
  shows "(\<forall>t\<in>V. \<exists>i\<in>V. t \<in> {i} \<and> t \<in> {i}) \<and> (\<forall>i\<in>V. \<forall>t1\<in>V. \<forall>t2\<in>V. t1 \<in> {i} \<longrightarrow> t2 \<in> {i} \<longrightarrow> t1 = t2)"
proof -
  show "(\<forall>t\<in>V. \<exists>i\<in>V. t \<in> {i} \<and> t \<in> {i}) \<and> (\<forall>i\<in>V. \<forall>t1\<in>V. \<forall>t2\<in>V. t1 \<in> {i} \<longrightarrow> t2 \<in> {i} \<longrightarrow> t1 = t2)" by (rule equality_card_rules_suffice)
qed

text \<open>Drift perturbs scores by at most D * norm r: the Cauchy-Schwarz step every certificate below rests on. Cites `inner_drift_bound`.\<close>
theorem innerdriftbound:
  shows "norm (v' - v) \<le> D \<Longrightarrow> \<bar>v' \<bullet> r - v \<bullet> r\<bar> \<le> D * norm r"
proof -
  show "norm (v' - v) \<le> D \<Longrightarrow> \<bar>v' \<bullet> r - v \<bullet> r\<bar> \<le> D * norm r" by (rule inner_drift_bound)
qed

text \<open>C8 core: at a stationary point of task-loss + quadratic incidence anchor, the drift obeys norm (p - pbar) ≤ G / (2*lam*omega) -- protection scales as one over the incidence importance. Cites `anchored_drift_bound`.\<close>
theorem anchoreddriftbound:
  shows "gL + (2 * lam * om) *\<^sub>R (p - pbar) = 0 \<Longrightarrow> norm gL \<le> G \<Longrightarrow> 0 < lam \<Longrightarrow> 0 < om \<Longrightarrow> norm (p - pbar) \<le> G / (2 * lam * om)"
proof -
  show "gL + (2 * lam * om) *\<^sub>R (p - pbar) = 0 \<Longrightarrow> norm gL \<le> G \<Longrightarrow> 0 < lam \<Longrightarrow> 0 < om \<Longrightarrow> norm (p - pbar) \<le> G / (2 * lam * om)" by (rule anchored_drift_bound)
qed

text \<open>The explicit freeze schedule: incidence omega ≥ G/(2*lam*eps) caps the drift at eps -- the binary freeze of C4 is the omega -> infinity limit, quantitatively. Cites `freeze_limit`.\<close>
theorem freezelimit:
  shows "gL + (2 * lam * om) *\<^sub>R (p - pbar) = 0 \<Longrightarrow> norm gL \<le> G \<Longrightarrow> 0 < lam \<Longrightarrow> 0 < om \<Longrightarrow> 0 < eps \<Longrightarrow> G / (2 * lam * eps) \<le> om \<Longrightarrow> norm (p - pbar) \<le> eps"
proof -
  show "gL + (2 * lam * om) *\<^sub>R (p - pbar) = 0 \<Longrightarrow> norm gL \<le> G \<Longrightarrow> 0 < lam \<Longrightarrow> 0 < om \<Longrightarrow> 0 < eps \<Longrightarrow> G / (2 * lam * eps) \<le> om \<Longrightarrow> norm (p - pbar) \<le> eps" by (rule freeze_limit)
qed

text \<open>The membership certificate: a concept whose direction drifted at most D keeps every membership whose margin beats D * norm r -- exactly, per input. Cites `drifted_membership_preserved`.\<close>
theorem driftedmembershippreserved:
  shows "norm (u' c - u c) \<le> D \<Longrightarrow> D * norm r < \<bar>u c \<bullet> r - b c\<bar> \<Longrightarrow> fires u' b c r = fires u b c r"
proof -
  show "norm (u' c - u c) \<le> D \<Longrightarrow> D * norm r < \<bar>u c \<bullet> r - b c\<bar> \<Longrightarrow> fires u' b c r = fires u b c r" by (rule drifted_membership_preserved)
qed

text \<open>A strict winner is the unique argmax -- the decode-side helper. Cites `amax_strict_winner`.\<close>
theorem amaxstrictwinner:
  shows "v0 \<in> V \<Longrightarrow> (\<And>w. w \<in> V \<Longrightarrow> w \<noteq> v0 \<Longrightarrow> U w \<bullet> r < U v0 \<bullet> r) \<Longrightarrow> amax V U r = {v0}"
proof -
  show "v0 \<in> V \<Longrightarrow> (\<And>w. w \<in> V \<Longrightarrow> w \<noteq> v0 \<Longrightarrow> U w \<bullet> r < U v0 \<bullet> r) \<Longrightarrow> amax V U r = {v0}" by (rule amax_strict_winner)
qed

text \<open>The decode certificate: if every readout direction drifted at most D and the winner's margin beats 2 * D * norm r, the argmax decision is identical before and after -- the PIC_Prune / PIC_Quant triangle shape with drift as the perturbation. Cites `drifted_decode_preserved`.\<close>
theorem drifteddecodepreserved:
  shows "(\<And>v. v \<in> V \<Longrightarrow> norm (U' v - U v) \<le> D) \<Longrightarrow> v0 \<in> V \<Longrightarrow> (\<And>w. w \<in> V \<Longrightarrow> w \<noteq> v0 \<Longrightarrow> U w \<bullet> r + 2 * (D * norm r) < U v0 \<bullet> r) \<Longrightarrow> amax V U' r = {v0} \<and> amax V U r = {v0}"
proof -
  show "(\<And>v. v \<in> V \<Longrightarrow> norm (U' v - U v) \<le> D) \<Longrightarrow> v0 \<in> V \<Longrightarrow> (\<And>w. w \<in> V \<Longrightarrow> w \<noteq> v0 \<Longrightarrow> U w \<bullet> r + 2 * (D * norm r) < U v0 \<bullet> r) \<Longrightarrow> amax V U' r = {v0} \<and> amax V U r = {v0}" by (rule drifted_decode_preserved)
qed

text \<open>C8 composed: stationarity of the omega-anchored objective + gradient bound + membership margin give EXACT per-input stability at finite omega -- C4's zero forgetting, margin-gated; the required margin shrinks to zero as omega grows. Cites `graded_membership_stability`.\<close>
theorem gradedmembershipstability:
  shows "gL + (2 * lam * om) *\<^sub>R (u' c - u c) = 0 \<Longrightarrow> norm gL \<le> G \<Longrightarrow> 0 < lam \<Longrightarrow> 0 < om \<Longrightarrow> G / (2 * lam * om) * norm r < \<bar>u c \<bullet> r - b c\<bar> \<Longrightarrow> fires u' b c r = fires u b c r"
proof -
  show "gL + (2 * lam * om) *\<^sub>R (u' c - u c) = 0 \<Longrightarrow> norm gL \<le> G \<Longrightarrow> 0 < lam \<Longrightarrow> 0 < om \<Longrightarrow> G / (2 * lam * om) * norm r < \<bar>u c \<bullet> r - b c\<bar> \<Longrightarrow> fires u' b c r = fires u b c r" by (rule graded_membership_stability)
qed

text \<open>The Adam finding as a theorem (signSGD idealization): an arbitrary positive per-step protection factor on the gradient leaves the ENTIRE trajectory unchanged -- multiplicative protection is a provable no-op under sign-normalized updates. Cites `sign_updates_ignore_scaling`.\<close>
theorem signupdatesignorescaling:
  shows "(q::nat \<Rightarrow> real) 0 = p 0 \<Longrightarrow> (\<And>n. 0 < c n) \<Longrightarrow> (\<And>n. p (Suc n) = p n - eta * sgn (grad n (p n))) \<Longrightarrow> (\<And>n. q (Suc n) = q n - eta * sgn (c n * grad n (q n))) \<Longrightarrow> q n = p n"
proof -
  show "(q::nat \<Rightarrow> real) 0 = p 0 \<Longrightarrow> (\<And>n. 0 < c n) \<Longrightarrow> (\<And>n. p (Suc n) = p n - eta * sgn (grad n (p n))) \<Longrightarrow> (\<And>n. q (Suc n) = q n - eta * sgn (c n * grad n (q n))) \<Longrightarrow> q n = p n" by (rule sign_updates_ignore_scaling)
qed

text \<open>The contrast: a plain gradient step shrinks linearly with the protection factor -- the mechanism scaling was wrongly expected to provide under Adam. Protection must enter the loss (the anchor), not the gradient magnitude. Cites `plain_update_scales`.\<close>
theorem plainupdatescales:
  shows "\<bar>((p::real) - eta * (c * g)) - p\<bar> = \<bar>c\<bar> * \<bar>eta * g\<bar>"
proof -
  show "\<bar>((p::real) - eta * (c * g)) - p\<bar> = \<bar>c\<bar> * \<bar>eta * g\<bar>" by (rule plain_update_scales)
qed

end
