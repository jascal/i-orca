<!--
  i-orca surface for the PIC/PIL GROUNDING CONJECTURES (workspace PIC_PIL_GROUNDING_CONJECTURES.md):
  six theorems about the geometry of grounded concepts -- concepts as half-spaces in residual space --
  proved in the work package's priority order C4, C1, C5, C3, C2, C6.

    C4  Consolidation.thy   -- masked training preserves frozen memberships/decisions EXACTLY;
                               reachable change and new boundaries confined to the plastic span;
                               retain-rank + learn-rank <= K.
    C1  ConceptCells.thy    -- sign-vector fibers = arrangement cells (partition, stated intersection,
                               convex); FCA Galois connection + concept anti-isomorphism; the intent of
                               a cell recovers its sign vector; the argmax decoder is piecewise-constant
                               on the cells and the concept arrangement refines it.
    C5  ComputedRank.thy    -- the computed-core rank floor under EXACT readout (the honest premise
                               strengthening: over argmax as originally stated the floor is false);
                               retrieval = rank one; homogeneous argmax at rank one has <= 3 behaviors;
                               the addition floor 2n-1 grows with operand width.
    C3  Compositional.thy   -- factored vs partition codes: covering fit generalizes exactly vs unseen
                               cells undetermined; card A + 1 vs 2^card A samples; a conjunction is one
                               threshold rule vs exponentially many cells.
    C2  Crystallization.thy -- collapse of a rule to one concept is exact iff the region is one
                               half-space: joint-redundancy direction, midpoint obstruction, essential
                               witnesses, and the fully worked quadrant instance.
    C6  Gauge.thy           -- decisions are O(d)-gauge-invariant and that gauge is provably INFINITE
                               (Householder family, DIM >= 2); exact alignment to a spanning frame kills
                               it (R = id); sign alignment leaves a finite involutive gauge.

  Two follow-on conjectures from the Wyly review (pil PR #10, feat/concept-rule-learner):

    C7  CrossToken.thy      -- cross-token equality is LINEAR-IMPOSSIBLE (no additive reader at any
                               dimension; the 4-point argument) but BILINEAR-EASY (orthonormal features,
                               threshold 1/2); conjunctive per-position rules only carve product sets and
                               need >= card V of them (tight) where one symbolic eq_atom suffices -- the
                               kernel-checked case for Wyly's unified substrate.
    C8  GradedConsolidation.thy -- the graded stability-plasticity certificate: anchored drift bound
                               norm(p - pbar) <= G/(2*lam*omega) at stationarity, freeze limit, drift-vs-
                               margin membership/decode preservation (PIC_Prune triangle shape), composed
                               graded stability; and the Adam finding as a theorem: sign-normalized
                               updates provably IGNORE gradient scaling while plain steps scale linearly.

  As in the sibling corpora, the heavy content lives in the kernel-checked substrate theories; each
  theorem below is STATED in i-orca form and discharged by `(rule <lemma>)`. Cited lemmas are NOT
  listed in `## context` (context rows lower to local assumes, which would make the cite vacuous).

  Verification:
    - `i-orca verify` (structural, zero Isabelle): all 68 theorems VALID.
    - Kernel: this file is compiled (`i-orca compile --target isar --document`) to
      ConceptGrounding_Surface.thy, which the ConceptGrounding session BUILDS -- the surface is
      re-derived by the kernel against the substrate end-to-end (the provable_opt pattern):
          isabelle build -d examples/concept_grounding -o quick_and_dirty ConceptGrounding
      The standalone `i-orca check` builds each theorem under a plain HOL parent and cannot load this
      project-local session (same caveat as the other corpora).

  Discipline: every theorem is `proved` over its STATED domain (finite concept sets, half-space
  membership, linear/argmax/exact readout as named per theorem); the bridge to real-LLM measurements
  stays `open`/`empirical` -- see PROPOSAL.md's tag ledger and RESULTS.md's premise-strengthening report.
-->

<!-- ============================================================================
     C4 -- CONSOLIDATION (Consolidation.thy): the stability-plasticity rank tradeoff.
     ============================================================================ -->

# theorem FrozenMembershipInvariant
> C4(i), one step: a masked update leaves every frozen concept's membership function identical. Cites `frozen_membership_invariant`.

## imports
| Theory        |
|---------------|
| Consolidation |

## goal
| Statement |
|-----------|
| masked F u b u' b' ⟹ c ∈ F ⟹ fires u' b' c = fires u b c |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | masked F u b u' b' ⟹ c ∈ F ⟹ fires u' b' c = fires u b c | frozen parameters are untouched, so the half-space test is unchanged | — | (rule frozen_membership_invariant) | method |


# theorem FrozenMembershipTrajectory
> C4(i), whole trajectory: any run of masked training steps leaves frozen memberships at their initial state -- invariance under ALL subsequent training. Cites `frozen_membership_trajectory`.

## imports
| Theory        |
|---------------|
| Consolidation |

## goal
| Statement |
|-----------|
| (⋀n. n < N ⟹ masked F (u n) (b n) (u (Suc n)) (b (Suc n))) ⟹ c ∈ F ⟹ fires (u N) (b N) c = fires (u 0) (b 0) c |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (⋀n. n < N ⟹ masked F (u n) (b n) (u (Suc n)) (b (Suc n))) ⟹ c ∈ F ⟹ fires (u N) (b N) c = fires (u 0) (b 0) c | induct over the trajectory; each masked step preserves the frozen membership | — | (rule frozen_membership_trajectory) | method |


# theorem FrozenDecisionPreserved
> C4(ii): every decision that reads only the frozen memberships returns the same value on every residual after any masked update -- zero forgetting, exactly. Cites `frozen_decision_preserved`.

## imports
| Theory        |
|---------------|
| Consolidation |

## goal
| Statement |
|-----------|
| masked F u b u' b' ⟹ D (restrict (λc. fires u' b' c r) F) = D (restrict (λc. fires u b c r) F) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | masked F u b u' b' ⟹ D (restrict (λc. fires u' b' c r) F) = D (restrict (λc. fires u b c r) F) | the restricted membership vectors coincide, so any function of them does | — | (rule frozen_decision_preserved) | method |


# theorem ReachableChangeDim
> C4(iii): the update of the whole concept frame vanishes on F, so it spans at most card (K - F) dimensions -- the reachable change is confined to the plastic span. Cites `reachable_change_dim`.

## imports
| Theory        |
|---------------|
| Consolidation |

## goal
| Statement |
|-----------|
| finite K ⟹ masked F (u::'c ⇒ 'a::euclidean_space) b u' b' ⟹ F ⊆ K ⟹ dim (span ((λc. u' c - u c) ` K)) ≤ card (K - F) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite K ⟹ masked F (u::'c ⇒ 'a::euclidean_space) b u' b' ⟹ F ⊆ K ⟹ dim (span ((λc. u' c - u c) ` K)) ≤ card (K - F) | frozen differences are zero; the rest are at most card (K - F) vectors | — | (rule reachable_change_dim) | method |


# theorem PlasticBoundaryDim
> C4(iii), boundary form: any bank of directions over the plastic set spans at most card P dimensions -- new-task decision boundaries live in a subspace of dimension at most the plastic budget. Cites `plastic_boundary_dim`.

## imports
| Theory        |
|---------------|
| Consolidation |

## goal
| Statement |
|-----------|
| finite P ⟹ dim (span ((u'::'c ⇒ 'a::euclidean_space) ` P)) ≤ card P |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite P ⟹ dim (span ((u'::'c ⇒ 'a::euclidean_space) ` P)) ≤ card P | the span of card P vectors has dimension at most card P | — | (rule plastic_boundary_dim) | method |


# theorem RetainLearnBudget
> C4 corollary, the hard tradeoff: retain-rank + learn-rank <= K. Freezing a k-dim frame preserves it exactly at the cost of capping new learning at K - k dimensions. Cites `retain_learn_budget`.

## imports
| Theory        |
|---------------|
| Consolidation |

## goal
| Statement |
|-----------|
| finite K ⟹ F ⊆ K ⟹ masked F (u::'c ⇒ 'a::euclidean_space) b u' b' ⟹ dim (span (u ` F)) + dim (span ((λc. u' c - u c) ` K)) ≤ card K |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite K ⟹ F ⊆ K ⟹ masked F (u::'c ⇒ 'a::euclidean_space) b u' b' ⟹ dim (span (u ` F)) + dim (span ((λc. u' c - u c) ` K)) ≤ card K | card F bounds the retained rank, card (K - F) the reachable change; they sum to card K | — | (rule retain_learn_budget) | method |


<!-- ============================================================================
     C1 -- CONCEPT CELLS (ConceptCells.thy): lattice == arrangement == decoder cells.
     ============================================================================ -->

# theorem CellSelf
> C1(a): every residual lies in the cell of its own sign vector -- the fibers of the membership map cover residual space. Cites `cell_self`.

## imports
| Theory       |
|--------------|
| ConceptCells |

## goal
| Statement |
|-----------|
| r ∈ cell C u b (sgnvec u b r) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | r ∈ cell C u b (sgnvec u b r) | a point trivially matches its own sign pattern | — | (rule cell_self) | method |


# theorem CellsCover
> C1(a): the cells cover all of residual space. Cites `cells_cover`.

## imports
| Theory       |
|--------------|
| ConceptCells |

## goal
| Statement |
|-----------|
| (⋃s. cell C u b s) = UNIV |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (⋃s. cell C u b s) = UNIV | every point lies in the cell of its own sign vector | — | (rule cells_cover) | method |


# theorem CellsDisjoint
> C1(a): cells of patterns that differ on some concept are disjoint -- with the cover, the nonempty cells PARTITION residual space, so the fibers of the membership map are exactly the arrangement cells. Cites `cells_disjoint`.

## imports
| Theory       |
|--------------|
| ConceptCells |

## goal
| Statement |
|-----------|
| c ∈ C ⟹ s c ≠ t c ⟹ cell C u b s ∩ cell C u b t = {} |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | c ∈ C ⟹ s c ≠ t c ⟹ cell C u b s ∩ cell C u b t = {} | one point cannot satisfy two different signs on concept c | — | (rule cells_disjoint) | method |


# theorem CellAsIntersection
> C1(a): a cell is exactly the intersection of the half-spaces its pattern turns ON with the open complements of those it turns OFF -- the face of the arrangement in its stated polyhedral form. Cites `cell_as_intersection`.

## imports
| Theory       |
|--------------|
| ConceptCells |

## goal
| Statement |
|-----------|
| cell C u b s = (⋂c∈{c ∈ C. s c}. Hspace u b c) ∩ (⋂c∈{c ∈ C. ¬ s c}. - Hspace u b c) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | cell C u b s = (⋂c∈{c ∈ C. s c}. Hspace u b c) ∩ (⋂c∈{c ∈ C. ¬ s c}. - Hspace u b c) | unfold the sign conditions into memberships and complements | — | (rule cell_as_intersection) | method |


# theorem CellConvex
> C1(a): every cell is convex -- an intersection of closed and open half-spaces. Cites `cell_convex`.

## imports
| Theory       |
|--------------|
| ConceptCells |

## goal
| Statement |
|-----------|
| convex (cell C u b s) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | convex (cell C u b s) | half-spaces and their complements are convex; intersections preserve convexity | — | (rule cell_convex) | method |


# theorem FcaGalois
> C1(b): the derivation operators of the half-space context form a Galois connection -- X is inside the extent of B iff B is inside the intent of X. Cites `fca_galois`.

## imports
| Theory       |
|--------------|
| ConceptCells |

## goal
| Statement |
|-----------|
| B ⊆ C ⟹ (X ⊆ extent u b B) ⟷ (B ⊆ intent C u b X) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | B ⊆ C ⟹ (X ⊆ extent u b B) ⟷ (B ⊆ intent C u b X) | both sides say every residual of X satisfies every concept of B | — | (rule fca_galois) | method |


# theorem FcaClosureExtensive
> C1(b): the double-derivation is extensive -- every object set is contained in the extent of its intent, the closure half of the FCA structure. Cites `fca_closure_extensive`.

## imports
| Theory       |
|--------------|
| ConceptCells |

## goal
| Statement |
|-----------|
| X ⊆ extent u b (intent C u b X) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | X ⊆ extent u b (intent C u b X) | each residual of X satisfies every concept its whole set satisfies | — | (rule fca_closure_extensive) | method |


# theorem ExtentConvex
> C1(b): every FCA extent is an intersection of closed half-spaces, hence convex -- the concept lattice's object sets are polyhedral. Cites `extent_convex`.

## imports
| Theory       |
|--------------|
| ConceptCells |

## goal
| Statement |
|-----------|
| convex (extent u b B) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | convex (extent u b B) | an intersection of convex half-spaces is convex | — | (rule extent_convex) | method |


# theorem ConceptAntiIso
> C1(b), the core of the fundamental theorem of FCA for this context: formal concepts are ordered anti-isomorphically -- extents by inclusion iff intents by REVERSE inclusion. Cites `concept_anti_iso`.

## imports
| Theory       |
|--------------|
| ConceptCells |

## goal
| Statement |
|-----------|
| X1 = extent u b B1 ⟹ B1 = intent C u b X1 ⟹ X2 = extent u b B2 ⟹ B2 = intent C u b X2 ⟹ (X1 ⊆ X2) ⟷ (B2 ⊆ B1) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | X1 = extent u b B1 ⟹ B1 = intent C u b X1 ⟹ X2 = extent u b B2 ⟹ B2 = intent C u b X2 ⟹ (X1 ⊆ X2) ⟷ (B2 ⊆ B1) | derivation operators are antitone in both directions | — | (rule concept_anti_iso) | method |


# theorem CellIntentRecoversSign
> C1(b) bridge to (a): the FCA intent of a nonempty cell is exactly the ON-set of its sign vector -- the concept lattice carries the same information as the arrangement. Cites `cell_intent_recovers_sign`.

## imports
| Theory       |
|--------------|
| ConceptCells |

## goal
| Statement |
|-----------|
| cell C u b s ≠ {} ⟹ intent C u b (cell C u b s) = {c ∈ C. s c} |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | cell C u b s ≠ {} ⟹ intent C u b (cell C u b s) = {c ∈ C. s c} | ON concepts hold across the cell; a witness point refutes every OFF concept | — | (rule cell_intent_recovers_sign) | method |


# theorem CellInjOnRealized
> C1(b): realized sign patterns and cells correspond bijectively -- equal nonempty cells force equal patterns, the object half of the anti-isomorphism. Cites `cell_inj_on_realized`.

## imports
| Theory       |
|--------------|
| ConceptCells |

## goal
| Statement |
|-----------|
| cell C u b s ≠ {} ⟹ cell C u b s = cell C u b t ⟹ c ∈ C ⟹ s c = t c |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | cell C u b s ≠ {} ⟹ cell C u b s = cell C u b t ⟹ c ∈ C ⟹ s c = t c | a shared point has one sign vector | — | (rule cell_inj_on_realized) | method |


# theorem AmaxPiecewiseConstant
> C1(c): two residuals with the same sign pattern on every decision difference decode identically -- the argmax decoder is piecewise-constant on the cells of its difference arrangement, tropic's cells. Cites `amax_piecewise_constant`.

## imports
| Theory       |
|--------------|
| ConceptCells |

## goal
| Statement |
|-----------|
| (⋀v w. v ∈ V ⟹ w ∈ V ⟹ (0 ≤ (U v - U w) ∙ r) ⟷ (0 ≤ (U v - U w) ∙ r')) ⟹ amax V U r = amax V U r' |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (⋀v w. v ∈ V ⟹ w ∈ V ⟹ (0 ≤ (U v - U w) ∙ r) ⟷ (0 ≤ (U v - U w) ∙ r')) ⟹ amax V U r = amax V U r' | each pairwise comparison is a sign of a difference functional | — | (rule amax_piecewise_constant) | method |


# theorem ConceptRefinesDecoder
> C1(c): when the concept family contains every decision hyperplane, residuals in the SAME concept cell decode identically -- the concept arrangement refines the decoder, so the membership bit-vector determines the decode. Cites `concept_refines_decoder`.

## imports
| Theory       |
|--------------|
| ConceptCells |

## goal
| Statement |
|-----------|
| (⋀v w. v ∈ V ⟹ w ∈ V ⟹ ∃c∈C. u c = U v - U w ∧ b c = 0) ⟹ r ∈ cell C u b s ⟹ r' ∈ cell C u b s ⟹ amax V U r = amax V U r' |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (⋀v w. v ∈ V ⟹ w ∈ V ⟹ ∃c∈C. u c = U v - U w ∧ b c = 0) ⟹ r ∈ cell C u b s ⟹ r' ∈ cell C u b s ⟹ amax V U r = amax V U r' | the shared sign vector fixes the sign of every decision difference | — | (rule concept_refines_decoder) | method |


<!-- ============================================================================
     C5 -- COMPUTED RANK (ComputedRank.thy): the computed-core rank floor.
     Premise strengthening: EXACT readout; over argmax the floor is false (see RESULTS.md).
     ============================================================================ -->

# theorem ComputedRankLowerBound
> C5 main, over the strengthened (exact/calibrated readout) domain: if residuals live in S and the scores are the one-hot targets, the number of distinct outputs -- which IS rank M_g -- is at most dim S. Cites `computed_rank_lower_bound`.

## imports
| Theory       |
|--------------|
| ComputedRank |

## goal
| Statement |
|-----------|
| finite X ⟹ (⋀x. x ∈ X ⟹ (r::'x ⇒ 'a::euclidean_space) x ∈ S) ⟹ g ` X ⊆ V ⟹ (⋀x v. x ∈ X ⟹ v ∈ V ⟹ W v ∙ r x = (if g x = v then 1 else 0)) ⟹ card (g ` X) ≤ dim S |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite X ⟹ (⋀x. x ∈ X ⟹ (r::'x ⇒ 'a::euclidean_space) x ∈ S) ⟹ g ` X ⊆ V ⟹ (⋀x v. x ∈ X ⟹ v ∈ V ⟹ W v ∙ r x = (if g x = v then 1 else 0)) ⟹ card (g ` X) ≤ dim S | per-output witness residuals are separated by the reader functionals, hence independent in S | — | (rule computed_rank_lower_bound) | method |


# theorem RetrievalRankOne
> C5 degenerate direction: a constant decision (pure lookup) is realizable with exactly calibrated readout over a residual subspace of dimension at most ONE -- retrieval is the rank-one regime. Cites `retrieval_rank_one`.

## imports
| Theory       |
|--------------|
| ComputedRank |

## goal
| Statement |
|-----------|
| ∃(S::'a::euclidean_space set) r W. dim S ≤ 1 ∧ (∀x∈X. r x ∈ S) ∧ (∀x∈X. ∀v∈V. W v ∙ r x = (if y0 = v then 1 else 0)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ∃(S::'a::euclidean_space set) r W. dim S ≤ 1 ∧ (∀x∈X. r x ∈ S) ∧ (∀x∈X. ∀v∈V. W v ∙ r x = (if y0 = v then 1 else 0)) | one fixed basis direction carries the constant answer | — | (rule retrieval_rank_one) | method |


# theorem ConstantIffCardOne
> Constancy is exactly the one-output case, tying the rank floor to C5's "rho = 1 iff lookup" phrasing on the exact-readout domain. Cites `constant_iff_card_one`.

## imports
| Theory       |
|--------------|
| ComputedRank |

## goal
| Statement |
|-----------|
| finite X ⟹ X ≠ {} ⟹ (card (g ` X) = 1) ⟷ (∃y. ∀x∈X. g x = y) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite X ⟹ X ≠ {} ⟹ (card (g ` X) = 1) ⟷ (∃y. ∀x∈X. g x = y) | a one-element image is exactly a constant function on a nonempty domain | — | (rule constant_iff_card_one) | method |


# theorem ComputationNeedsRankTwo
> C5's non-degeneracy consequence, proved form: any two inputs with different outputs force at least TWO residual dimensions under exact readout -- computation is separated from lookup by rank. Cites `computation_needs_rank_two`.

## imports
| Theory       |
|--------------|
| ComputedRank |

## goal
| Statement |
|-----------|
| finite X ⟹ (⋀x. x ∈ X ⟹ (r::'x ⇒ 'a::euclidean_space) x ∈ S) ⟹ g ` X ⊆ V ⟹ (⋀x v. x ∈ X ⟹ v ∈ V ⟹ W v ∙ r x = (if g x = v then 1 else 0)) ⟹ x1 ∈ X ⟹ x2 ∈ X ⟹ g x1 ≠ g x2 ⟹ 2 ≤ dim S |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite X ⟹ (⋀x. x ∈ X ⟹ (r::'x ⇒ 'a::euclidean_space) x ∈ S) ⟹ g ` X ⊆ V ⟹ (⋀x v. x ∈ X ⟹ v ∈ V ⟹ W v ∙ r x = (if g x = v then 1 else 0)) ⟹ x1 ∈ X ⟹ x2 ∈ X ⟹ g x1 ≠ g x2 ⟹ 2 ≤ dim S | two distinct outputs put two elements in the image; the rank floor does the rest | — | (rule computation_needs_rank_two) | method |


# theorem AmaxScaleR
> Homogeneous argmax is scale-invariant on rays: positive scaling never changes the decode. Cites `amax_scaleR`.

## imports
| Theory       |
|--------------|
| ComputedRank |

## goal
| Statement |
|-----------|
| 0 < c ⟹ amax V W (c *\<^sub>R y) = amax V W y |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < c ⟹ amax V W (c *\<^sub>R y) = amax V W y | positive scaling preserves every score comparison | — | (rule amax_scaleR) | method |


# theorem ArgmaxRankOneThreeBehaviors
> C5's argmax salvage: over a ONE-dimensional residual subspace the bias-free argmax decoder attains at most THREE distinct decision sets (positive ray, origin, negative ray) -- the provable form of "rank one is the retrieval regime" for the decoder as originally conjectured. Cites `argmax_rank_one_three_behaviors`.

## imports
| Theory       |
|--------------|
| ComputedRank |

## goal
| Statement |
|-----------|
| (⋀x. x ∈ X ⟹ r x ∈ span {e}) ⟹ card ((λx. amax V W (r x)) ` X) ≤ 3 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (⋀x. x ∈ X ⟹ r x ∈ span {e}) ⟹ card ((λx. amax V W (r x)) ` X) ≤ 3 | on a line the decode depends only on the sign of the coordinate | — | (rule argmax_rank_one_three_behaviors) | method |


# theorem AddRangeCard
> The addition anchor's counting core: the sum of two width-n operands attains exactly 2n - 1 distinct values. Cites `add_range_card`.

## imports
| Theory       |
|--------------|
| ComputedRank |

## goal
| Statement |
|-----------|
| 0 < n ⟹ card ((λ(x, y). x + y) ` ({0..<n} × {0..<n})) = 2 * n - 1 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < n ⟹ card ((λ(x, y). x + y) ` ({0..<n} × {0..<n})) = 2 * n - 1 | the image is exactly the interval from 0 to 2n - 2 | — | (rule add_range_card) | method |


# theorem AdditionRankGrows
> C5's growth consequence on the exact-readout domain: reading out the sum of two width-n operands needs at least 2n - 1 residual dimensions -- for b-bit operands the floor 2^(b+1) - 1 grows with b. (With argmax decoding the floor provably does not apply -- see RESULTS.md; the measured rank-4 stays `empirical`.) Cites `addition_rank_grows`.

## imports
| Theory       |
|--------------|
| ComputedRank |

## goal
| Statement |
|-----------|
| 0 < n ⟹ (⋀x. x ∈ {0..<n} × {0..<n} ⟹ (r::nat × nat ⇒ 'a::euclidean_space) x ∈ S) ⟹ (λ(x, y). x + y) ` ({0..<n} × {0..<n}) ⊆ V ⟹ (⋀x v. x ∈ {0..<n} × {0..<n} ⟹ v ∈ V ⟹ W v ∙ r x = (if fst x + snd x = v then 1 else 0)) ⟹ 2 * n - 1 ≤ dim S |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 0 < n ⟹ (⋀x. x ∈ {0..<n} × {0..<n} ⟹ (r::nat × nat ⇒ 'a::euclidean_space) x ∈ S) ⟹ (λ(x, y). x + y) ` ({0..<n} × {0..<n}) ⊆ V ⟹ (⋀x v. x ∈ {0..<n} × {0..<n} ⟹ v ∈ V ⟹ W v ∙ r x = (if fst x + snd x = v then 1 else 0)) ⟹ 2 * n - 1 ≤ dim S | 2n - 1 attained sums, each demanding its own independent witness direction | — | (rule addition_rank_grows) | method |


<!-- ============================================================================
     C3 -- COMPOSITIONAL (Compositional.thy): factored vs partition capacity gap.
     ============================================================================ -->

# theorem CoveringCard
> The canonical covering set -- the base assignment plus each single-attribute flip -- has exactly card A + 1 elements: the O(A) sample budget of the factored code. Cites `covering_card`.

## imports
| Theory        |
|---------------|
| Compositional |

## goal
| Statement |
|-----------|
| finite A ⟹ card (covering A) = card A + 1 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite A ⟹ card (covering A) = card A + 1 | the flips are injective and distinct from the base | — | (rule covering_card) | method |


# theorem FactoredIdentification
> C3(b), factored side: two factored readouts agreeing on the covering set agree on EVERY assignment -- fitting A + 1 examples pins all 2^A outputs, exact compositional generalization. Cites `factored_identification`.

## imports
| Theory        |
|---------------|
| Compositional |

## goal
| Statement |
|-----------|
| finite A ⟹ (⋀T. T ∈ covering A ⟹ fpred θ θ0 T = fpred θ' θ0' T) ⟹ S ⊆ A ⟹ fpred θ θ0 S = fpred θ' θ0' S |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite A ⟹ (⋀T. T ∈ covering A ⟹ fpred θ θ0 T = fpred θ' θ0' T) ⟹ S ⊆ A ⟹ fpred θ θ0 S = fpred θ' θ0' S | the base fixes the bias, each flip fixes a weight, linearity extends | — | (rule factored_identification) | method |


# theorem PartitionNoGeneralization
> C3(b), partition side: for ANY target and any unseen combination, two partition readouts fit the training set exactly yet disagree on the held-out cell -- the unseen cell is undetermined (chance). Cites `partition_no_generalization`.

## imports
| Theory        |
|---------------|
| Compositional |

## goal
| Statement |
|-----------|
| S0 ∉ Train ⟹ ∃w w'. (∀S∈Train. w S = (T::'i set ⇒ real) S) ∧ (∀S∈Train. w' S = T S) ∧ w S0 ≠ w' S0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | S0 ∉ Train ⟹ ∃w w'. (∀S∈Train. w S = (T::'i set ⇒ real) S) ∧ (∀S∈Train. w' S = T S) ∧ w S0 ≠ w' S0 | the unseen cell's output is a free parameter | — | (rule partition_no_generalization) | method |


# theorem FactoredSampleComplexity
> C3(c), factored side packaged: there IS a training set of card A + 1 assignments whose fit determines the factored readout on all of Pow A. Cites `factored_sample_complexity`.

## imports
| Theory        |
|---------------|
| Compositional |

## goal
| Statement |
|-----------|
| finite A ⟹ ∃Cov⊆Pow A. card Cov = card A + 1 ∧ (∀θ θ0 τ τ0. (∀T∈Cov. fpred θ θ0 T = fpred τ τ0 T) ⟶ (∀S∈Pow A. fpred θ θ0 S = fpred τ τ0 S)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite A ⟹ ∃Cov⊆Pow A. card Cov = card A + 1 ∧ (∀θ θ0 τ τ0. (∀T∈Cov. fpred θ θ0 T = fpred τ τ0 T) ⟶ (∀S∈Pow A. fpred θ θ0 S = fpred τ τ0 S)) | the canonical covering set is the witness | — | (rule factored_sample_complexity) | method |


# theorem PartitionNeedsAllCells
> C3(c), partition side: any training set with fewer than 2^A cells leaves some combination whose output is a free parameter for EVERY target -- the partition code needs Omega(2^A) samples. Cites `partition_needs_all_cells`.

## imports
| Theory        |
|---------------|
| Compositional |

## goal
| Statement |
|-----------|
| finite A ⟹ Train ⊆ Pow A ⟹ card Train < 2 ^ card A ⟹ ∃S0∈Pow A - Train. ∀T::'i set ⇒ real. ∃w w'. (∀S∈Train. w S = T S) ∧ (∀S∈Train. w' S = T S) ∧ w S0 ≠ w' S0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite A ⟹ Train ⊆ Pow A ⟹ card Train < 2 ^ card A ⟹ ∃S0∈Pow A - Train. ∀T::'i set ⇒ real. ∃w w'. (∀S∈Train. w S = T S) ∧ (∀S∈Train. w' S = T S) ∧ w S0 ≠ w' S0 | counting finds an unseen cell; its output is free | — | (rule partition_needs_all_cells) | method |


# theorem ConjunctionSingleThreshold
> C3(a), factored side: the conjunction over S0 is ONE linear-threshold rule on the factored code -- unit weights on S0, threshold card S0. Cites `conjunction_single_threshold`.

## imports
| Theory        |
|---------------|
| Compositional |

## goal
| Statement |
|-----------|
| finite S0 ⟹ (S0 ⊆ S) ⟷ (real (card S0) ≤ (∑i∈S0. if i ∈ S then (1::real) else 0)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite S0 ⟹ (S0 ⊆ S) ⟷ (real (card S0) ≤ (∑i∈S0. if i ∈ S then (1::real) else 0)) | the sum counts the satisfied conjuncts; hitting card S0 means all of them | — | (rule conjunction_single_threshold) | method |


# theorem ConjunctionPartitionCells
> C3(a), partition side: the same conjunction occupies one partition cell per positive combination -- exactly 2^(card A - card S0) cells, exponentially many. Cites `conjunction_partition_cells`.

## imports
| Theory        |
|---------------|
| Compositional |

## goal
| Statement |
|-----------|
| finite A ⟹ S0 ⊆ A ⟹ card {S ∈ Pow A. S0 ⊆ S} = 2 ^ (card A - card S0) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite A ⟹ S0 ⊆ A ⟹ card {S ∈ Pow A. S0 ⊆ S} = 2 ^ (card A - card S0) | supersets of S0 in Pow A biject with subsets of the complement | — | (rule conjunction_partition_cells) | method |


<!-- ============================================================================
     C2 -- CRYSTALLIZATION (Crystallization.thy): when a rule collapses to one concept.
     ============================================================================ -->

# theorem RegionConvex
> A rule's firing region -- the intersection of its constraint half-spaces -- is convex. Cites `region_convex`.

## imports
| Theory          |
|-----------------|
| Crystallization |

## goal
| Statement |
|-----------|
| convex (region u b S) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | convex (region u b S) | an intersection of half-spaces is convex | — | (rule region_convex) | method |


# theorem RegionSingle
> The degenerate exact case: a single-constraint rule IS a half-space. Cites `region_single`.

## imports
| Theory          |
|-----------------|
| Crystallization |

## goal
| Statement |
|-----------|
| region u b {c} = {r. b c ≤ u c ∙ r} |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | region u b {c} = {r. b c ≤ u c ∙ r} | one constraint, one half-space | — | (rule region_single) | method |


# theorem RedundantCollapseExact
> C2 exact direction: if the other constraints are jointly redundant -- the region already equals one constraint's half-space -- crystallization into a single concept direction is exact. Cites `redundant_collapse_exact`.

## imports
| Theory          |
|-----------------|
| Crystallization |

## goal
| Statement |
|-----------|
| c ∈ S ⟹ region u b S = region u b {c} ⟹ ∃w t. region u b S = {r. t ≤ w ∙ r} |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | c ∈ S ⟹ region u b S = region u b {c} ⟹ ∃w t. region u b S = {r. t ≤ w ∙ r} | the surviving constraint is the collapsed concept | — | (rule redundant_collapse_exact) | method |


# theorem MidpointBlocksCollapse
> C2 obstruction: two points outside R whose midpoint lies inside R rule out EVERY half-space representation of R -- half-space complements are convex. The representation-independent core of crystallization inexactness. Cites `midpoint_blocks_collapse`.

## imports
| Theory          |
|-----------------|
| Crystallization |

## goal
| Statement |
|-----------|
| q1 ∉ R ⟹ q2 ∉ R ⟹ midpoint q1 q2 ∈ R ⟹ ¬ (∃w t. R = {r. t ≤ w ∙ r}) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | q1 ∉ R ⟹ q2 ∉ R ⟹ midpoint q1 q2 ∈ R ⟹ ¬ (∃w t. R = {r. t ≤ w ∙ r}) | a half-space complement is convex, so it would contain the midpoint | — | (rule midpoint_blocks_collapse) | method |


# theorem EssentialWitness
> Every essential constraint supplies a witness: a point satisfying all OTHER constraints but violating the region -- the conjecture's "point near the facet, just outside". Cites `essential_witness`.

## imports
| Theory          |
|-----------------|
| Crystallization |

## goal
| Statement |
|-----------|
| essential u b S c ⟹ ∃q. q ∈ region u b (S - {c}) ∧ q ∉ region u b S |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | essential u b S c ⟹ ∃q. q ∈ region u b (S - {c}) ∧ q ∉ region u b S | dropping an essential constraint strictly grows the region | — | (rule essential_witness) | method |


# theorem TwoEssentialFacetsBlock
> C2 main obstruction on its stated domain: two essential constraints whose witnesses straddle the region (midpoint inside) block the collapse -- the rule indicator equals NO single half-space indicator. Cites `two_essential_facets_block`.

## imports
| Theory          |
|-----------------|
| Crystallization |

## goal
| Statement |
|-----------|
| essential u b S c1 ⟹ essential u b S c2 ⟹ q1 ∈ region u b (S - {c1}) ⟹ q1 ∉ region u b S ⟹ q2 ∈ region u b (S - {c2}) ⟹ q2 ∉ region u b S ⟹ midpoint q1 q2 ∈ region u b S ⟹ ¬ (∃w t. region u b S = {r. t ≤ w ∙ r}) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | essential u b S c1 ⟹ essential u b S c2 ⟹ q1 ∈ region u b (S - {c1}) ⟹ q1 ∉ region u b S ⟹ q2 ∈ region u b (S - {c2}) ⟹ q2 ∉ region u b S ⟹ midpoint q1 q2 ∈ region u b S ⟹ ¬ (∃w t. region u b S = {r. t ≤ w ∙ r}) | the straddling pair feeds the midpoint obstruction | — | (rule two_essential_facets_block) | method |


# theorem QuadrantEssentialFirst
> The worked instance, facet one: in the quadrant rule over distinct basis directions both constraints matter -- dropping the first admits a violating witness. Cites `quadrant_essential(1)`.

## imports
| Theory          |
|-----------------|
| Crystallization |

## goal
| Statement |
|-----------|
| i ∈ Basis ⟹ j ∈ Basis ⟹ i ≠ j ⟹ essential (quadrant_dirs i j) (λ_. 0) {0, 1} 0 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | i ∈ Basis ⟹ j ∈ Basis ⟹ i ≠ j ⟹ essential (quadrant_dirs i j) (λ_. 0) {0, 1} 0 | the witness j - i satisfies facet two and violates facet one | — | (rule quadrant_essential(1)) | method |


# theorem QuadrantEssentialSecond
> The worked instance, facet two: symmetrically, dropping the second constraint admits the witness i - j. Cites `quadrant_essential(2)`.

## imports
| Theory          |
|-----------------|
| Crystallization |

## goal
| Statement |
|-----------|
| i ∈ Basis ⟹ j ∈ Basis ⟹ i ≠ j ⟹ essential (quadrant_dirs i j) (λ_. 0) {0, 1} 1 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | i ∈ Basis ⟹ j ∈ Basis ⟹ i ≠ j ⟹ essential (quadrant_dirs i j) (λ_. 0) {0, 1} 1 | the witness i - j satisfies facet one and violates facet two | — | (rule quadrant_essential(2)) | method |


# theorem QuadrantNotHalfspace
> C2's worked inexactness: the quadrant -- a genuinely two-facet rule -- provably equals NO single half-space; crystallizing it into one concept direction is inexact, with concrete witnesses j - i, i - j and midpoint 0. Cites `quadrant_not_halfspace`.

## imports
| Theory          |
|-----------------|
| Crystallization |

## goal
| Statement |
|-----------|
| i ∈ Basis ⟹ j ∈ Basis ⟹ i ≠ j ⟹ ¬ (∃w t. region (quadrant_dirs i j) (λ_. 0) {0, 1} = {r. t ≤ w ∙ r}) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | i ∈ Basis ⟹ j ∈ Basis ⟹ i ≠ j ⟹ ¬ (∃w t. region (quadrant_dirs i j) (λ_. 0) {0, 1} = {r. t ≤ w ∙ r}) | the straddling witnesses meet at the origin inside the quadrant | — | (rule quadrant_not_halfspace) | method |


<!-- ============================================================================
     C6 -- GAUGE (Gauge.thy): grounding collapses the continuous gauge to a finite one.
     ============================================================================ -->

# theorem UngroundedGaugeMembership
> C6 ungrounded freedom, membership side: rotating residuals and concept directions together preserves every membership -- decisions cannot see the gauge. Cites `ungrounded_gauge_membership`.

## imports
| Theory |
|--------|
| Gauge  |

## goal
| Statement |
|-----------|
| orthogonal_transformation R ⟹ fires (λc. R (u c)) b c (R r) = fires u b c r |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | orthogonal_transformation R ⟹ fires (λc. R (u c)) b c (R r) = fires u b c r | orthogonal maps preserve inner products, hence every half-space test | — | (rule ungrounded_gauge_membership) | method |


# theorem UngroundedGaugeDecoder
> C6 ungrounded freedom, decoder side: the argmax decode is invariant under any orthogonal gauge applied to residuals and readout directions together. Cites `ungrounded_gauge_decoder`.

## imports
| Theory |
|--------|
| Gauge  |

## goal
| Statement |
|-----------|
| orthogonal_transformation R ⟹ amax V (λv. R (U v)) (R r) = amax V U r |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | orthogonal_transformation R ⟹ amax V (λv. R (U v)) (R r) = amax V U r | every score comparison is an inner product, preserved by the gauge | — | (rule ungrounded_gauge_decoder) | method |


# theorem HreflectOrthogonal
> The Householder reflection along any unit direction is an orthogonal transformation -- the generator of the explicit infinite family. Cites `hreflect_orthogonal`.

## imports
| Theory |
|--------|
| Gauge  |

## goal
| Statement |
|-----------|
| n ∙ n = 1 ⟹ orthogonal_transformation (hreflect n) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | n ∙ n = 1 ⟹ orthogonal_transformation (hreflect n) | linear by construction; the cross terms cancel against the unit norm | — | (rule hreflect_orthogonal) | method |


# theorem UngroundedGaugeInfinite
> C6's "continuous": for DIM at least 2 the ungrounded gauge group is INFINITE -- witnessed by the Householder reflections along the unit vectors of a coordinate plane, injectively parametrized. Cites `ungrounded_gauge_infinite`.

## imports
| Theory |
|--------|
| Gauge  |

## goal
| Statement |
|-----------|
| 2 ≤ DIM('a::euclidean_space) ⟹ infinite {R::'a ⇒ 'a. orthogonal_transformation R} |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | 2 ≤ DIM('a::euclidean_space) ⟹ infinite {R::'a ⇒ 'a. orthogonal_transformation R} | distinct reflection axes act differently on the first basis vector | — | (rule ungrounded_gauge_infinite) | method |


# theorem AlignmentKillsGauge
> C6 grounded, exact case: an orthogonal gauge that fixes a SPANNING readout frame pointwise is the identity -- decisions plus exact alignment leave no gauge freedom at all (the generically trivial stabilizer). Cites `alignment_kills_gauge`.

## imports
| Theory |
|--------|
| Gauge  |

## goal
| Statement |
|-----------|
| orthogonal_transformation R ⟹ (⋀v. v ∈ V ⟹ R ((Uout::'v ⇒ 'a::euclidean_space) v) = Uout v) ⟹ span (Uout ` V) = UNIV ⟹ R = id |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | orthogonal_transformation R ⟹ (⋀v. v ∈ V ⟹ R ((Uout::'v ⇒ 'a::euclidean_space) v) = Uout v) ⟹ span (Uout ` V) = UNIV ⟹ R = id | a linear map fixing a spanning set fixes everything | — | (rule alignment_kills_gauge) | method |


# theorem SignGaugeInvolutive
> C6 grounded, sign case: if alignment pins each frame direction only up to sign, every consistent gauge is an involution -- applying it twice restores every residual. Cites `sign_gauge_involutive`.

## imports
| Theory |
|--------|
| Gauge  |

## goal
| Statement |
|-----------|
| linear R ⟹ (⋀v. v ∈ B ⟹ R v = v ∨ R v = - v) ⟹ span B = (UNIV :: 'a::euclidean_space set) ⟹ R ∘ R = id |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | linear R ⟹ (⋀v. v ∈ B ⟹ R v = v ∨ R v = - v) ⟹ span B = (UNIV :: 'a::euclidean_space set) ⟹ R ∘ R = id | both sign choices square to the identity on the spanning set | — | (rule sign_gauge_involutive) | method |


# theorem SignGaugeFinite
> C6's collapse: only FINITELY many linear gauges send each basis direction to itself or its negation (at most 2^d sign choices) -- versus the infinite ungrounded group. Grounding collapses a continuous gauge to a finite one. Cites `sign_gauge_finite`.

## imports
| Theory |
|--------|
| Gauge  |

## goal
| Statement |
|-----------|
| finite {R::'a::euclidean_space ⇒ 'a. linear R ∧ (∀v∈Basis. R v = v ∨ R v = - v)} |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite {R::'a::euclidean_space ⇒ 'a. linear R ∧ (∀v∈Basis. R v = v ∨ R v = - v)} | a linear map is determined by its basis values, of which there are at most 2^d sign patterns | — | (rule sign_gauge_finite) | method |


<!-- ============================================================================
     C7 -- CROSS-TOKEN EQUALITY (CrossToken.thy): linear-impossible, bilinear-easy.
     Follow-on from the Wyly review (pil PR #10); grounds ground_multipos / ground_relational.
     ============================================================================ -->

# theorem EqualityNotAdditive
> C7(i), the 4-point core: an additive score g(t1) + h(t2) that clears theta exactly on the diagonal is contradictory on the four pairs from two distinct tokens -- matched and mismatched pairs have the same total. Dimension-free. Cites `equality_not_additive`.

## imports
| Theory     |
|------------|
| CrossToken |

## goal
| Statement |
|-----------|
| x ∈ V ⟹ y ∈ V ⟹ x ≠ y ⟹ (⋀t1 t2. t1 ∈ V ⟹ t2 ∈ V ⟹ ((theta::real) ≤ g t1 + h t2) ⟷ (t1 = t2)) ⟹ False |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | x ∈ V ⟹ y ∈ V ⟹ x ≠ y ⟹ (⋀t1 t2. t1 ∈ V ⟹ t2 ∈ V ⟹ ((theta::real) ≤ g t1 + h t2) ⟷ (t1 = t2)) ⟹ False | the two matched sums and the two mismatched sums total the same yet straddle 2*theta | — | (rule equality_not_additive[where V = V and x = x and y = y and theta = theta and g = g and h = h]) | method |


# theorem EqualityNotLinear
> C7(i) packaged: over any vocabulary with two tokens there is NO additive equality decider at all -- which subsumes every linear head over concatenated per-position features in any dimension. Cites `equality_not_linear`.

## imports
| Theory     |
|------------|
| CrossToken |

## goal
| Statement |
|-----------|
| x ∈ V ⟹ y ∈ V ⟹ x ≠ y ⟹ ¬ (∃g h theta. ∀t1∈V. ∀t2∈V. ((theta::real) ≤ g t1 + h t2) ⟷ (t1 = t2)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | x ∈ V ⟹ y ∈ V ⟹ x ≠ y ⟹ ¬ (∃g h theta. ∀t1∈V. ∀t2∈V. ((theta::real) ≤ g t1 + h t2) ⟷ (t1 = t2)) | any such decider instantiates the 4-point contradiction | — | (rule equality_not_linear) | method |


# theorem EqualityNotResidualLinear
> C7(ii): a linear readout over concatenated per-position RESIDUALS is an additive reader, hence cannot decide cross-token equality -- the grounded reader ground_multipos trained, ruled out at every dimension. Cites `equality_not_residual_linear`.

## imports
| Theory     |
|------------|
| CrossToken |

## goal
| Statement |
|-----------|
| x ∈ V ⟹ y ∈ V ⟹ x ≠ y ⟹ ¬ (∃theta. ∀t1∈V. ∀t2∈V. ((theta::real) ≤ (W1::'a::real_inner) ∙ r1 t1 + (W2::'a) ∙ r2 t2) ⟷ (t1 = t2)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | x ∈ V ⟹ y ∈ V ⟹ x ≠ y ⟹ ¬ (∃theta. ∀t1∈V. ∀t2∈V. ((theta::real) ≤ (W1::'a::real_inner) ∙ r1 t1 + (W2::'a) ∙ r2 t2) ⟷ (t1 = t2)) | the per-position inner products are the g and h of the additive impossibility | — | (rule equality_not_residual_linear) | method |


# theorem EqualityNotMembershipLinear
> C7(ii): neither can any bank of hyperplane concepts read per-position and combined linearly -- concept memberships are still additive across positions. The wall is structural, not a capacity limit. Cites `equality_not_membership_linear`.

## imports
| Theory     |
|------------|
| CrossToken |

## goal
| Statement |
|-----------|
| x ∈ V ⟹ y ∈ V ⟹ x ≠ y ⟹ ¬ (∃theta. ∀t1∈V. ∀t2∈V. ((theta::real) ≤ (∑c∈C. w1 c * (if fires u bb c (r1 t1) then 1 else 0)) + (∑c∈C. w2 c * (if fires u bb c (r2 t2) then 1 else 0))) ⟷ (t1 = t2)) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | x ∈ V ⟹ y ∈ V ⟹ x ≠ y ⟹ ¬ (∃theta. ∀t1∈V. ∀t2∈V. ((theta::real) ≤ (∑c∈C. w1 c * (if fires u bb c (r1 t1) then 1 else 0)) + (∑c∈C. w2 c * (if fires u bb c (r2 t2) then 1 else 0))) ⟷ (t1 = t2)) | the two membership sums are again additive per-position scores | — | (rule equality_not_membership_linear) | method |


# theorem EqualityBilinear
> C7(iii): with orthonormal per-token features the bilinear score IS the equality indicator -- threshold one half, margin one half. The PR's soft-eq match and the QK-attention primitive. Cites `equality_bilinear`.

## imports
| Theory     |
|------------|
| CrossToken |

## goal
| Statement |
|-----------|
| (⋀t1 t2. t1 ∈ V ⟹ t2 ∈ V ⟹ phi t1 ∙ phi t2 = (if t1 = t2 then 1 else 0)) ⟹ t1 ∈ V ⟹ t2 ∈ V ⟹ (1 / 2 ≤ phi t1 ∙ phi t2) ⟷ (t1 = t2) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (⋀t1 t2. t1 ∈ V ⟹ t2 ∈ V ⟹ phi t1 ∙ phi t2 = (if t1 = t2 then 1 else 0)) ⟹ t1 ∈ V ⟹ t2 ∈ V ⟹ (1 / 2 ≤ phi t1 ∙ phi t2) ⟷ (t1 = t2) | the score is 1 on the diagonal and 0 off it | — | (rule equality_bilinear) | method |


# theorem BilinearReaderExists
> C7(iii) existence: orthonormal token features -- hence an exact bilinear equality reader -- exist whenever card V fits the dimension. Paired with the impossibility, the separation theorem for the retrieved/computed frontier. Cites `bilinear_reader_exists`.

## imports
| Theory     |
|------------|
| CrossToken |

## goal
| Statement |
|-----------|
| finite V ⟹ card V ≤ DIM('a::euclidean_space) ⟹ ∃phi::'t ⇒ 'a. ∀t1∈V. ∀t2∈V. (1 / 2 ≤ phi t1 ∙ phi t2) ⟷ (t1 = t2) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite V ⟹ card V ≤ DIM('a::euclidean_space) ⟹ ∃phi::'t ⇒ 'a. ∀t1∈V. ∀t2∈V. (1 / 2 ≤ phi t1 ∙ phi t2) ⟷ (t1 = t2) | inject the vocabulary into the orthonormal basis | — | (rule bilinear_reader_exists) | method |


# theorem ConjunctionRuleIsProduct
> C7(iv): a conjunction of per-position concepts fires on a PRODUCT set -- the extents of its two position groups. Conjunctive rules over per-position memberships can only carve products. Cites `conjunction_rule_is_product`.

## imports
| Theory     |
|------------|
| CrossToken |

## goal
| Statement |
|-----------|
| {(r1, r2). (∀c∈S1. r1 ∈ Hspace u bb c) ∧ (∀c∈S2. r2 ∈ Hspace u bb c)} = extent u bb S1 × extent u bb S2 |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | {(r1, r2). (∀c∈S1. r1 ∈ Hspace u bb c) ∧ (∀c∈S2. r2 ∈ Hspace u bb c)} = extent u bb S1 × extent u bb S2 | the two conjunct groups constrain the two coordinates independently | — | (rule conjunction_rule_is_product) | method |


# theorem EqualityNeedsCardRules
> C7(iv) counting: any family of product rules covering the diagonal without firing off-diagonal needs at least card V rules -- each sound rule pins one token. One symbolic eq_atom replaces card V geometric rules: the case for the unified substrate. Cites `equality_needs_card_rules`.

## imports
| Theory     |
|------------|
| CrossToken |

## goal
| Statement |
|-----------|
| finite I ⟹ (⋀t. t ∈ V ⟹ ∃i∈I. t ∈ A i ∧ t ∈ B i) ⟹ (⋀i t1 t2. i ∈ I ⟹ t1 ∈ V ⟹ t2 ∈ V ⟹ t1 ∈ A i ⟹ t2 ∈ B i ⟹ t1 = t2) ⟹ card V ≤ card I |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | finite I ⟹ (⋀t. t ∈ V ⟹ ∃i∈I. t ∈ A i ∧ t ∈ B i) ⟹ (⋀i t1 t2. i ∈ I ⟹ t1 ∈ V ⟹ t2 ∈ V ⟹ t1 ∈ A i ⟹ t2 ∈ B i ⟹ t1 = t2) ⟹ card V ≤ card I | picking each token's covering rule is injective: a sound rule cannot serve two tokens | — | (rule equality_needs_card_rules) | method |


# theorem EqualityCardRulesSuffice
> C7(iv) tightness: the card V singleton rules cover the diagonal soundly -- the product-rule cost of equality is exactly card V. Cites `equality_card_rules_suffice`.

## imports
| Theory     |
|------------|
| CrossToken |

## goal
| Statement |
|-----------|
| (∀t∈V. ∃i∈V. t ∈ {i} ∧ t ∈ {i}) ∧ (∀i∈V. ∀t1∈V. ∀t2∈V. t1 ∈ {i} ⟶ t2 ∈ {i} ⟶ t1 = t2) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (∀t∈V. ∃i∈V. t ∈ {i} ∧ t ∈ {i}) ∧ (∀i∈V. ∀t1∈V. ∀t2∈V. t1 ∈ {i} ⟶ t2 ∈ {i} ⟶ t1 = t2) | one singleton rule per token covers its diagonal pair and nothing else | — | (rule equality_card_rules_suffice) | method |


<!-- ============================================================================
     C8 -- GRADED CONSOLIDATION (GradedConsolidation.thy): the middle of the omega axis.
     Follow-on from the Wyly review (pil PR #10); grounds wyly_incidence + the Adam finding.
     ============================================================================ -->

# theorem InnerDriftBound
> Drift perturbs scores by at most D * norm r: the Cauchy-Schwarz step every certificate below rests on. Cites `inner_drift_bound`.

## imports
| Theory              |
|---------------------|
| GradedConsolidation |

## goal
| Statement |
|-----------|
| norm (v' - v) ≤ D ⟹ ¦v' ∙ r - v ∙ r¦ ≤ D * norm r |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | norm (v' - v) ≤ D ⟹ ¦v' ∙ r - v ∙ r¦ ≤ D * norm r | the score difference is the drift vector read against r | — | (rule inner_drift_bound) | method |


# theorem AnchoredDriftBound
> C8 core: at a stationary point of task-loss + quadratic incidence anchor, the drift obeys norm (p - pbar) ≤ G / (2*lam*omega) -- protection scales as one over the incidence importance. Cites `anchored_drift_bound`.

## imports
| Theory              |
|---------------------|
| GradedConsolidation |

## goal
| Statement |
|-----------|
| gL + (2 * lam * om) *\<^sub>R (p - pbar) = 0 ⟹ norm gL ≤ G ⟹ 0 < lam ⟹ 0 < om ⟹ norm (p - pbar) ≤ G / (2 * lam * om) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | gL + (2 * lam * om) *\<^sub>R (p - pbar) = 0 ⟹ norm gL ≤ G ⟹ 0 < lam ⟹ 0 < om ⟹ norm (p - pbar) ≤ G / (2 * lam * om) | the anchor force balances the bounded task force | — | (rule anchored_drift_bound) | method |


# theorem FreezeLimit
> The explicit freeze schedule: incidence omega ≥ G/(2*lam*eps) caps the drift at eps -- the binary freeze of C4 is the omega -> infinity limit, quantitatively. Cites `freeze_limit`.

## imports
| Theory              |
|---------------------|
| GradedConsolidation |

## goal
| Statement |
|-----------|
| gL + (2 * lam * om) *\<^sub>R (p - pbar) = 0 ⟹ norm gL ≤ G ⟹ 0 < lam ⟹ 0 < om ⟹ 0 < eps ⟹ G / (2 * lam * eps) ≤ om ⟹ norm (p - pbar) ≤ eps |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | gL + (2 * lam * om) *\<^sub>R (p - pbar) = 0 ⟹ norm gL ≤ G ⟹ 0 < lam ⟹ 0 < om ⟹ 0 < eps ⟹ G / (2 * lam * eps) ≤ om ⟹ norm (p - pbar) ≤ eps | plug the omega threshold into the drift bound | — | (rule freeze_limit) | method |


# theorem DriftedMembershipPreserved
> The membership certificate: a concept whose direction drifted at most D keeps every membership whose margin beats D * norm r -- exactly, per input. Cites `drifted_membership_preserved`.

## imports
| Theory              |
|---------------------|
| GradedConsolidation |

## goal
| Statement |
|-----------|
| norm (u' c - u c) ≤ D ⟹ D * norm r < ¦u c ∙ r - b c¦ ⟹ fires u' b c r = fires u b c r |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | norm (u' c - u c) ≤ D ⟹ D * norm r < ¦u c ∙ r - b c¦ ⟹ fires u' b c r = fires u b c r | the score moves less than the margin, so the half-space test cannot flip | — | (rule drifted_membership_preserved) | method |


# theorem AmaxStrictWinner
> A strict winner is the unique argmax -- the decode-side helper. Cites `amax_strict_winner`.

## imports
| Theory              |
|---------------------|
| GradedConsolidation |

## goal
| Statement |
|-----------|
| v0 ∈ V ⟹ (⋀w. w ∈ V ⟹ w ≠ v0 ⟹ U w ∙ r < U v0 ∙ r) ⟹ amax V U r = {v0} |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | v0 ∈ V ⟹ (⋀w. w ∈ V ⟹ w ≠ v0 ⟹ U w ∙ r < U v0 ∙ r) ⟹ amax V U r = {v0} | beating every rival strictly is exactly unique maximality | — | (rule amax_strict_winner) | method |


# theorem DriftedDecodePreserved
> The decode certificate: if every readout direction drifted at most D and the winner's margin beats 2 * D * norm r, the argmax decision is identical before and after -- the PIC_Prune / PIC_Quant triangle shape with drift as the perturbation. Cites `drifted_decode_preserved`.

## imports
| Theory              |
|---------------------|
| GradedConsolidation |

## goal
| Statement |
|-----------|
| (⋀v. v ∈ V ⟹ norm (U' v - U v) ≤ D) ⟹ v0 ∈ V ⟹ (⋀w. w ∈ V ⟹ w ≠ v0 ⟹ U w ∙ r + 2 * (D * norm r) < U v0 ∙ r) ⟹ amax V U' r = {v0} ∧ amax V U r = {v0} |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (⋀v. v ∈ V ⟹ norm (U' v - U v) ≤ D) ⟹ v0 ∈ V ⟹ (⋀w. w ∈ V ⟹ w ≠ v0 ⟹ U w ∙ r + 2 * (D * norm r) < U v0 ∙ r) ⟹ amax V U' r = {v0} ∧ amax V U r = {v0} | winner loses at most one drift budget, rivals gain at most one | — | (rule drifted_decode_preserved) | method |


# theorem GradedMembershipStability
> C8 composed: stationarity of the omega-anchored objective + gradient bound + membership margin give EXACT per-input stability at finite omega -- C4's zero forgetting, margin-gated; the required margin shrinks to zero as omega grows. Cites `graded_membership_stability`.

## imports
| Theory              |
|---------------------|
| GradedConsolidation |

## goal
| Statement |
|-----------|
| gL + (2 * lam * om) *\<^sub>R (u' c - u c) = 0 ⟹ norm gL ≤ G ⟹ 0 < lam ⟹ 0 < om ⟹ G / (2 * lam * om) * norm r < ¦u c ∙ r - b c¦ ⟹ fires u' b c r = fires u b c r |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | gL + (2 * lam * om) *\<^sub>R (u' c - u c) = 0 ⟹ norm gL ≤ G ⟹ 0 < lam ⟹ 0 < om ⟹ G / (2 * lam * om) * norm r < ¦u c ∙ r - b c¦ ⟹ fires u' b c r = fires u b c r | chain the anchored drift bound into the membership certificate | — | (rule graded_membership_stability) | method |


# theorem SignUpdatesIgnoreScaling
> The Adam finding as a theorem (signSGD idealization): an arbitrary positive per-step protection factor on the gradient leaves the ENTIRE trajectory unchanged -- multiplicative protection is a provable no-op under sign-normalized updates. Cites `sign_updates_ignore_scaling`.

## imports
| Theory              |
|---------------------|
| GradedConsolidation |

## goal
| Statement |
|-----------|
| (q::nat ⇒ real) 0 = p 0 ⟹ (⋀n. 0 < c n) ⟹ (⋀n. p (Suc n) = p n - eta * sgn (grad n (p n))) ⟹ (⋀n. q (Suc n) = q n - eta * sgn (c n * grad n (q n))) ⟹ q n = p n |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | (q::nat ⇒ real) 0 = p 0 ⟹ (⋀n. 0 < c n) ⟹ (⋀n. p (Suc n) = p n - eta * sgn (grad n (p n))) ⟹ (⋀n. q (Suc n) = q n - eta * sgn (c n * grad n (q n))) ⟹ q n = p n | positive scaling never changes the sign, so every step coincides by induction | — | (rule sign_updates_ignore_scaling) | method |


# theorem PlainUpdateScales
> The contrast: a plain gradient step shrinks linearly with the protection factor -- the mechanism scaling was wrongly expected to provide under Adam. Protection must enter the loss (the anchor), not the gradient magnitude. Cites `plain_update_scales`.

## imports
| Theory              |
|---------------------|
| GradedConsolidation |

## goal
| Statement |
|-----------|
| ¦((p::real) - eta * (c * g)) - p¦ = ¦c¦ * ¦eta * g¦ |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_show | ¦((p::real) - eta * (c * g)) - p¦ = ¦c¦ * ¦eta * g¦ | the step is literally the scaled gradient | — | (rule plain_update_scales) | method |
