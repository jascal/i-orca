# ConceptGrounding — the PIC/PIL grounding conjectures, kernel-checked

The work package of `../../..//PIC_PIL_GROUNDING_CONJECTURES.md` (workspace root): six formalizable
conjectures that fell out of the concept-grounding experiments (the concept-as-hyperplane bridge,
`pil` branch `feat/concept-rule-learner`; Coppice proposal §10). Each is a theorem about the
**geometry** of grounded concepts — the objects the existing packing corpus
(`tropical/DecodeCapacity.thy`, `tropical/RoutingRank.thy`, `superposition/RoutingWelch.thy`)
already reasons over. This corpus proves them, in the work package's priority order
(C4 → C1 → C5 → C3 → C2 → C6), as six substrate theories under one `ConceptGrounding` session.

## Discipline (inherited from the work package)

- **`proved` vs `empirical` stay separate.** The grounding *experiments* are `empirical`
  (e.g. "grammar is ~0.95 linearly decodable across pythia/qwen 70M–7B"). The theorems here are what
  that geometry *would provably satisfy* over a **stated domain** (finite K concepts, half-space
  membership, linear/argmax readout). A proved C-theorem is **not** evidence about any specific
  model; the empirical ceiling is **not** a proof.
- **State the domain.** Every theorem names its regime in its hypotheses. The leap to "therefore
  real LLMs" stays `open` in every case.
- **No necessity from a plateau.** Where a bound is a method limit we say so
  (see the C5 premise-strengthening note — the headline example).

## Tag ledger

| claim | tag | artifact |
|---|---|---|
| C4 (i) frozen memberships invariant under masked training, incl. whole trajectories | `proved` | `Consolidation.thy` `frozen_membership_invariant`, `frozen_membership_trajectory` |
| C4 (ii) decisions reading only frozen memberships preserved exactly | `proved` | `frozen_decision_preserved` |
| C4 (iii) reachable frame change spans ≤ card(K−F) dims; plastic boundaries ≤ card P dims | `proved` | `reachable_change_dim`, `plastic_boundary_dim` |
| C4 (cor) retain-rank + learn-rank ≤ K | `proved` | `retain_learn_budget` |
| C1 (a) σ-fibers = arrangement cells: cover, disjoint, stated intersection, convex | `proved` | `ConceptCells.thy` `cell_self`/`cells_cover`/`cells_disjoint`/`cell_as_intersection`/`cell_convex` |
| C1 (b) FCA Galois connection, closure, extent convexity, concept anti-isomorphism | `proved` | `fca_galois`, `fca_closure_extensive`, `extent_convex`, `concept_anti_iso` |
| C1 (b-bridge) intent of a nonempty cell = its sign vector | `proved` | `cell_intent_recovers_sign` |
| C1 (c) argmax decoder piecewise-constant on cells; concept arrangement refines decoder | `proved` | `amax_piecewise_constant`, `concept_refines_decoder` |
| C1 full polyhedral **face-lattice order** (closure order, Zaslavsky) | `open` | not formalized — cell/sign-vector + FCA-order level only |
| C5 rank floor under **exact (calibrated) readout**: card(g\`X) ≤ dim S — i.e. ρ ≥ rank M_g | `proved` | `ComputedRank.thy` `computed_rank_lower_bound` |
| C5 as stated over **argmax** readout | **false** (bias) / weakened (homogeneous) | header counterexample note; `argmax_rank_one_three_behaviors` (≤3 decisions at ρ=1) |
| C5 retrieval degenerate case: constant g realizable at dim ≤ 1; ≥2 outputs force dim ≥ 2 | `proved` | `retrieval_rank_one`, `computation_needs_rank_two` |
| C5 addition anchor: width-n sum attains 2n−1 outputs ⇒ exact-readout rank ≥ 2^{b+1}−1 | `proved` | `add_range_card`, `addition_rank_grows` |
| C5 measured effective rank (≈4) matches any floor | `empirical` | not claimed — argmax decoding voids the floor (see RESULTS) |
| C3 (b) factored: covering fit ⇒ exact generalization to all 2^A combos | `proved` | `Compositional.thy` `factored_identification`, `factored_exact_generalization` |
| C3 (b) partition: unseen cell undetermined for every target | `proved` | `partition_no_generalization` |
| C3 (c) factored O(A) (card A + 1 covering set); partition Ω(2^A) | `proved` | `factored_sample_complexity`, `partition_needs_all_cells` |
| C3 (a) conjunction = 1 threshold rule vs 2^(A−|S₀|) partition cells | `proved` | `conjunction_single_threshold`, `conjunction_partition_cells` |
| C2 exact direction: joint redundancy ⇒ collapse exact | `proved` | `Crystallization.thy` `redundant_collapse_exact` |
| C2 obstruction: straddling midpoint witnesses ⇒ no half-space equals the rule | `proved` | `midpoint_blocks_collapse`, `two_essential_facets_block` |
| C2 essential constraint ⇒ violating witness exists | `proved` | `essential_witness` |
| C2 worked instance: quadrant has 2 essential facets and is provably no half-space | `proved` | `quadrant_essential`, `quadrant_not_halfspace` |
| C2 witnesses from bare essential+non-parallel (supporting hyperplane); margin-deficit size | `open` | not formalized (stated domain = witnessed straddle) |
| C6 ungrounded gauge: all of O(d) preserves memberships + decodes | `proved` | `Gauge.thy` `ungrounded_gauge_membership`, `ungrounded_gauge_decoder` |
| C6 that gauge is **infinite** for DIM ≥ 2 (explicit Householder family) | `proved` | `hreflect_orthogonal`, `ungrounded_gauge_infinite` |
| C6 exact alignment to a spanning frame ⇒ gauge trivial (R = id) | `proved` | `alignment_kills_gauge` |
| C6 sign alignment ⇒ involutive gauge, finitely many (≤ 2^d) | `proved` | `sign_gauge_involutive`, `sign_gauge_finite` |
| C1–C6 bridge to real-LLM measurements (pythia/qwen ceilings, tiny_math rank, wake_sleep band) | `open`/`empirical` | by design — see Discipline |

## Empirical anchors (NOT proofs; the `empirical` facts the theorems formalize)

| finding | experiment | anchor value |
|---|---|---|
| concepts recover known structure as residual hyperplanes | `ground_threx/lisp/stories/pythia` | recovery 0.95–1.0 |
| grammar linearly present cross-family | pythia + qwen2.5, 70M–7B | CUR ceiling ~0.95 (plateau) |
| computed core higher-rank than retrieved | `ground_lisp` effective rank | arithmetic 2× structural |
| addition is low-rank | `tiny_math` / capacity | rank ≈ 4 |
| factored composes to novel combos; partition memorizes | `compositional` | 0.90 vs 0.69 |
| spare capacity enables continual learning | `wake_sleep` | interior optimum |
