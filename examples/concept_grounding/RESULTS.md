# ConceptGrounding — verification status

The six PIC/PIL grounding conjectures (workspace `PIC_PIL_GROUNDING_CONJECTURES.md`), proved in the
work package's priority order C4 → C1 → C5 → C3 → C2 → C6. See [`PROPOSAL.md`](PROPOSAL.md) for the
tag ledger and [`README.md`](README.md) for the map.

## Layer 1 — structural skeleton (no Isabelle)

```
$ .venv/bin/i-orca verify examples/concept_grounding/concept_grounding.i.orca.md
```
All **50** surface theorems VALID, `formal_fraction_static = 1.000`, 0 frontier holes.

## Layer 2 — kernel check of the substrate (the load-bearing math)

```
$ isabelle build -d examples/concept_grounding -o quick_and_dirty ConceptGrounding
```

`Finished ConceptGrounding`, exit 0, **zero `sorry`** across all six substrate theories
(`Consolidation.thy`, `ConceptCells.thy`, `ComputedRank.thy`, `Compositional.thy`,
`Crystallization.thy`, `Gauge.thy`; Isabelle2025-2, parent `HOL-Analysis`). The `.thy` files are the
hand-authored, kernel-checked substrate; the `.i.orca.md` is the thin i-orca surface, each theorem
discharged by `(rule <lemma>)`.

## Layer 3 — kernel check of the surface itself (end-to-end)

The session also builds `ConceptGrounding_Surface.thy` — the i-orca surface compiled by
`i-orca compile --target isar --document` — so all **50** surface theorems are re-derived inside the
kernel against the substrate (the `provable_opt` pattern): the surface is certified end-to-end, not
just structurally.

Toolchain note: closing this layer surfaced three missing entries in the Isar compiler's
Unicode→escape table (`∙` → `\<bullet>`, `∘` → `\<circ>`, `∄` → `\<nexists>`), now added to
`i_orca/compiler/isar.py` with a regression test — the geometry corpora lean on `∙` everywhere.

## The six theories

| theory | conjecture | what it establishes |
|--------|-----------|---------------------|
| `Consolidation` | C4 | masked training exactly preserves frozen memberships (single step AND whole trajectories) and every decision reading only them; the reachable frame change spans ≤ card(K−F) dims; retain-rank + learn-rank ≤ K |
| `ConceptCells` | C1 | σ-fibers are the arrangement cells (cover, disjoint, stated half-space intersection, convex); the FCA context has the Galois/closure structure with the concept order ANTI-isomorphic; the intent of a nonempty cell recovers its sign vector; the argmax decoder is piecewise-constant on its difference cells and the concept arrangement refines it |
| `ComputedRank` | C5 | exact-readout rank floor card(g\`X) ≤ dim S (= ρ ≥ rank M_g); retrieval realizable at dim ≤ 1 and constancy ⟺ one output; ≥ 2 outputs force dim ≥ 2; homogeneous argmax over 1 dim has ≤ 3 decision sets; width-n addition attains 2n−1 outputs so its exact-readout floor grows with width |
| `Compositional` | C3 | factored code: fitting the card A+1 covering set determines all 2^A outputs (exact held-out generalization); partition code: any unseen cell is a free parameter for every target, so < 2^A samples never determine it; a conjunction is 1 threshold rule vs 2^(A−card S₀) partition cells |
| `Crystallization` | C2 | joint redundancy ⇒ exact collapse; midpoint obstruction: any straddling pair of violators kills EVERY half-space representation; essential constraints always supply violating witnesses; the quadrant instance fully worked (both facets essential, provably no half-space) |
| `Gauge` | C6 | every orthogonal gauge preserves memberships + decodes; that group is INFINITE for DIM ≥ 2 (explicit injective Householder family); exact alignment to a spanning frame forces R = id; sign-only alignment leaves an involutive gauge of finitely many (≤ 2^d) elements |

## Premise-strengthening report (what had to change to close each proof)

The work package asked: *"Report back which premises had to be strengthened to close each proof —
that itself is signal about where the geometric idealization departs from the messy empirical
reality."* The ledger:

- **C4 — none.** The masking linear algebra goes through as conjectured. The only formalization
  choice: "invariant under all subsequent training" is rendered as invariance under arbitrary
  trajectories of masked parameter updates (`frozen_membership_trajectory`) — nothing about
  gradients is needed, only that masking holds each step. The corollary's `rank(U_F)` reads as
  `dim (span (u ` F))` and the budget is stated against `card K` (dimension counting, as proposed).
- **C1 — scoped, not strengthened.** Everything conjectured at the cell/sign-vector level is proved.
  NOT formalized: the full polyhedral **face-lattice order** (faces ordered by closure containment,
  Zaslavsky's framework) — the anti-isomorphism proved is the FCA concept order against
  extent-inclusion, plus the cell↔sign-vector bijection and the intent bridge. The decoder claim (c)
  is proved as refinement ("same concept cell ⇒ same decode" when the decision hyperplanes are among
  the concepts), which is the piecewise-constancy statement actually used downstream.
- **C5 — the headline strengthening.** As stated (argmax decoder), the rank floor is **false**:
  with biases, `argmax_v (v·t − v²/2)` computes nearest-integer over a ONE-dimensional residual —
  unboundedly many outputs at ρ = 1; homogeneously, a 2-dim fan already gives many outputs.
  The floor is true and proved for the **exact (calibrated) readout** regime
  (`W_v · r x = [g x = v]` — the interpolation regime linear probes fit), where
  `rank M_g = card (g ` X)` because distinct one-hot rows are independent. The salvage for the
  homogeneous argmax as conjectured: at ρ = 1 the decoder attains **at most 3** decision sets
  (`argmax_rank_one_three_behaviors`) — "retrieval-like", not constant. Consequence worth keeping:
  the `tiny_math` rank-4 addition head does not contradict the exponential exact-readout floor
  `2^(b+1) − 1`; it *witnesses* that real models decode by argmax, where the floor provably does
  not bind. The "matches measured effective rank" question stays `empirical` by design.
- **C3 — covering set made canonical.** "Trained on a set that covers each attribute" is not enough
  for identification (e.g. {00, 11} covers both attributes of A = 2 but leaves 3 parameters under 2
  equations). Strengthened to the **canonical covering set** {base} ∪ {single flips} of size A + 1,
  which identifies exactly. The partition side and the expressiveness gap go through as conjectured.
- **C2 — witnessed-straddle domain.** The obstruction is proved from a straddling witness pair
  (two violators with midpoint inside), and essential constraints provably supply violators; the
  **construction** of a straddling pair from bare "≥ 2 essential, non-parallel facets" (supporting
  hyperplane + interior-point argument) is left `open`, as is the quantitative margin-deficit bound.
  The worked quadrant instance exhibits the witnesses concretely, so the intended phenomenon is
  kernel-checked end-to-end on the canonical example.
- **C6 — "generic" rendered as exact/sign alignment.** "Distinct singular directions ⇒ finite
  stabilizer" is rendered in two proved regimes: exact pointwise alignment to a spanning frame
  (stabilizer trivial) and up-to-sign alignment (involutive, ≤ 2^d elements). "Continuous" is made a
  theorem rather than a slogan: the ungrounded gauge group is provably infinite for DIM ≥ 2 via an
  explicit Householder family. The signed-*permutation* case (repeated singular values) is subsumed
  by the finite bound only for the diagonal subgroup; the full permutation stabilizer is not treated.

**Open / not claimed:** the polyhedral face-lattice order (C1); witnesses from bare essentialness +
non-parallelism, and the margin-deficit magnitude (C2); any statement about argmax-decoder rank
floors beyond the 1-dim 3-behavior bound (C5 — false in general, see above); permutation stabilizers
(C6); and every bridge from these stated domains to measurements on real models (pythia/qwen
ceilings, `tiny_math` rank ≈ 4, `wake_sleep` band, `compositional` 0.90 vs 0.69) — those stay
`empirical` anchors, exactly per the work package's discipline.
