# ConceptGrounding — geometry of grounded concepts, kernel-checked

The six PIC/PIL grounding conjectures (workspace `PIC_PIL_GROUNDING_CONJECTURES.md`) proved as
Isabelle theories with a thin i-orca surface, in the work package's priority order. Concepts are
half-spaces `H_c = {r. b_c ≤ ⟨u_c, r⟩}` in residual space; every theorem is about what that
geometry provably satisfies — the *bridge to real models stays open* (see
[`PROPOSAL.md`](PROPOSAL.md) for the full tag ledger, [`RESULTS.md`](RESULTS.md) for verification
status and the premise-strengthening report).

## The six theories

| theory | conjecture | headline |
|--------|-----------|----------|
| `Consolidation.thy` | **C4** stability–plasticity | frozen memberships/decisions exactly invariant under masked training; reachable change ≤ card P dims; retain + learn ≤ K |
| `ConceptCells.thy` | **C1** lattice ≡ arrangement ≡ cells | σ-fibers are the (convex) arrangement cells; FCA Galois + anti-isomorphism, intent of a cell = its sign vector; concept arrangement refines the argmax decoder |
| `ComputedRank.thy` | **C5** computed-core rank floor | exact-readout: #outputs ≤ dim S (= ρ ≥ rank M_g); retrieval is rank-1; homogeneous argmax at rank 1 has ≤ 3 behaviors; addition floor 2n−1 grows with width |
| `Compositional.thy` | **C3** capacity gap | factored code: A+1 covering examples ⇒ exact generalization to all 2^A combos; partition code: unseen cell undetermined, needs all 2^A; conjunction = 1 rule vs 2^(A−card S₀) cells |
| `Crystallization.thy` | **C2** collapse exactness | collapse exact iff region is one half-space (joint-redundancy direction proved); straddling midpoint witnesses block ANY half-space; quadrant instance fully worked |
| `Gauge.thy` | **C6** gauge reduction | all of O(d) preserves decisions (and is provably infinite for d ≥ 2, explicit Householder family); exact frame alignment ⇒ gauge trivial; sign alignment ⇒ finite involutive gauge |
| `CrossToken.thy` | **C7** equality separation *(from the Wyly review, pil PR #10)* | cross-token equality is linear-impossible (no additive reader at any dimension) yet bilinear-easy (orthonormal features, threshold ½); conjunctive per-position rules need ≥ card V where one eq_atom suffices — the kernel-checked case for the unified substrate |
| `GradedConsolidation.thy` | **C8** graded stability *(from the Wyly review, pil PR #10)* | anchored drift ≤ G/(2λω) at stationarity, explicit freeze schedule; drift-vs-margin membership/decode certificates (PIC_Prune triangle shape); composed graded stability recovering C4 as ω→∞; sign-normalized updates provably ignore gradient scaling (the Adam finding) |

`concept_grounding.i.orca.md` is the i-orca surface: every theorem stated in the DSL and
discharged by `(rule <lemma>)` against the substrate. Its compiled form
`ConceptGrounding_Surface.thy` is part of the session, so the surface itself is kernel-checked.

## Verify / kernel-check

```bash
# structural (no Isabelle)
.venv/bin/i-orca verify examples/concept_grounding/concept_grounding.i.orca.md

# kernel (Isabelle2025-2, parent HOL-Analysis): substrate + compiled surface
isabelle build -d examples/concept_grounding -o quick_and_dirty ConceptGrounding
```

## Ties to the packing corpus

- `tropical/DecodeCapacity.thy` — C1 generalizes its cell/γ-code reasoning to the concept arrangement.
- `tropical/RoutingRank.thy` — C4(iii)/C5 are the consolidation- and computed-function-side rank
  bounds to its routing-side "M generators move logits in ≤ M dims".
- `superposition/RoutingWelch.thy` — the interference story the capacity/budget theorems slot into.
