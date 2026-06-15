# Complexity of irreducibility (WIP)

Exploratory investigation on branch `complexity/irreducibility-hardness` — **how
hard is it to decide whether a composed token is irreducible?** Builds on the
kernel-checked characterisation in `../fieldrun/separation/` (`main`); does not
touch the fully-proven fieldrun corpus.

- [`PROPOSAL.md`](PROPOSAL.md) — design: the margin/cone formulation, the
  formal-vs-meta split, Route A (NP-hardness via PARTITION + anchor gadget),
  Route B (poly for bounded #competitors — likely the real answer), milestones.
- [`Hardness.thy`](Hardness.thy) — Isabelle, kernel-checked: `decides_via_margin`
  (the margin reformulation) and `single_competitor_reducible` /
  `irreducible_needs_two_competitors` (Route B base case: **irreducibility needs
  ≥ 2 competitors**). Route A/B gadgets are documented targets.
- [`Hardness_RouteB.thy`](Hardness_RouteB.thy) — Route B, K = 2, kernel-checked:
  `pp_nonempty_reducible` / `mm_nonempty_reducible` settle the both-positive and
  both-negative sign classes (a one-pass test); the residual pm/mp-only case is
  the genuine pseudo-poly core (where the irreducible witnesses live).
- [`Density.thy`](Density.thy) — the activation→density bridge (the layer the
  static margin model lacks): `fires` / `active_on` / `avg_density`, with
  `active_count_mono` / `total_firing_mono` proving the firing COUNT is monotone
  under shrinking a coalition. (The ratio `density_on` is *not* monotone — flagged.)
- [`Density_Minimization.thy`](Density_Minimization.thy) — top-down decomposition:
  `decomposes` repeatedly replaces a reducible deciding coalition by a strictly
  smaller deciding sub-coalition, bottoming out at irreducible atoms
  (`decomposes_atom`); the result still decides (`decomposes_decides`) and its
  firing count is non-increasing (`decomposes_firing_non_increasing`). You never
  split an irreducible coalition.
- [`Hub.thy`](Hub.thy) — the shared-core / "which neurons can't be disentangled"
  layer, corrected: `per_token_active_bound` is the honest per-token density bound
  (subadditivity, routing each token to its own minimal decider — no hub condition
  needed); `disjoint_private` + `disjoint_private_card_Union` are where the hub
  disjointness actually pays (total distinct private neurons = sum, i.e. the bit
  budget / clean partition), which is NOT the per-token density. **GAP #3, the
  realistic hub:** `is_d_bounded_disentangling_hub` relaxes perfect disjointness to
  BOUNDED overlap (each neuron in the private part of ≤ d tokens);
  `d_bounded_private_budget` proves the naive sum of private sizes overcounts the
  distinct union by at most a factor d (so the distinct neuron budget is ≥ sum/d);
  `disjoint_private_is_1_bounded` / `d1_bounded_budget_is_partition` show the d = 1
  case recovers the clean partition.
- [`MinimalDecider.thy`](MinimalDecider.thy) — **the algorithm as a theorem**, two
  objects and the honest gap between them. (A) `minimal_decider`: an EXECUTABLE
  greedy (`function` + termination on `card S`) that drops one removable source at a
  time; proved to return a deciding SUBSET that is locally minimal
  (`minimal_decider_decides` / `minimal_decider_subset` /
  `minimal_decider_all_necessary`) and never fires more neurons
  (`minimal_decider_firing_bound`). (B) `irreducible_core_exists` /
  `decomposes_exists`: every deciding finite coalition contains a GENUINELY
  irreducible atom. The single-token end-to-end theorem
  `every_deciding_token_has_firing_minimal_irreducible_atom` and the multi-token
  **pipeline theorem** `pipeline_composition` (with `pipeline_density_max_bound`
  giving the literal `≤ |H| + max_e|M_e − H|` shared-core bound) tie
  MinimalDecider + Hub + Density together. `all_necessary_not_irreducible` makes the
  kernel-filtered correction explicit: the greedy's local minimality is NOT global
  irreducibility (the `c4` witness on `main` is `all_necessary` yet reducible), so
  `minimal_decider` is a sound poly UNDER-approximation and the global core is the
  hard part.
- [`MarginBridge.thy`](MarginBridge.thy) — **GAP #4, the per-input model bridge** to
  fieldrun measurements. The static theory uses an input-independent `c j v`; real
  measurements are per-input `c_x x j v` with the physical gate `gated`
  (`¬fires ⟹ c_x = 0`, i.e. `not_fires_margin_zero`). `decides_iff_active` proves the
  decision on any input is carried entirely by the FIRING sources (`active_on`, the
  quantity fieldrun measures); `effective_irreducible_atom_on_input` lifts
  `irreducible_core_exists` onto firing — the decision-relevant irreducible atom sits
  inside `active_on a θ x S`, so the measured active count upper-bounds it; and
  `bridge_pipeline` is the measured counterpart of `pipeline_composition` over an input
  sample (one irreducible atom per input, inside its measured active set).
- [`hardness.i.orca.md`](hardness.i.orca.md) — a concrete i-orca witness of the
  single-competitor base case (verifies + kernel-checks).

Build the Isabelle development:

```bash
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/complexity -o quick_and_dirty Hardness
```

This branch is expected to carry WIP / open targets; the clean zero-`sorry`
corpus lives on `main`.
