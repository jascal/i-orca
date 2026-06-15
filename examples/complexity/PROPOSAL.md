# The decision-complexity of irreducibility

> Merged to `main` (was branch `complexity/irreducibility-hardness`). Goal: settle
> how hard it is to decide whether a composed token is irreducible, and formalise
> the parts that are i-orca/Isabelle-shaped. The **decomposition / decider / hub /
> end-to-end** layers are now kernel-checked (see "What is proven" below); the
> genuinely open items are the Route A NP-hardness gadget, the `K`-dichotomy, and
> the per-input model bridge to fieldrun measurements.

## Background

From `examples/fieldrun/separation/` (on `main`, kernel-checked): a token `t`
decided by the full source set `S` is **irreducible** iff `S` is the *unique*
deciding coalition (`irreducible_iff_unique_decider`). Writing the per-competitor
**margin** `m_j^v = c_j(t) − c_j(v)`, deciding is positivity of margin sums:

> `decides c P V t  ⟺  (∀v∈V, v≠t)  Σ_{j∈P} m_j^v > 0`.

So **reducibility** is: does the open cone `⋂_{v≠t} {x : Σ_j m_j^v x_j > 0}`
contain a hypercube vertex `1_P` other than `0` and `1_S`? Equivalently, is there a
non-empty proper `P ⊊ S` whose indicator satisfies all the strict margin
inequalities?

`main` already pins down: necessary conditions (μ_t = 0, every-source-necessary),
the **exact** characterisation at n ≤ 3, and a **sharp** n = 4 counterexample.
What remains is the middle lattice layers — and the conjecture that there is no
simple closed form because the decision problem is hard.

## What is proven (kernel-checked on `main`)

Beyond the margin reformulation and the Route B base case, the following layers are
now fully discharged (zero `sorry`; `isabelle build` of session `Hardness`):

- **Density bridge** (`Density.thy`): the activation→firing model `fires`/`active_on`,
  with the firing **count** monotone under shrinking a coalition
  (`active_count_mono`, `total_firing_mono`) — the right objective, since the
  **ratio** `density_on` is *not* monotone.
- **Top-down decomposition** (`Density_Minimization.thy`): the `decomposes` relation
  replaces a reducible deciding coalition by a strictly smaller deciding one, bottoming
  out at irreducible atoms (`decomposes_atom`), still deciding (`decomposes_decides`),
  firing-count non-increasing (`decomposes_firing_non_increasing`).
- **Executable minimal decider** (`MinimalDecider.thy`): `minimal_decider` (a real
  `function` + termination on `card S`) returns a deciding subset that is locally
  minimal (`minimal_decider_all_necessary`) and fires no more neurons
  (`minimal_decider_firing_bound`); `irreducible_core_exists`/`decomposes_exists` give
  genuine irreducible atoms. **Honest gap:** local minimality is a sound poly
  *under-approximation*, **not** global irreducibility — `all_necessary_not_irreducible`
  (the `c4` witness is `all_necessary` yet reducible).
- **End-to-end pipeline** (`MinimalDecider.thy`): single-token
  `every_deciding_token_has_firing_minimal_irreducible_atom`, and multi-token
  `pipeline_composition` / `pipeline_density_max_bound` — every token in a sample gets
  an irreducible atom that still decides and whose per-token active count is
  `≤ |H| + max_e |M_e − H|`.
- **Realistic hub** (`Hub.thy`): `is_d_bounded_disentangling_hub` (bounded overlap)
  with `d_bounded_private_budget` (sum overcounts the distinct union by ≤ factor `d`);
  `d = 1` recovers the clean partition (`d1_bounded_budget_is_partition`).
- **Per-input model bridge** (`MarginBridge.thy`): gated per-input contributions
  (`gated`: `¬fires ⟹ c_x = 0`); `decides_iff_active` (the decision is carried by the
  FIRING sources, the measured `active_on`); `effective_irreducible_atom_on_input` /
  `bridge_pipeline` lift `irreducible_core_exists` / `pipeline_composition` onto
  measured firing — the decision-relevant irreducible atom sits inside the measured
  active set, whose count upper-bounds it.

## The two layers (only one is formalisable)

1. **Reduction / gadget correctness** — "construction `G(x)` yields a reducible
   token iff `x` is a YES-instance." A concrete `decides`/`has_suff_sub` statement
   about an explicit parametric `c`. **This is an Isabelle theorem** (same shape
   as `triple_irreducible`). It is the load-bearing, error-prone part.
2. **Complexity wrapper** — "`G` is poly-time, hence REDUCIBLE is NP-complete /
   IRREDUCIBLE is coNP-complete." Needs a model of computation; **left as the
   paper-level argument**, citing the known-hard source problem. Not formalised.

## Route A — NP-hardness (conjectured)

Reduce from **PARTITION** (NP-complete): positive integers `w_1..w_n` with total
`2W`; is there `A ⊆ {1..n}` with `Σ_{j∈A} w_j = W`?

Sketch: build margins so that a proper coalition decides `t` iff it corresponds to
a partition half. The constraint `Σ_{j∈P} m_j^v > 0` is **homogeneous** (no
constant term), so two gadget tricks are needed:

- an **anchor** source/competitor to fake the missing constant (encode
  `Σ w_j x_j ≥ W` and `Σ w_j x_j ≤ W`, i.e. `= W`, via two competitors with
  opposite-signed margins and an anchor offset);
- force the trivial vertices out: `∅` never decides; arrange that `1_S` decides
  (the planted irreducible/reducible token) while the only *other* deciders are
  the partition halves.

**Formal target:** `definition c_red` (parametric in `ws, W`) and
`irreducible c_red S V t ⟷ ¬ (∃A. A ⊆ S ∧ A ≠ {} ∧ A ⊂ S ∧ Σ_{j∈A} ws j = W)`.

## Route B — polynomial for bounded #competitors (conjectured, maybe the real answer)

With `|V| ≤ K` competitors fixed, the deciding cone is an intersection of `K`
open halfspaces; the relevant 0/1 feasibility may be poly-time (the margin-sum
vector lives in `ℝ^K`, and the reachable sums have bounded structure). **This is
probably the more interesting answer for interpretability**: real tokens have few
*near*-competitors, so the regime that matters is small `K`.

- **Base cases (done / starter):** `K = 1` (single competitor) — the full-deciding
  token is *always* reducible, so **irreducible ⟹ ≥ 2 competitors**
  (`single_competitor_reducible`, in `Hardness.thy`). n ≤ 3 already exact on `main`.
- **Target:** a decision procedure + correctness for fixed `K`, or a sharp `K`
  threshold where hardness kicks in.

## Milestones

- [x] Margin reformulation (`decides_via_margin`).
- [x] `single_competitor_reducible` (Route B base case; ⟹ ≥2 competitors needed).
- [x] Density bridge + monotone firing count (`Density.thy`).
- [x] Top-down decomposition to irreducible atoms (`Density_Minimization.thy`).
- [x] Executable `minimal_decider` + correctness; irreducible-core existence
      (`MinimalDecider.thy`).
- [x] End-to-end pipeline theorem (`pipeline_composition` /
      `pipeline_density_max_bound`).
- [x] Realistic bounded-overlap hub (`is_d_bounded_disentangling_hub`,
      `d_bounded_private_budget`).
- [x] Model bridge: per-input `c_x` with `¬fires ⟹ margin = 0`; decision carried by
      the firing sources; static results lifted onto measured firing
      (`MarginBridge.thy`).
- [ ] **Route A:** define `c_red`, prove the partition ⟷ reducibility gadget (the
      load-bearing NP-hardness construction; still a target).
- [ ] **Route B:** poly procedure for bounded `K` (or locate the hardness threshold);
      the `K`-dichotomy write-up.

## Build

```bash
ISABELLE_HOME=/path/to/Isabelle isabelle build \
  -d examples/fieldrun/separation -D examples/complexity -o quick_and_dirty Hardness
```
