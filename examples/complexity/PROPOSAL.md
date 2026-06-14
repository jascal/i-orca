# The decision-complexity of irreducibility (WIP)

> Branch `complexity/irreducibility-hardness`. Exploratory — does **not** affect
> the fully-proven `main` corpus. Goal: settle how hard it is to decide whether a
> composed token is irreducible, and formalise the parts that are
> i-orca/Isabelle-shaped.

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
- [ ] `single_competitor_reducible` (Route B base case; ⟹ ≥2 competitors needed).
- [ ] Route A: define `c_red`, prove the partition ⟷ reducibility gadget.
- [ ] Route B: poly procedure for bounded `K` (or locate the hardness threshold).
- [ ] Write up: hardness/poly dichotomy in `K` + the interpretability reading.

## Build

```bash
ISABELLE_HOME=/path/to/Isabelle isabelle build \
  -d examples/fieldrun/separation -D examples/complexity -o quick_and_dirty Hardness
```
