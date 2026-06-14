# Theorem 3, refined: realisability, the μ_t=0 gap, and irreducibility

A paper-ready writeup of what formalising the "general half" of Theorem 3 settled
and what it left open. All claims below are kernel-checked
(Isabelle2025-2): the *realisability* half in
[`../fieldrun.i.orca.md`](../fieldrun.i.orca.md) (`WeightedThresholdExpressivity`),
the *gap* in the same file (`MuZeroDoesNotImplyIrreducible`), and the *existence /
irreducibility* results in [`Separation.thy`](Separation.thy).

## The model (explicit definitions)

Fix a finite source set `S`, a finite outcome set `V`, and contributions
`c j v ∈ ℝ`. Write the sub-conjunction *vote* of a subset `P ⊆ S` as
`vote_P(v) = Σ_{j∈P} c j v`.

- **decides** `P` decides `t` iff `t` is the strict argmax of `vote_P` over `V`:
  `∀v∈V. v ≠ t ⟶ vote_P(v) < vote_P(t)`.
- **μ_t = 0** (`mu0`): no *singleton* decides `t`, i.e. `∀j∈S. ¬ decides {j} t`.
  (This is the paper's measured readout multiplicity being zero.)
- **Horn / sub-conjunction-expressible** (`has_suff_sub`): some *proper non-empty
  subset* already decides `t`, i.e. `∃P. P ≠ ∅ ∧ P ⊊ S ∧ decides P t`.
- **irreducible**: `decides S t ∧ ¬ has_suff_sub S t` — the full set decides `t`
  but no proper sub-conjunction does.

The key distinction the formalisation forced into the open: **μ_t = 0 ranges over
singletons; irreducibility ranges over all proper subsets.** They are not the same
condition.

## What is proven

**(3a) Realisability** — `WeightedThresholdExpressivity`.
A composed token (μ_t = 0) can be the argmax of the full weighted sum while no
singleton selects it. Witness (`n = 2`, three outcomes A,B,C):
`c₁ = (2,3,0)`, `c₂ = (2,0,3)`; the sum gives `(4,3,3)` → A, but source 1 → B and
source 2 → C. So weighted-threshold realises tokens beyond any singleton.

**(3b-i) The gap** — `MuZeroDoesNotImplyIrreducible`.
**μ_t = 0 does *not* imply irreducible.** Witness (`n = 3`):
`c₁ = (2,3,0)`, `c₂ = (2,0,3)`, `c₃ = (0,½,½)`. The full triple decides A and no
singleton decides A (μ_A = 0), **yet the proper subset {1,2} already decides A.**
So a μ_t = 0 token can still be expressible by a sub-conjunction. The literal
reading "COMPOSED ⟺ not-sub-conjunction-expressible" is therefore false; μ_t = 0 is
strictly weaker than irreducibility.

**(3b-ii) Existence of irreducible tokens** — `Separation.thy`.
- `irreducible_pair`: at `n = 2` the proper non-empty subsets are exactly the
  singletons, so `μ_t = 0 ⟺ irreducible`; the realisability witness above is
  *already irreducible*.
- `triple_irreducible`: an `n = 3`, four-outcome construction where each source
  defends a distinct competitor — `c j = (A:3, threat_j:8, else 0)`. Every
  singleton picks its threat (8 > 3); every *pair* still loses A (3+3 = 6 < 8);
  only the **full triple** clears all threats (3+3+3 = 9 > 8). No proper subset
  decides A — `irreducible`, with **every source necessary**.

## Connection to §4.4 (route-ordered fragility)

`triple_irreducible` is the formal counterpart of the paper's fragility result:
irreducibility = "no proper sub-conjunction suffices" = *every contributing source
is causally necessary*; ablating any one flips the decision. The measured per-head
un-rescue / flip behaviour is the empirical shadow of tokens sitting in (or near)
the irreducible regime.

## Characterising irreducibility — what we can pin down

(All in [`Characterization.thy`](Characterization.thy), kernel-checked.)

- **Reformulation (exact).** `irreducible_iff_unique_decider`: t is irreducible
  iff the full set S is the **unique deciding set** — the only `P ⊆ S` with
  `decides c P V t` is `P = S`. Equivalently, writing the per-competitor *margin*
  `m_j^v = c j t − c j v`, the all-ones vector is the unique nonzero 0/1 solution
  of the system `(∀v≠t) Σ_{j} m_j^v x_j > 0`.
- **Necessary conditions (any |S| ≥ 2).** Irreducible ⟹ `mu0` (no singleton
  decides) **and** `all_necessary` (every `S − {j}` fails) — `necessary_mu0`,
  `necessary_all_sources`. So both the bottom layer (singletons) and the top
  layer (co-singletons) of the subset lattice must fail.
- **Exact at n ≤ 3.** `n3_characterization`: for `card S = 3`,
  `irreducible ⟺ mu0 ∧ all_necessary`. (At n = 3 the proper non-empty subsets are
  exactly the singletons and the co-singletons, so the two necessary conditions
  already cover the whole lattice.)
- **Sharp — it breaks at n = 4.** `n3_characterization_is_sharp`: an explicit
  4-source token with `mu0` **and** `all_necessary` **and** decided by the full
  set, yet **reducible** — the proper *pair* `{1,2}` already decides it. The
  middle lattice layers (sizes 2…n−2) are exactly what the bottom/top necessary
  conditions miss, and they are where irreducibility actually lives for n ≥ 4.

## What remains open

The middle layers are genuinely hard, not just unwritten. Deciding *reducibility*
is the existence of a non-empty proper `P` with `Σ_{j∈P} m_j^v > 0` for every
competitor v — a **0/1 feasibility of strict linear inequalities** (does the open
cone `⋂_v {m^v · x > 0}` contain a hypercube vertex other than 0 and the all-ones
point?). That decision problem is NP-hard in general, so one should **not** expect
a simple closed-form characterisation of irreducibility for arbitrary n; the exact
statement is the lattice one (unique deciding set), with the dimension ≤ 3 case
fully pinned down and existence settled at every n. (The NP-hardness is a
complexity meta-claim, not formalised here.)

The remaining *mathematical* frontier is then narrow and precise: a structural
description of the middle-layer deciding sets (e.g. for bounded #competitors |V|,
or bounded subset size), and the corresponding weighted-threshold vs Horn / ∩–∪
formula-class separation. Existence is settled; low dimension is exact; the
general case is provably lattice-combinatorial rather than a missing formula.

## Suggested paper text

> A composed token (μ_t = 0) can be realised by the weighted-threshold connective
> though no singleton sub-conjunction selects it (Theorem 3a). But μ_t = 0 — *no
> singleton suffices* — is strictly weaker than *irreducibility* — *no proper
> sub-conjunction suffices*. Call t irreducible when the full source set is the
> unique deciding coalition. Irreducibility implies both μ_t = 0 and that every
> source is necessary (each single-source ablation flips the decision — the
> formal counterpart of the route-ordered fragility of §4.4); for n ≤ 3 these two
> conditions are also sufficient, but at n ≥ 4 they are not — a two-source
> coalition can select a token that neither it, any singleton, nor any
> (n−1)-subset selects. Genuinely irreducible composed tokens exist at every n,
> including cases where every source is necessary. A complete characterisation of
> *which* composed tokens are irreducible is, in general, a 0/1 linear-feasibility
> question (NP-hard), so the clean content is the unique-deciding-coalition
> criterion plus the exact low-dimension result; the corresponding formula-class
> separation remains the open frontier. (All non-complexity claims here are
> machine-checked in Isabelle/HOL; see the i-orca formalisation.)

## Naming note

If lifting into the paper, "irreducible composition" reads more cleanly than the
μ_t-centric framing: *μ_t = 0 is necessary but not sufficient for irreducible
composition.*
