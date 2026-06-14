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

## What remains open

The **full expressivity characterisation** — *exactly which* composed tokens are
irreducible, and the separation between the weighted-threshold connective and the
Horn / ∩–∪ fragment over *all* formula classes (not just the vote-subset reading
above). The existence of irreducible tokens is settled; their characterisation is
the genuine open frontier — now well-posed rather than vacuous.

## Suggested paper text

> A composed token (μ_t = 0) can be realised by the weighted-threshold connective
> though no singleton sub-conjunction selects it (Theorem 3a). But μ_t = 0 — *no
> singleton suffices* — is strictly weaker than irreducibility — *no proper
> sub-conjunction suffices*: there are μ_t = 0 tokens already decided by a proper
> subset of sources (a two-source coalition can select a token that neither source
> selects alone). The two conditions coincide at n = 2 and diverge for n ≥ 3.
> Genuinely irreducible composed tokens — decided by the full source set but by no
> proper sub-conjunction — do exist, including cases where every source is
> necessary (the formal counterpart of the route-ordered fragility of §4.4). A
> complete characterisation of when irreducibility occurs, and the corresponding
> formula-class separation, remains open. (All claims here are machine-checked in
> Isabelle/HOL; see the i-orca formalisation.)

## Naming note

If lifting into the paper, "irreducible composition" reads more cleanly than the
μ_t-centric framing: *μ_t = 0 is necessary but not sufficient for irreducible
composition.*
