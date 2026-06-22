# Tropical geometry of deep neural networks — i-orca corpus

A kernel-checked formalisation of the mathematical core of the **tropical-geometry view
of ReLU networks** — the second entry in i-orca's **"canonical proofs from other
authors"** track (after [`../watermark`](../watermark)). Primary source: **Zhang,
Naitzat & Lim, *"Tropical Geometry of Deep Neural Networks"*, ICML 2018** (Thm 5.4,
Def 2.4, Cor 3.4), with **Pachter–Sturmfels** (PNAS 2004) and **Maragos et al.**
(Proc. IEEE 2021) as the surrounding literature.

> ⚠️ As everywhere in i-orca, a green `i-orca verify` certifies only that the proof
> *skeleton* is well-formed. Truth is the kernel's: every theorem here is discharged by
> `(rule <lemma>)` against a hand-authored Isabelle lemma, and the whole `Tropical`
> session builds under Isabelle2025-2 with **zero `sorry`**.

## The idea in one line

`ReLU(t) = max(t,0) = t ⊕ 0` and an affine layer is a tropical monomial, so a ReLU
network is built from the **max-plus semiring** `(max, +)`; its outputs are **tropical
rational functions** (differences of convex piecewise-linear tropical polynomials), and
its **linear regions** are governed by the Newton polytopes of those polynomials. See
[`PROPOSAL.md`](PROPOSAL.md).

## Layout

| File | Role |
|------|------|
| [`TropicalSemiring.thy`](TropicalSemiring.thy) | the max-plus semiring: associativity, commutativity, idempotence, identities, and `⊙`-over-`⊕` distributivity |
| [`TropicalPoly.thy`](TropicalPoly.thy) | tropical polynomials are convex; `convex_on_max` (not in the library); tropical rational = difference of two |
| [`ReLUNet.thy`](ReLUNet.thy) | **Theorem 5.4 core**: ReLU/affine are tropical rational, the class is closed under the network ops, a one-hidden-layer net is tropical rational, and tropical rationals are continuous |
| [`MaxPlus.thy`](MaxPlus.thy) | max-plus matrix–vector product and **residuation** (Maragos): feasibility + greatest subsolution |
| [`Newton.thy`](Newton.thy) | **polytope propagation** (Pachter–Sturmfels): tropical product = pointwise sum, submultiplicative monomial count, Minkowski-sum slope support |
| [`Examples.thy`](Examples.thy) | a concrete worked example: the two-neuron ReLU net `relu x + relu(−x)` computes `¦x¦`, rendered as the tropical polynomial `max x (−x)` |
| [`HeadTail.thy`](HeadTail.thy) | a **fieldrun** contribution: the LLM decode `argmax_v ⟨x,U_v⟩` as a max-plus polynomial, split into a compact HEAD + open-class TAIL; the head certifiably reproduces the decode when it out-values the tail, the tail is the explicit residue |
| [`DecodeCapacity.thy`](DecodeCapacity.thy) | a **fieldrun** contribution: confident decoding forces separated frames — γ-margin-decodable tokens are γ-separated in `ℝ^d` (bias-free), so the certifiable head is a γ-code bounded by the packing number `(1+2ρ/γ)^d`. The decision-side sibling of the Welch bound — the **cell-capacity (frame-side) half** of the two-sided packing story (foundational; routing complexity is the currently-binding side, see `RoutingRank.thy`) |
| [`RoutingRank.thy`](RoutingRank.thy) | a **fieldrun** contribution: the generator-side dual — `M` trainable rules move logits only within an `≤M`-dim subspace (`span` of the `M` fixed readout vectors), so superposition is forced when the number of routing features exceeds `M` |
| [`ROOT`](ROOT) | Isabelle session `Tropical` (parent `HOL-Analysis`) |
| [`tropical.i.orca.md`](tropical.i.orca.md) | the i-orca surface: 30 theorems, each `(rule <lemma>)` |
| [`PROPOSAL.md`](PROPOSAL.md) | the sources, the formal-vs-meta table, honest reckonings, open targets |
| [`RESULTS.md`](RESULTS.md) | verification status and commands |

The `.thy` files are the **hand-authored, kernel-checked substrate**; the `.i.orca.md`
is the thin i-orca surface over it (the `watermark` / `provenance` pattern).

## Verify

```bash
# Layer 1 — structural skeleton (zero Isabelle)
i-orca verify examples/tropical/tropical.i.orca.md
#   -> all 30 theorems VALID, formal_fraction_static = 1.000

# Layer 2 — kernel check of the substrate (the load-bearing math)
ISABELLE_HOME=/path/to/Isabelle isabelle build -D examples/tropical \
  -o quick_and_dirty Tropical
#   -> Finished Tropical, exit 0, zero sorry
```

To also kernel-check the **surface**, compile it into the session and rebuild:

```bash
i-orca compile examples/tropical/tropical.i.orca.md --target isar \
  --document --theory TropicalSurface --out examples/tropical/TropicalSurface.thy
# append "TropicalSurface" to ROOT, rebuild -> exit 0 (every (rule ...) non-vacuous)
# TropicalSurface.thy is a regenerable artifact; not committed.
```

The standalone `i-orca check` builds each theorem under a plain HOL parent and cannot
load this project-local session — an import-resolution limit, not a math failure (same
caveat as the `watermark` / `provenance` / `complexity` corpora).

## What it proves (and what it doesn't)

Twenty kernel-checked cores spanning the max-plus semiring, the convexity of tropical
polynomials, the ReLU-network–tropical-rational correspondence (Thm 5.4, scalar/closure
form), max-plus residuation, polytope propagation, and a concrete worked example (a
two-neuron ReLU net as a tropical polynomial) — see the table in
[`PROPOSAL.md`](PROPOSAL.md). The theorems are honest about scope: the full multivariate
multilayer Theorem 5.4, the multivariate Newton-polytope linear-region bound (Thm 6.3),
and the decision-boundary = tropical-hypersurface result (Prop 6.1) are flagged as open
targets. None of those caveats touch the parts that are proven.
